use rustc_ast::{self as ast, Block, BlockCheckMode, Local, LocalKind, Stmt, StmtKind};
use rustc_hir as hir;
use rustc_hir::Target;
use rustc_span::{Ident, Symbol, sym};
use smallvec::SmallVec;
use std::collections::HashMap;

use crate::{ImplTraitContext, ImplTraitPosition, LoweringContext};

impl<'a, 'hir> LoweringContext<'a, 'hir> {
    pub(super) fn lower_block(
        &mut self,
        b: &Block,
        targeted_by_break: bool,
    ) -> &'hir hir::Block<'hir> {
        let hir_id = self.lower_node_id(b.id);
        self.arena.alloc(self.lower_block_noalloc(hir_id, b, targeted_by_break))
    }

    pub(super) fn lower_block_noalloc(
        &mut self,
        hir_id: hir::HirId,
        b: &Block,
        targeted_by_break: bool,
    ) -> hir::Block<'hir> {
        let (stmts, expr) = self.lower_stmts(&b.stmts);
        let rules = self.lower_block_check_mode(&b.rules);
        hir::Block { hir_id, stmts, expr, rules, span: self.lower_span(b.span), targeted_by_break }
    }

    pub(super) fn lower_stmts(
        &mut self,
        mut ast_stmts: &[Stmt],
    ) -> (&'hir [hir::Stmt<'hir>], Option<&'hir hir::Expr<'hir>>) {
        let mut stmts = SmallVec::<[hir::Stmt<'hir>; 8]>::new();
        let mut expr = None;
        
        // Collect DAG tasks and edges for parallel execution
        let mut dag_tasks: HashMap<Symbol, &ast::DagTask> = HashMap::new();
        let mut dag_edges: Vec<(Symbol, Symbol)> = Vec::new();
        let mut has_dag_content = false;
        
        // First pass: collect all DAG tasks and edges
        for s in ast_stmts {
            match &s.kind {
                StmtKind::DagTask(dag_task) => {
                    dag_tasks.insert(dag_task.ident.name, dag_task);
                    has_dag_content = true;
                }
                StmtKind::DagEdge(dag_edge) => {
                    // Only collect edges with simple identifiers (internal task references)
                    if let ast::ExprKind::Path(None, ref from_path) = dag_edge.from_expr.kind {
                        if let ast::ExprKind::Path(None, ref to_path) = dag_edge.to_expr.kind {
                            if from_path.segments.len() == 1 && to_path.segments.len() == 1 {
                                let from_name = from_path.segments[0].ident.name;
                                let to_name = to_path.segments[0].ident.name;
                                dag_edges.push((from_name, to_name));
                                has_dag_content = true;
                            }
                        }
                    }
                }
                _ => {}
            }
        }
        
        // If we have DAG content, generate parallel execution code
        if has_dag_content && !dag_tasks.is_empty() {
            let parallel_stmts = self.lower_dag_parallel(&dag_tasks, &dag_edges, ast_stmts);
            stmts.extend(parallel_stmts);
            
            // Process remaining non-DAG statements
            while let [s, tail @ ..] = ast_stmts {
                match &s.kind {
                    StmtKind::DagTask(_) | StmtKind::DagEdge(_) => {
                        // Already processed
                    }
                    _ => {
                        let lowered = self.lower_single_stmt(s, tail.is_empty());
                        if let Some((stmt, is_expr)) = lowered {
                            if is_expr && tail.is_empty() {
                                if let hir::StmtKind::Expr(e) = stmt.kind {
                                    expr = Some(e);
                                } else {
                                    stmts.push(stmt);
                                }
                            } else {
                                stmts.push(stmt);
                            }
                        }
                    }
                }
                ast_stmts = tail;
            }
        } else {
            // No DAG content, use original logic
            while let [s, tail @ ..] = ast_stmts {
                self.lower_stmt_into(&mut stmts, &mut expr, s, tail.is_empty());
                ast_stmts = tail;
            }
        }
        
        (self.arena.alloc_from_iter(stmts), expr)
    }
    
    fn lower_single_stmt(
        &mut self,
        s: &Stmt,
        is_last: bool,
    ) -> Option<(hir::Stmt<'hir>, bool)> {
        match &s.kind {
            StmtKind::Let(local) => {
                let hir_id = self.lower_node_id(s.id);
                let local = self.lower_local(local);
                self.alias_attrs(hir_id, local.hir_id);
                let kind = hir::StmtKind::Let(local);
                let span = self.lower_span(s.span);
                Some((hir::Stmt { hir_id, kind, span }, false))
            }
            StmtKind::Expr(e) => {
                let e = self.lower_expr(e);
                let hir_id = self.lower_node_id(s.id);
                self.alias_attrs(hir_id, e.hir_id);
                let kind = hir::StmtKind::Expr(e);
                let span = self.lower_span(s.span);
                Some((hir::Stmt { hir_id, kind, span }, is_last))
            }
            StmtKind::Semi(e) => {
                let e = self.lower_expr(e);
                let hir_id = self.lower_node_id(s.id);
                self.alias_attrs(hir_id, e.hir_id);
                let kind = hir::StmtKind::Semi(e);
                let span = self.lower_span(s.span);
                Some((hir::Stmt { hir_id, kind, span }, false))
            }
            StmtKind::Empty => None,
            _ => None,
        }
    }
    
    fn lower_dag_parallel(
        &mut self,
        dag_tasks: &HashMap<Symbol, &ast::DagTask>,
        dag_edges: &[(Symbol, Symbol)],
        _ast_stmts: &[Stmt],
    ) -> Vec<hir::Stmt<'hir>> {
        let mut result_stmts = Vec::new();
        
        // Build dependency graph
        let mut in_degree: HashMap<Symbol, usize> = HashMap::new();
        let mut dependents: HashMap<Symbol, Vec<Symbol>> = HashMap::new();
        
        for name in dag_tasks.keys() {
            in_degree.insert(*name, 0);
            dependents.insert(*name, Vec::new());
        }
        
        for (from, to) in dag_edges {
            if dag_tasks.contains_key(from) && dag_tasks.contains_key(to) {
                *in_degree.get_mut(to).unwrap() += 1;
                dependents.get_mut(from).unwrap().push(*to);
            }
        }
        
        // Topological sort into levels (tasks in same level can run in parallel)
        let mut levels: Vec<Vec<Symbol>> = Vec::new();
        let mut remaining = in_degree.clone();
        
        while !remaining.is_empty() {
            let level: Vec<Symbol> = remaining
                .iter()
                .filter(|&(_, deg)| *deg == 0)
                .map(|(&name, _)| name)
                .collect();
            
            if level.is_empty() {
                break;
            }
            
            for name in &level {
                remaining.remove(name);
                if let Some(deps) = dependents.get(name) {
                    for dep in deps {
                        if let Some(deg) = remaining.get_mut(dep) {
                            *deg -= 1;
                        }
                    }
                }
            }
            
            levels.push(level);
        }
        
        // Generate code for each level
        for level in levels {
            if level.len() == 1 {
                let task_name = level[0];
                if let Some(dag_task) = dag_tasks.get(&task_name) {
                    let task_block = self.lower_block(&dag_task.body, false);
                    let hir_id = self.next_id();
                    let block_expr = self.arena.alloc(hir::Expr {
                        hir_id: self.next_id(),
                        kind: hir::ExprKind::Block(task_block, None),
                        span: self.lower_span(dag_task.span),
                    });
                    let kind = hir::StmtKind::Semi(block_expr);
                    let span = self.lower_span(dag_task.span);
                    result_stmts.push(hir::Stmt { hir_id, kind, span });
                }
            } else {
                // Multiple tasks at same level - generate thread::scope call
                let span = self.lower_span(dag_tasks.values().next().unwrap().span);
                
                // Collect all task bodies for this level
                let mut task_bodies: Vec<(&'hir hir::Block<'hir>, rustc_span::Span)> = Vec::new();
                for task_name in &level {
                    if let Some(dag_task) = dag_tasks.get(task_name) {
                        let task_block = self.lower_block(&dag_task.body, false);
                        task_bodies.push((task_block, self.lower_span(dag_task.span)));
                    }
                }
                
                // Generate: std::thread::scope(|s| { s.spawn(|| task1); s.spawn(|| task2); });
                let scope_call = self.make_dag_parallel_scope_call(span, task_bodies);
                result_stmts.push(hir::Stmt {
                    hir_id: self.next_id(),
                    kind: hir::StmtKind::Semi(scope_call),
                    span,
                });
            }
        }
        
        result_stmts
    }
    
    fn make_dag_parallel_scope_call(
        &mut self,
        span: rustc_span::Span,
        task_bodies: Vec<(&'hir hir::Block<'hir>, rustc_span::Span)>,
    ) -> &'hir hir::Expr<'hir> {
        // Create spawn statements for each task
        let mut spawn_stmts: Vec<hir::Stmt<'hir>> = Vec::new();
        
        let scope_param_ident = Ident::from_str("__dag_s");
        let (scope_pat, scope_binding_id) = self.pat_ident(span, scope_param_ident);
        
        // Store closure def_ids that we'll need
        let mut inner_closure_def_ids: Vec<_> = Vec::new();
        for _ in &task_bodies {
            let closure_node_id = self.next_node_id();
            inner_closure_def_ids.push(self.local_def_id(closure_node_id));
        }
        
        // Create inner closure bodies first
        let mut inner_closure_bodies: Vec<_> = Vec::new();
        for (task_block, task_span) in &task_bodies {
            let closure_body_expr = hir::Expr {
                hir_id: self.next_id(),
                kind: hir::ExprKind::Block(*task_block, None),
                span: *task_span,
            };
            let body_id = self.lower_body(|_this| {
                (&[], closure_body_expr)
            });
            inner_closure_bodies.push(body_id);
        }
        
        // Now create spawn calls
        for (i, ((task_block, task_span), body_id)) in task_bodies.iter().zip(inner_closure_bodies.iter()).enumerate() {
            let inner_closure = self.arena.alloc(hir::Expr {
                hir_id: self.next_id(),
                kind: hir::ExprKind::Closure(self.arena.alloc(hir::Closure {
                    def_id: inner_closure_def_ids[i],
                    binder: hir::ClosureBinder::Default,
                    constness: hir::Constness::NotConst,
                    capture_clause: hir::CaptureBy::Ref,
                    bound_generic_params: &[],
                    fn_decl: self.arena.alloc(hir::FnDecl {
                        inputs: &[],
                        output: hir::FnRetTy::DefaultReturn(*task_span),
                        c_variadic: false,
                        implicit_self: hir::ImplicitSelfKind::None,
                        lifetime_elision_allowed: true,
                    }),
                    body: *body_id,
                    fn_decl_span: *task_span,
                    fn_arg_span: None,
                    kind: hir::ClosureKind::Closure,
                })),
                span: *task_span,
            });
            
            // Create scope reference: __dag_s
            let scope_ref = self.arena.alloc(hir::Expr {
                hir_id: self.next_id(),
                kind: hir::ExprKind::Path(hir::QPath::Resolved(
                    None,
                    self.arena.alloc(hir::Path {
                        span,
                        res: hir::def::Res::Local(scope_binding_id),
                        segments: self.arena.alloc_from_iter([
                            hir::PathSegment::new(scope_param_ident, self.next_id(), hir::def::Res::Local(scope_binding_id))
                        ]),
                    }),
                )),
                span,
            });
            
            // Create method call: __dag_s.spawn(closure)
            let spawn_ident = Ident::from_str("spawn");
            let spawn_call = self.arena.alloc(hir::Expr {
                hir_id: self.next_id(),
                kind: hir::ExprKind::MethodCall(
                    self.arena.alloc(hir::PathSegment::new(spawn_ident, self.next_id(), hir::def::Res::Err)),
                    scope_ref,
                    std::slice::from_ref(inner_closure),
                    *task_span,
                ),
                span: *task_span,
            });
            
            spawn_stmts.push(hir::Stmt {
                hir_id: self.next_id(),
                kind: hir::StmtKind::Semi(spawn_call),
                span: *task_span,
            });
        }
        
        // Create outer closure body block
        let outer_body_block = self.arena.alloc(hir::Block {
            hir_id: self.next_id(),
            stmts: self.arena.alloc_from_iter(spawn_stmts),
            expr: None,
            rules: hir::BlockCheckMode::DefaultBlock,
            span,
            targeted_by_break: false,
        });
        
        let outer_body_expr = hir::Expr {
            hir_id: self.next_id(),
            kind: hir::ExprKind::Block(outer_body_block, None),
            span,
        };
        
        // Create outer closure: |__dag_s| { spawn calls }
        let outer_closure_node_id = self.next_node_id();
        let outer_closure_def_id = self.local_def_id(outer_closure_node_id);
        
        // Create parameter for outer closure
        let scope_param_hir_id = self.next_id();
        let scope_param = self.arena.alloc(hir::Param {
            hir_id: scope_param_hir_id,
            pat: scope_pat,
            ty_span: span,
            span,
        });
        
        let outer_closure_body = self.lower_body(|_this| {
            (std::slice::from_ref(scope_param), outer_body_expr)
        });
        
        let outer_closure = self.arena.alloc(hir::Expr {
            hir_id: self.next_id(),
            kind: hir::ExprKind::Closure(self.arena.alloc(hir::Closure {
                def_id: outer_closure_def_id,
                binder: hir::ClosureBinder::Default,
                constness: hir::Constness::NotConst,
                capture_clause: hir::CaptureBy::Ref,
                bound_generic_params: &[],
                fn_decl: self.arena.alloc(hir::FnDecl {
                    inputs: self.arena.alloc_from_iter([hir::Ty {
                        hir_id: self.next_id(),
                        kind: hir::TyKind::Infer(()),
                        span,
                    }]),
                    output: hir::FnRetTy::DefaultReturn(span),
                    c_variadic: false,
                    implicit_self: hir::ImplicitSelfKind::None,
                    lifetime_elision_allowed: true,
                }),
                body: outer_closure_body,
                fn_decl_span: span,
                fn_arg_span: Some(span),
                kind: hir::ClosureKind::Closure,
            })),
            span,
        });
        
        // Call thread::scope with the closure
        let scope_call = self.expr_call_lang_item_fn(
            span,
            hir::LangItem::ThreadScope,
            std::slice::from_ref(outer_closure),
        );
        
        scope_call
    }
    
    fn lower_stmt_into(
        &mut self,
        stmts: &mut SmallVec<[hir::Stmt<'hir>; 8]>,
        expr: &mut Option<&'hir hir::Expr<'hir>>,
        s: &Stmt,
        is_last: bool,
    ) {
        match &s.kind {
            StmtKind::Let(local) => {
                let hir_id = self.lower_node_id(s.id);
                let local = self.lower_local(local);
                self.alias_attrs(hir_id, local.hir_id);
                let kind = hir::StmtKind::Let(local);
                let span = self.lower_span(s.span);
                stmts.push(hir::Stmt { hir_id, kind, span });
            }
            StmtKind::Item(it) => {
                stmts.extend(self.lower_item_ref(it).into_iter().enumerate().map(
                    |(i, item_id)| {
                        let hir_id = match i {
                            0 => self.lower_node_id(s.id),
                            _ => self.next_id(),
                        };
                        let kind = hir::StmtKind::Item(item_id);
                        let span = self.lower_span(s.span);
                        hir::Stmt { hir_id, kind, span }
                    },
                ));
            }
            StmtKind::Expr(e) => {
                let e = self.lower_expr(e);
                if is_last {
                    *expr = Some(e);
                } else {
                    let hir_id = self.lower_node_id(s.id);
                    self.alias_attrs(hir_id, e.hir_id);
                    let kind = hir::StmtKind::Expr(e);
                    let span = self.lower_span(s.span);
                    stmts.push(hir::Stmt { hir_id, kind, span });
                }
            }
            StmtKind::Semi(e) => {
                let e = self.lower_expr(e);
                let hir_id = self.lower_node_id(s.id);
                self.alias_attrs(hir_id, e.hir_id);
                let kind = hir::StmtKind::Semi(e);
                let span = self.lower_span(s.span);
                stmts.push(hir::Stmt { hir_id, kind, span });
            }
            StmtKind::Empty => {}
            StmtKind::MacCall(..) => panic!("shouldn't exist here"),
            StmtKind::DagTask(dag_task) => {
                let task_block = self.lower_block(&dag_task.body, false);
                let hir_id = self.lower_node_id(s.id);
                let block_expr = self.arena.alloc(hir::Expr {
                    hir_id: self.next_id(),
                    kind: hir::ExprKind::Block(task_block, None),
                    span: self.lower_span(dag_task.span),
                });
                let kind = hir::StmtKind::Semi(block_expr);
                let span = self.lower_span(s.span);
                stmts.push(hir::Stmt { hir_id, kind, span });
            }
            StmtKind::DagEdge(dag_edge) => {
                if let ast::ExprKind::Call(_, _) = &dag_edge.from_expr.kind {
                    let edge_span = self.lower_span(dag_edge.span);
                    
                    let has_underscore = if let ast::ExprKind::Call(_, ref args) = dag_edge.to_expr.kind {
                        args.iter().any(|arg| matches!(arg.kind, ast::ExprKind::Underscore))
                    } else {
                        false
                    };
                    
                    if has_underscore {
                        let from_hir = self.lower_expr(&dag_edge.from_expr);
                        let result_ident = Ident::from_str("__dag_result");
                        let (pat, pat_hir_id) = self.pat_ident(edge_span, result_ident);
                        
                        let let_stmt = hir::LetStmt {
                            super_: None,
                            hir_id: self.lower_node_id(s.id),
                            init: Some(from_hir),
                            pat,
                            els: None,
                            source: hir::LocalSource::Normal,
                            span: edge_span,
                            ty: None,
                        };
                        stmts.push(hir::Stmt {
                            hir_id: self.next_id(),
                            kind: hir::StmtKind::Let(self.arena.alloc(let_stmt)),
                            span: edge_span,
                        });
                        
                        if let ast::ExprKind::Call(ref callee, ref args) = dag_edge.to_expr.kind {
                            let callee_hir = self.lower_expr(callee);
                            let new_args: Vec<hir::Expr<'hir>> = args.iter().map(|arg| {
                                if matches!(arg.kind, ast::ExprKind::Underscore) {
                                    let path = hir::QPath::Resolved(
                                        None,
                                        self.arena.alloc(hir::Path {
                                            span: edge_span,
                                            res: hir::def::Res::Local(pat_hir_id),
                                            segments: self.arena.alloc_from_iter([
                                                hir::PathSegment::new(result_ident, self.next_id(), hir::def::Res::Local(pat_hir_id))
                                            ]),
                                        }),
                                    );
                                    hir::Expr {
                                        hir_id: self.next_id(),
                                        kind: hir::ExprKind::Path(path),
                                        span: edge_span,
                                    }
                                } else {
                                    let lowered = self.lower_expr(arg);
                                    hir::Expr {
                                        hir_id: lowered.hir_id,
                                        kind: lowered.kind,
                                        span: lowered.span,
                                    }
                                }
                            }).collect();
                            
                            let call_expr = self.arena.alloc(hir::Expr {
                                hir_id: self.next_id(),
                                kind: hir::ExprKind::Call(callee_hir, self.arena.alloc_from_iter(new_args)),
                                span: self.lower_span(dag_edge.to_expr.span),
                            });
                            
                            stmts.push(hir::Stmt {
                                hir_id: self.next_id(),
                                kind: hir::StmtKind::Semi(call_expr),
                                span: self.lower_span(dag_edge.to_expr.span),
                            });
                        }
                    } else {
                        let from_hir = self.lower_expr(&dag_edge.from_expr);
                        let from_hir_id = self.lower_node_id(s.id);
                        let from_kind = hir::StmtKind::Semi(from_hir);
                        let from_span = self.lower_span(dag_edge.from_expr.span);
                        stmts.push(hir::Stmt { hir_id: from_hir_id, kind: from_kind, span: from_span });
                        
                        let to_hir = self.lower_expr(&dag_edge.to_expr);
                        let to_hir_id = self.next_id();
                        let to_kind = hir::StmtKind::Semi(to_hir);
                        let to_span = self.lower_span(dag_edge.to_expr.span);
                        stmts.push(hir::Stmt { hir_id: to_hir_id, kind: to_kind, span: to_span });
                    }
                }
            }
        }
    }

    /// Return an `ImplTraitContext` that allows impl trait in bindings if
    /// the feature gate is enabled, or issues a feature error if it is not.
    fn impl_trait_in_bindings_ctxt(&self, position: ImplTraitPosition) -> ImplTraitContext {
        if self.tcx.features().impl_trait_in_bindings() {
            ImplTraitContext::InBinding
        } else {
            ImplTraitContext::FeatureGated(position, sym::impl_trait_in_bindings)
        }
    }

    fn lower_local(&mut self, l: &Local) -> &'hir hir::LetStmt<'hir> {
        // Let statements are allowed to have impl trait in bindings.
        let super_ = l.super_.map(|span| self.lower_span(span));
        let ty = l.ty.as_ref().map(|t| {
            self.lower_ty(t, self.impl_trait_in_bindings_ctxt(ImplTraitPosition::Variable))
        });
        let init = l.kind.init().map(|init| self.lower_expr(init));
        let hir_id = self.lower_node_id(l.id);
        let pat = self.lower_pat(&l.pat);
        let els = if let LocalKind::InitElse(_, els) = &l.kind {
            Some(self.lower_block(els, false))
        } else {
            None
        };
        let span = self.lower_span(l.span);
        let source = hir::LocalSource::Normal;
        self.lower_attrs(hir_id, &l.attrs, l.span, Target::Statement);
        self.arena.alloc(hir::LetStmt { hir_id, super_, ty, pat, init, els, span, source })
    }

    fn lower_block_check_mode(&mut self, b: &BlockCheckMode) -> hir::BlockCheckMode {
        match *b {
            BlockCheckMode::Default => hir::BlockCheckMode::DefaultBlock,
            BlockCheckMode::Unsafe(u) => {
                hir::BlockCheckMode::UnsafeBlock(self.lower_unsafe_source(u))
            }
        }
    }
}
