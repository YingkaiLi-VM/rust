use rustc_ast::{self as ast, Block, BlockCheckMode, Local, LocalKind, Stmt, StmtKind};
use rustc_hir as hir;
use rustc_hir::Target;
use rustc_span::{Ident, sym};
use smallvec::SmallVec;

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
        while let [s, tail @ ..] = ast_stmts {
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
                    if tail.is_empty() {
                        expr = Some(e);
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
                    // Lower the task body as a block expression
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
            ast_stmts = tail;
        }
        (self.arena.alloc_from_iter(stmts), expr)
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
