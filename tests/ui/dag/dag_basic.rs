// Test basic DAG function syntax
// run-pass

// DAG function that defines tasks and their dependencies
dag fn simple_dag() {
    // Define tasks
    task A {
        println!("Executing task A");
    }

    task B {
        println!("Executing task B");
    }

    task C {
        println!("Executing task C");
    }

    // Define dependencies (edges)
    // A -> B means B depends on A (A must run before B)
    edge A -> B;
    edge A -> C;
    edge B -> C;
}

fn main() {
    // Call the DAG function
    simple_dag();
    println!("DAG execution completed!");
}
