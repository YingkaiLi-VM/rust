
dag fn pipeline_dag() {
    task fetch_data {
        println!("Fetching data...");
    }

    task process_data {
        println!("Processing data...");
    }

    task save_result {
        println!("Saving result...");
    }
    edge fetch_data -> process_data;
    edge process_data -> save_result;
}

dag fn parallel_dag() {
    task A {
        println!("Task A - start");
        std::thread::sleep(std::time::Duration::from_millis(100));
        println!("Task A - end");
    }

    task B {
        println!("Task B - start");
        std::thread::sleep(std::time::Duration::from_millis(100));
        println!("Task B - end");
    }

    task C {
        println!("Task C - start");
        std::thread::sleep(std::time::Duration::from_millis(100));
        println!("Task C - end");
    }

    task D {
        println!("Task D - depends on B and C");
    }
    edge A -> B;
    edge A -> C;
    edge B -> D;
    edge C -> D;
}

dag fn task_a(x: i32) -> i32 {
    println!("Executing task A with x = {}", x);
    x * 2
}

dag fn task_b(y: i32, z: i32) -> i32 {
    println!("Executing task B with y = {}, z = {}", y, z);
    y + z
}

dag fn task_c(result: i32) {
    println!("Executing task C with result = {}", result);
}


fn test_keywords_as_variables() {

    let edge = 42;
    println!("edge = {}", edge);
    
 
    let task = "hello";
    println!("task = {}", task);
    

    let dag = vec![1, 2, 3];
    println!("dag = {:?}", dag);
}

fn main() {
    println!("=== Style 1: DAG with internal tasks ===");
    pipeline_dag();
    parallel_dag();
    println!("\n=== Style 2: Chaining dag functions with edge ===");
    edge task_a(10) -> task_b(_, 30);
    edge task_b(20, 30) -> task_c(_);
    
    println!("\n=== Test keywords as variables ===");
    test_keywords_as_variables();
    
    println!("\nDAG execution completed!");
}
