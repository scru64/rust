use scru64::generator::GlobalGenerator;

/// Tests the initialization of `GlobalGenerator` by reading the environment variable and the
/// `new_sync()` and `new_string_sync()` entry point functions.
fn main() {
    // SAFETY: ok because this example is a single-threaded program.
    unsafe { std::env::set_var("SCRU64_NODE_SPEC", "42/8") };

    assert_eq!(GlobalGenerator.node_id(), 42);
    assert_eq!(GlobalGenerator.node_id_size(), 8);
    assert_eq!(GlobalGenerator.node_spec().to_string(), "42/8");

    let mut prev = scru64::new_sync();
    for _ in 0..100_000 {
        let curr = scru64::new_sync();
        assert!(prev < curr);
        prev = curr;
    }

    let mut prev = String::from(prev);
    for _ in 0..100_000 {
        let curr = scru64::new_string_sync();
        assert!(prev < curr);
        prev = curr;
    }

    println!("test {} ... ok", file!());
}
