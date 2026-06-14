use archsig_practical_rust_service_sample::scenario::run_demo;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let snapshot = run_demo()?;
    println!("{}", snapshot.render());
    Ok(())
}
