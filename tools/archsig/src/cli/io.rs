pub(crate) fn write_json<T: serde::Serialize>(
    out: Option<PathBuf>,
    value: &T,
) -> Result<(), Box<dyn Error>> {
    match out {
        Some(path) => {
            if let Some(parent) = path.parent() {
                if !parent.as_os_str().is_empty() {
                    std::fs::create_dir_all(parent)?;
                }
            }
            let mut file = File::create(path)?;
            serde_json::to_writer_pretty(&mut file, value)?;
            writeln!(file)?;
        }
        None => {
            let stdout = io::stdout();
            let mut handle = stdout.lock();
            serde_json::to_writer_pretty(&mut handle, value)?;
            writeln!(handle)?;
        }
    }
    Ok(())
}
pub(crate) fn read_json<T: serde::de::DeserializeOwned>(path: &PathBuf) -> Result<T, Box<dyn Error>> {
    Ok(serde_json::from_reader(File::open(path)?)?)
}

pub(crate) fn require_schema(
    document: &serde_json::Value,
    expected: &str,
    field_name: &str,
) -> Result<(), Box<dyn Error>> {
    let actual = document
        .get("schemaVersion")
        .or_else(|| document.get("schema"))
        .and_then(|value| value.as_str());
    if actual != Some(expected) {
        return Err(format!("{field_name} must have schemaVersion {expected}").into());
    }
    Ok(())
}
