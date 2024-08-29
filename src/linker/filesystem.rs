use super::ModulePath;

pub trait ReadonlyFilesystem {
    type Error;
    fn read(&self, path: &ModulePath) -> Result<String, Self::Error>;
}

#[derive(Default)]
pub struct EmptyFilesystem;

impl ReadonlyFilesystem for EmptyFilesystem {
    type Error = std::io::Error;

    fn read(&self, _path: &ModulePath) -> Result<String, Self::Error> {
        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            "file not found",
        ))
    }
}

pub struct PhysicalFilesystem {
    pub entry_point: std::path::PathBuf,
}

impl ReadonlyFilesystem for PhysicalFilesystem {
    type Error = std::io::Error;

    fn read(&self, path: &ModulePath) -> Result<String, Self::Error> {
        // TODO:
        todo!()
    }
}
