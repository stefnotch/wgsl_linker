use arcstr::ArcStr;

use super::ModulePath;

pub trait ReadonlyFilesystem {
    type Error;
    /// Responsible for reading files, and for caching the results.
    fn read(&self, path: &ModulePath) -> Result<ArcStr, Self::Error>;
}

#[derive(Default)]
pub struct EmptyFilesystem;

impl ReadonlyFilesystem for EmptyFilesystem {
    type Error = std::io::Error;

    fn read(&self, _path: &ModulePath) -> Result<ArcStr, Self::Error> {
        Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            "file not found",
        ))
    }
}

#[cfg(feature = "fs")]
pub struct PhysicalFilesystem {
    pub entry_point: std::path::PathBuf,
}

#[cfg(feature = "fs")]
impl ReadonlyFilesystem for PhysicalFilesystem {
    type Error = std::io::Error;

    fn read(&self, path: &ModulePath) -> Result<ArcStr, Self::Error> {
        let path = self
            .entry_point
            .join(path.path.iter().collect::<std::path::PathBuf>());
        std::fs::read_to_string(&path).map(ArcStr::from)
    }
}
