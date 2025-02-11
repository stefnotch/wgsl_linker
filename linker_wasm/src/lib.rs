use no_panic::no_panic;
use wasm_bindgen::prelude::wasm_bindgen;

#[global_allocator]
static ALLOCATOR: talc::Talck<talc::locking::AssumeUnlockable, talc::ClaimOnOom> = {
    // From https://github.com/SFBdragon/talc/blob/75d049aaafe8a936f554a8930d90812719e3b0e8/wasm-size/src/lib.rs#L34
    const MEMORY_SIZE: usize = 128 * 1024 * 1024;
    static mut MEMORY: [std::mem::MaybeUninit<u8>; MEMORY_SIZE] =
        [std::mem::MaybeUninit::uninit(); MEMORY_SIZE];
    let span = talc::Span::from_array(std::ptr::addr_of_mut!(MEMORY));
    talc::Talc::new(unsafe { talc::ClaimOnOom::new(span) }).lock()
};

#[no_panic]
#[wasm_bindgen]
pub fn main(input: &str) -> String {
    let a = wesl_linker::parser::parse(input).unwrap();

    if a.0.len() > 3 {
        return "Hi".to_string();
    } else {
        return "Bye".to_string();
    }
}
