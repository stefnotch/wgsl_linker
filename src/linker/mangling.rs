use super::parsed_module::ModulePath;

pub struct UnmangledName {
    pub module: ModulePath,
    pub name: String,
}

pub fn write_mangled_name(module_name: &ModulePath, name: &str, output: &mut String) {
    // Length prefixing is a much simpler scheme, but it's not as readable
    for name_part in module_name.0.iter() {
        write_escaped(name_part, output);
        output.push('_');
    }
    write_escaped(name, output)
}

pub fn mangle_name(module_name: &ModulePath, name: &str) -> String {
    let mut output = String::new();
    write_mangled_name(module_name, name, &mut output);
    output
}

fn write_escaped(name: &str, output: &mut String) {
    for c in name.chars() {
        if c == '_' {
            output.push_str("__");
        } else {
            output.push(c);
        }
    }
}

pub fn unmangle_name(mangled_name: &str) -> UnmangledName {
    let mut name_parts = vec![];

    let mut mangled_chars = mangled_name.chars();
    let mut name = String::new();
    while let Some(c) = mangled_chars.next() {
        if c == '_' {
            match mangled_chars.next() {
                Some('_') => {
                    // Underscore escape
                    name.push('_');
                }
                Some(v) => {
                    name_parts.push(std::mem::take(&mut name));
                    name.push(v);
                }
                None => {
                    name_parts.push(std::mem::take(&mut name));
                }
            }
        } else {
            name.push(c);
        }
    }

    // Whatever is left over is the name itself.

    UnmangledName {
        module: ModulePath(name_parts),
        name,
    }
}
