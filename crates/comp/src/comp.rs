use alloy_primitives::Bytes;
use huff_ast::{Definition, Macro, MacroStatement, Root, RootSection, Span};
use std::collections::HashMap;

use crate::{Contract, Error, MACRO_CONSTRUCTOR, MACRO_RUNTIME};

pub fn compile(ast: Root<'_>) -> Result<Contract, Error> {
    let file_scope = FileScope::new(ast)?;

    let runtime_scope = file_scope
        .globals
        .get(MACRO_RUNTIME)
        .map(|def| match def {
            Definition::Macro(m) => m,
            _ => unreachable!("RUNTIME must be macro"),
        })
        .map(|m| MacroScope::new(m.clone()));

    if let Some(runtime_scope) = runtime_scope {
        let mut scope_stack = vec![runtime_scope];

        let mut runtime = Bytes::new();
        while let Some(peek_scope) = scope_stack.last() {}

        return Ok(Contract {
            runtime,
            constructor: Bytes::new(),
        });
    }

    todo!();
}

#[derive(Debug, Clone)]
struct FileScope<'src> {
    filename: &'src str,
    globals: HashMap<&'src str, Definition<'src>>,
}

impl<'src> FileScope<'src> {
    pub fn new(root: Root<'src>) -> Result<Self, Error> {
        // collect all definitions and verify they are unique by name
        let globals = root
            .sections
            .iter()
            .filter_map(|section| match section {
                RootSection::Definition(def) => Some(def),
                _ => None,
            })
            .try_fold(HashMap::<&str, Definition>::new(), |mut globals, def| {
                let def_name = def.name();
                if let Some(first_def) = globals.get(def_name.0) {
                    return Err(Error::DefinitionNameCollision {
                        filename: root.filename.to_string(),
                        first: (first_def.name().0.to_string(), first_def.name().1),
                        second: (def_name.0.to_string(), def_name.1),
                    });
                }
                globals.insert(def_name.0, def.clone());
                Ok(globals)
            })?;

        // verify presence of either RUNTIME or CONSTRUCTOR macro
        globals
            .get(MACRO_RUNTIME)
            .or_else(|| globals.get(MACRO_CONSTRUCTOR))
            .map(|def| match def {
                Definition::Macro(m) => Some(m),
                _ => None,
            })
            .ok_or(Error::MissingMacroRuntimeOrConstructor {
                filename: root.filename.to_string(),
            })?;

        Ok(FileScope {
            filename: root.filename,
            globals,
        })
    }
}

#[derive(Debug, Clone)]
struct MacroScope<'src> {
    r#macro: Macro<'src>,
    jumpdest_labels: HashMap<&'src str, (usize, Span)>,
}

impl<'src> MacroScope<'src> {
    pub fn new(m: Macro<'src>) -> Self {
        let jumpdest_labels = m
            .body
            .iter()
            .filter_map(|s| match s {
                MacroStatement::LabelDefinition(label) => Some((label.0, (0, label.1))),
                _ => None,
            })
            .fold(HashMap::new(), |mut map, (k, v)| {
                map.insert(k, v);
                map
            });
        MacroScope {
            r#macro: m,
            jumpdest_labels: HashMap::new(),
        }
    }
}
