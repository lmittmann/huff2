use huff_ast::{Constant, Definition, Macro, Root, RootSection, SolError, SolEvent, SolFunction, Span, Table};
use std::{
    collections::{HashMap, HashSet},
    fs::File,
};

use crate::{Contract, Error, MACRO_CONSTRUCTOR, MACRO_RUNTIME};

pub fn compile<'src>(ast: Root<'src>) -> Result<Contract, Error> {
    let fs = FileScope::new(ast)?;

    todo!();
}

#[derive(Debug, Clone)]
struct FileScope<'src> {
    filename: &'src str,
    globals: HashMap<&'src str, Definition<'src>>,
}

impl<'src> FileScope<'src> {
    pub fn new(root: Root<'src>) -> Result<Self, Error<'src>> {
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
                        filename: root.filename,
                        first: first_def.name(),
                        second: def_name,
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
                filename: root.filename,
            })?;

        Ok(FileScope {
            filename: root.filename,
            globals,
        })
    }

    pub fn compile(self) -> Result<Contract, Error<'src>> {
        todo!()
    }
}

#[derive(Debug, Clone)]
struct Scope {}
