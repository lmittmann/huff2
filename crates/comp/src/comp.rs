use huff_ast::{Constant, Definition, Macro, Root, RootSection, SolError, SolEvent, SolFunction, Span, Table};
use std::collections::{HashMap, HashSet};

use crate::{Contract, Error};

pub fn compile<'src>(ast: Root<'src>) -> Result<Contract, Error> {
    Scope::new(ast)?.compile()
}

#[derive(Debug, Clone, Default)]
struct Scope<'src> {
    macros: HashMap<&'src str, Macro<'src>>,
    constants: HashMap<&'src str, Constant<'src>>,
    tables: HashMap<&'src str, Table<'src>>,
    sol_functions: HashMap<&'src str, SolFunction<'src>>,
    sol_events: HashMap<&'src str, SolEvent<'src>>,
    sol_errors: HashMap<&'src str, SolError<'src>>,
}

impl<'src> Scope<'src> {
    pub fn new(root: Root<'src>) -> Result<Self, Error<'src>> {
        let mut s = Self::default();
        root.0
            .iter()
            .filter_map(|section| match section {
                RootSection::Definition(def) => Some(def),
                _ => None,
            })
            .try_fold(
                (Vec::new(), HashMap::<&str, Span>::new()),
                |(mut defs, mut names), def| {
                    let name_span = def.name();
                    if let Some(first_span) = names.get(name_span.0) {
                        return Err(Error::DefinitionNameCollision {
                            first: (name_span.0, first_span.clone()),
                            second: name_span,
                        });
                    } else {
                        defs.push(def);
                        names.insert(name_span.0, name_span.1);
                        Ok((defs, names))
                    }
                },
            )?
            .0
            .iter()
            .for_each(|def| {
                let k = def.name().0;
                match def {
                    Definition::Macro(m) => s.macros.insert(k, m.clone()).is_none(),
                    Definition::Constant(c) => s.constants.insert(k, c.clone()).is_none(),
                    Definition::Table(t) => s.tables.insert(k, t.clone()).is_none(),
                    Definition::SolFunction(f) => s.sol_functions.insert(k, f.clone()).is_none(),
                    Definition::SolEvent(e) => s.sol_events.insert(k, e.clone()).is_none(),
                    Definition::SolError(e) => s.sol_errors.insert(k, e.clone()).is_none(),
                };
            });

        Ok(s)
    }

    pub fn compile(self) -> Result<Contract, Error<'src>> {
        todo!()
    }
}
