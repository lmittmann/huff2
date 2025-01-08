use huff_ast::Spanned;

#[derive(Debug)]
pub enum Error {
    DefinitionNameCollision {
        filename: String,
        first: Spanned<String>,
        second: Spanned<String>,
    },
    MissingMacroRuntimeOrConstructor {
        filename: String,
    },
}
