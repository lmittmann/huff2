use huff_ast::Spanned;

#[derive(Debug)]
pub enum Error<'src> {
    DefinitionNameCollision {
        filename: &'src str,
        first: Spanned<&'src str>,
        second: Spanned<&'src str>,
    },
    MissingMacroRuntimeOrConstructor {
        filename: &'src str,
    },
}
