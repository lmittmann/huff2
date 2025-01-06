use huff_ast::Spanned;

#[derive(Debug)]
pub enum Error<'src> {
    DefinitionNameCollision {
        first: Spanned<&'src str>,
        second: Spanned<&'src str>,
    },
}
