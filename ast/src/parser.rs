use crate::*;
use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::{
    error::Rich,
    extra,
    primitive::{choice, just},
    text::{digits, ident, int, keyword},
    IterParser, Parser,
};

/// parse the source string into an AST.
pub fn parse<'a>(src: &'a str) -> Result<Root<'a>, Vec<Rich<'a, char>>> {
    root().parse(src).into_result()
}

trait HuffParser<'a, T>: Parser<'a, &'a str, T, extra::Err<Rich<'a, char>>> {}
impl<'a, P, T> HuffParser<'a, T> for P where P: Parser<'a, &'a str, T, extra::Err<Rich<'a, char>>> {}

fn root<'a>() -> impl HuffParser<'a, Root<'a>> {
    definition().repeated().collect().map(Root)
}

fn definition<'a>() -> impl HuffParser<'a, HuffDefinition<'a>> {
    just("#define").ignore_then(choice((constant(),)).padded())
}

fn constant<'a>() -> impl HuffParser<'a, HuffDefinition<'a>> {
    keyword("constant")
        .ignore_then(identifier())
        .then_ignore(just("="))
        .then(word())
        .map(|(name, value)| HuffDefinition::Constant { name, value })
}

fn identifier<'a>() -> impl HuffParser<'a, &'a str> {
    ident().to_slice().padded()
}

fn word<'a>() -> impl HuffParser<'a, U256> {
    choice((
        just("0x").ignore_then(
            digits(16)
                .at_least(1)
                .collect::<String>()
                .map(|s| U256::from_str_radix(&s, 16).unwrap()),
        ),
        just("0b").ignore_then(
            digits(2)
                .at_least(1)
                .collect::<String>()
                .map(|s| U256::from_str_radix(&s, 2).unwrap())
                .map_err(Rich::from),
        ),
        int(10)
            .map(|s| U256::from_str_radix(s, 10).unwrap())
            .map_err(Rich::from),
    ))
    .padded()
}
