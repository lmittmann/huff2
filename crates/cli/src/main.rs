use ariadne::{Color, Config, Fmt, IndexType, Label, Report, ReportKind, sources};
use clap::Parser as ClapParser;
use huff_ast::{RootSection, parse};
use huff_comp::compile;
use std::collections::BTreeSet;

mod versions;
use versions::EvmVersion;

/// Huff Language Compiler
#[derive(ClapParser)]
struct Cli {
    /// filename
    #[clap(help = "Root huff file to compile")]
    filename: String,

    #[clap(
        short = 'e',
        long = "evm-version",
        help = "What EVM version to use, NOTE: Pre-EOF this option only affects the use of PUSH0.",
        default_value = "paris"
    )]
    evm_version: EvmVersion,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    if matches!(cli.evm_version, EvmVersion::Eof) {
        eprintln!("{}: EVM Version 'EOF' not yet supported", "Error".fg(Color::Red),);
        std::process::exit(1);
    }

    let src_res = std::fs::read_to_string(&cli.filename);

    if let Err(err) = &src_res {
        if let std::io::ErrorKind::NotFound = err.kind() {
            eprintln!(
                "{}: File with path '{}' not found",
                "Error".fg(Color::Red),
                cli.filename.escape_debug()
            );
            std::process::exit(1);
        }
    };

    let src = src_res?;

    let filename: String = cli.filename;

    let ast = match parse(&src, &filename) {
        Ok(ast) => ast,
        Err(errs) => {
            errs.into_iter().for_each(|e| {
                Report::build(ReportKind::Error, filename.clone(), e.span().start)
                    .with_config(Config::default().with_index_type(IndexType::Byte))
                    // .with_message(e.reason())
                    .with_label(
                        Label::new((filename.clone(), e.span().into_range()))
                            .with_message(e.reason())
                            .with_color(Color::Red),
                    )
                    .finish()
                    .eprint(sources([(filename.clone(), &src)]))
                    .unwrap()
            });

            std::process::exit(1);
        }
    };
    println!("{:?}", ast);

    match compile(ast) {
        Ok(c) => println!("{:?}", c),
        Err(e) => {
            eprintln!("Compilation failed {:?}", e);
            std::process::exit(1);
        }
    }

    // let mut analysis_errors = Vec::with_capacity(5);
    // let global_defs = build_ident_map(ast.0.iter().filter_map(|section| match section {
    //     RootSection::Include(huff_include) => {
    //         analysis_errors.push(errors::AnalysisError::NotYetSupported {
    //             intent: "Huff '#include'".to_owned(),
    //             span: ((), huff_include.1),
    //         });
    //         None
    //     }
    //     RootSection::Definition(def) => Some(def),
    // }));
    // let unique_defs = analyze_global_for_dups(&global_defs, |err| analysis_errors.push(err));

    // {
    //     let mut to_analyze_stack = vec![CodeInclusionFrame::top(cli.entry_point.as_str())];
    //     let mut analyzed_macros = BTreeSet::new();
    //     while let Some(next_entrypoint) = to_analyze_stack.last() {
    //         let idx_to_remove = to_analyze_stack.len() - 1;
    //         if analyzed_macros.insert(next_entrypoint.name) {
    //             analyze_entry_point(
    //                 &global_defs,
    //                 next_entrypoint.name,
    //                 |err| analysis_errors.push(err),
    //                 &mut to_analyze_stack,
    //             );
    //         }
    //         to_analyze_stack.remove(idx_to_remove);
    //     }
    // }

    // if !analysis_errors.is_empty() {
    //     analysis_errors.into_iter().for_each(|err| {
    //         err.report(filename.clone())
    //             .eprint(sources([(filename.clone(), &src)]))
    //             .unwrap()
    //     });
    //     std::process::exit(1);
    // }

    // let mut config = CompileGlobals::new(cli.optimize, cli.evm_version.allows_push0(), unique_defs);

    // let entry_point_macro = match config.defs.get(cli.entry_point.as_str()) {
    //     Some(huff_ast::Definition::Macro(entry_point)) => entry_point,
    //     _ => panic!("macro not found despite no errors in analysis"),
    // };
    // let mut entry_point_code = generate_for_entrypoint(&mut config, entry_point_macro);
    // if cli.add_default_constructor {
    //     entry_point_code = config.assemble(&generate_default_constructor(entry_point_code));
    // }

    // println!("0x{}", hex::encode(entry_point_code));

    Ok(())
}
