mod comp;
mod contract;
mod errors;
mod ir;
mod util;

pub use comp::compile;
pub use contract::Contract;
pub use errors::Error;

const MACRO_RUNTIME: &'static str = "RUNTIME";
const MACRO_CONSTRUCTOR: &'static str = "CONSTRUCTOR";
