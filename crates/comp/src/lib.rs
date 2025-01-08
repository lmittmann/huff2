mod comp;
mod contract;
mod errors;
mod ir;
mod util;

pub use comp::compile;
pub use contract::Contract;
pub use errors::Error;

const MACRO_RUNTIME: &str = "RUNTIME";
const MACRO_CONSTRUCTOR: &str = "CONSTRUCTOR";
