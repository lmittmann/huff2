use alloy_primitives::Bytes;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Contract {
    pub runtime: Bytes,
    pub constructor: Bytes,
}
