use crate::Spanned;
use alloy_dyn_abi::DynSolType;
use alloy_primitives::{keccak256, FixedBytes};

pub fn compute_selector(name: &Spanned<&str>, args: &[&Spanned<DynSolType>]) -> FixedBytes<4> {
    let arg_types: Vec<String> = args.iter().map(|arg| arg.0.to_string()).collect();

    let signature = format!("{}({})", name.0, arg_types.join(","));
    let hash = keccak256(signature.as_bytes());
    FixedBytes::<4>::from_slice(&hash[..4])
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{SolError, SolFunction};
    use chumsky::span::Span;

    #[test]

    fn test_compute_selector() {
        let func = SolFunction {
            name: Spanned::new("transfer", 0..8),
            args: Box::new([Spanned::new(DynSolType::Address, 9..17), Spanned::new(DynSolType::Uint(256), 18..26)]),
            rets: Box::new([]),
        };

        let err = SolError {
            name: Spanned::new("TransferFailed", 0..15),
            args: Box::new([Spanned::new(DynSolType::String, 16..21), Spanned::new(DynSolType::Uint(256), 22..30)]),
        };

        let func_selector = compute_selector(&func.name, func.args.iter().collect::<Vec<_>>().as_slice());
        let err_selector = compute_selector(&err.name, err.args.iter().collect::<Vec<_>>().as_slice());

        let expected_func_signature = "transfer(address,uint256)";
        let expected_err_signature = "TransferFailed(string,uint256)";

        let expected_func_hash = keccak256(expected_func_signature.as_bytes());
        let expected_err_hash = keccak256(expected_err_signature.as_bytes());

        let expected_func_selector = FixedBytes::<4>::from_slice(&expected_func_hash[..4]);
        let expected_err_selector = FixedBytes::<4>::from_slice(&expected_err_hash[..4]);

        assert_eq!(func_selector, expected_func_selector);
        assert_eq!(err_selector, expected_err_selector);
    }
}
