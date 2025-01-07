use alloy_primitives::{Bytes, U256};
use revm_interpreter::OpCode;

#[derive(Debug)]
pub enum IR {
    Op(OpCode),
    Push(U256),
    PushOp(OpCode, U256),
    Raw(Vec<u8>),
}

impl IR {
    pub fn size(self) -> usize {
        match self {
            IR::Op(_) => 1,
            IR::Push(data) => 1 + data.byte_len(),
            IR::PushOp(op, _) => op.get() as usize - 0x5f + 1,
            IR::Raw(v) => v.len(),
        }
    }

    pub fn append(self, mut bytes: Vec<u8>) -> Vec<u8> {
        match self {
            IR::Op(op) => {
                assert!(!op.is_push(), "op must not be PUSH1..32");
                bytes.push(op.get());
            }
            IR::Push(data) => {
                bytes.push(0x59 + 32 - data.leading_zeros() as u8);
                if data > U256::ZERO {
                    bytes.extend_from_slice(data.to_be_bytes_vec().as_mut());
                }
            }
            IR::PushOp(op, data) => {
                assert!(op.is_push(), "op must be PUSH1..32");
                bytes.push(op.get());
                if data > U256::ZERO {
                    bytes.extend_from_slice(data.to_be_bytes_vec().as_mut());
                }
            }
            IR::Raw(raw_bytes) => bytes.extend(raw_bytes),
        }
        bytes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::uint;

    #[test]
    fn test_size() {
        assert_eq!(IR::Op(OpCode::STOP).size(), 1);

        assert_eq!(IR::Push(U256::ZERO).size(), 1);
        assert_eq!(IR::Push(uint!(1_U256)).size(), 2);
        assert_eq!(IR::Push(uint!(0x100_U256)).size(), 3);

        assert_eq!(IR::PushOp(OpCode::PUSH2, uint!(0x1_U256)).size(), 3);

        assert_eq!(IR::Raw(vec![0xc0, 0xfe]).size(), 2);
    }

    #[test]
    fn test_append() {
        assert_eq!(IR::Op(OpCode::STOP).append(vec![]), vec![0x00]);

        assert_eq!(IR::Push(U256::ZERO).append(vec![]), vec![0x59]);
        assert_eq!(IR::Push(uint!(1_U256)).append(vec![]), vec![0x60, 0x01]);
        assert_eq!(IR::Push(uint!(0x100_U256)).append(vec![]), vec![0x61, 0x01, 0x00]);

        assert_eq!(IR::PushOp(OpCode::PUSH2, uint!(0x1_U256)).append(vec![]), vec![
            0x62, 0x00, 0x01
        ]);

        assert_eq!(IR::Raw(vec![0xc0, 0xfe]).append(vec![]), vec![0xc0, 0xfe]);
    }
}
