use alloy_primitives::U256;

pub(crate) trait U256Extensions {
    /// Returns the bytes of the U256 value stripped of leading zeros.
    fn bytes(&self) -> Vec<u8>;
}

// Implement the trait for U256
impl U256Extensions for U256 {
    fn bytes(&self) -> Vec<u8> {
        let bytes = self.to_be_bytes_vec();
        let leading_zeros = bytes.iter().take_while(|&&b| b == 0).count();
        bytes[leading_zeros..].to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloy_primitives::uint;

    #[test]
    fn test_bytes() {
        assert_eq!(uint!(0x0_U256).bytes(), vec![]);
        assert_eq!(uint!(0x1_U256).bytes(), vec![1]);
        assert_eq!(uint!(0x100_U256).bytes(), vec![1, 0]);
        assert_eq!(uint!(0x10000_U256).bytes(), vec![1, 0, 0]);
    }
}
