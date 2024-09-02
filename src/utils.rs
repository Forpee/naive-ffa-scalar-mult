use byteorder::WriteBytesExt;
use num_bigint::{BigInt, Sign};
use pasta_curves::group::ff::PrimeField;
use std::io::{self, Write};

fn write_be<F: PrimeField, W: Write>(f: &F, mut writer: W) -> io::Result<()> {
    for digit in f.to_repr().as_ref().iter().rev() {
        writer.write_u8(*digit)?;
    }

    Ok(())
}

/// Convert a field element to a natural number
pub fn f_to_nat<Scalar: PrimeField>(f: &Scalar) -> BigInt {
    let mut s = Vec::new();
    write_be(f, &mut s).unwrap();
    BigInt::from_bytes_le(Sign::Plus, f.to_repr().as_ref())
}
