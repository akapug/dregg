//! Small, deliberately direct polynomial arithmetic for the two LB-VRF rings.

use crate::{
    DEGREE, MODULUS_P, MODULUS_Q, MSIS_RANK, OUTPUT_DEGREE, OUTPUT_POLYNOMIAL_CONSTANT,
    SECRET_WIDTH,
};

pub(crate) type OutputPoly = [u32; OUTPUT_DEGREE];

pub(crate) fn matrix_vector_product(
    matrix: &[[[u32; DEGREE]; SECRET_WIDTH]; MSIS_RANK],
    vector: &[[i32; DEGREE]; SECRET_WIDTH],
) -> [[u32; DEGREE]; MSIS_RANK] {
    let mut result = [[0_u32; DEGREE]; MSIS_RANK];
    for row in 0..MSIS_RANK {
        for column in 0..SECRET_WIDTH {
            let product = mul_q_signed(&matrix[row][column], &vector[column]);
            result[row] = add_q(&result[row], &product);
        }
    }
    result
}

pub(crate) fn mul_q_signed(a: &[u32; DEGREE], b: &[i32; DEGREE]) -> [u32; DEGREE] {
    let mut convolution = [0_i128; DEGREE * 2];
    for (i, &left) in a.iter().enumerate() {
        for (j, &right) in b.iter().enumerate() {
            convolution[i + j] += i128::from(left) * i128::from(right);
        }
    }
    let mut result = [0_u32; DEGREE];
    let q = i128::from(MODULUS_Q);
    for i in 0..DEGREE {
        result[i] = (convolution[i] - convolution[i + DEGREE]).rem_euclid(q) as u32;
    }
    result
}

pub(crate) fn add_q(a: &[u32; DEGREE], b: &[u32; DEGREE]) -> [u32; DEGREE] {
    let mut result = [0_u32; DEGREE];
    for i in 0..DEGREE {
        let sum = u64::from(a[i]) + u64::from(b[i]);
        result[i] = (sum % u64::from(MODULUS_Q)) as u32;
    }
    result
}

pub(crate) fn sub_q(a: &[u32; DEGREE], b: &[u32; DEGREE]) -> [u32; DEGREE] {
    let mut result = [0_u32; DEGREE];
    for i in 0..DEGREE {
        result[i] = (i64::from(a[i]) - i64::from(b[i])).rem_euclid(i64::from(MODULUS_Q)) as u32;
    }
    result
}

/// Reduces an `R_q` representative into `Z_p[x]/(x^32+852368)`.
pub(crate) fn reduce_to_output<T: Into<i32> + Copy>(poly: [T; DEGREE]) -> OutputPoly {
    let p = i128::from(MODULUS_P);
    let negative_constant = -i128::from(OUTPUT_POLYNOMIAL_CONSTANT);
    let mut powers = [0_i128; DEGREE / OUTPUT_DEGREE];
    powers[0] = 1;
    for i in 1..powers.len() {
        powers[i] = (powers[i - 1] * negative_constant).rem_euclid(p);
    }

    let mut accum = [0_i128; OUTPUT_DEGREE];
    for (index, coefficient) in poly.into_iter().enumerate() {
        accum[index % OUTPUT_DEGREE] +=
            i128::from(coefficient.into()) * powers[index / OUTPUT_DEGREE];
    }
    accum.map(|coefficient| coefficient.rem_euclid(p) as u32)
}

pub(crate) fn inner_product_output(
    a: &[OutputPoly; SECRET_WIDTH],
    b: &[OutputPoly; SECRET_WIDTH],
) -> OutputPoly {
    let mut result = [0_u32; OUTPUT_DEGREE];
    for i in 0..SECRET_WIDTH {
        result = add_output(&result, &mul_output(&a[i], &b[i]));
    }
    result
}

pub(crate) fn mul_output(a: &OutputPoly, b: &OutputPoly) -> OutputPoly {
    let mut convolution = [0_i128; OUTPUT_DEGREE * 2];
    for (i, &left) in a.iter().enumerate() {
        for (j, &right) in b.iter().enumerate() {
            convolution[i + j] += i128::from(left) * i128::from(right);
        }
    }

    let p = i128::from(MODULUS_P);
    let constant = i128::from(OUTPUT_POLYNOMIAL_CONSTANT);
    let mut result = [0_u32; OUTPUT_DEGREE];
    for i in 0..OUTPUT_DEGREE {
        result[i] =
            (convolution[i] - constant * convolution[i + OUTPUT_DEGREE]).rem_euclid(p) as u32;
    }
    result
}

fn add_output(a: &OutputPoly, b: &OutputPoly) -> OutputPoly {
    let mut result = [0_u32; OUTPUT_DEGREE];
    for i in 0..OUTPUT_DEGREE {
        result[i] = ((u64::from(a[i]) + u64::from(b[i])) % u64::from(MODULUS_P)) as u32;
    }
    result
}

pub(crate) fn sub_output(a: &OutputPoly, b: &OutputPoly) -> OutputPoly {
    let mut result = [0_u32; OUTPUT_DEGREE];
    for i in 0..OUTPUT_DEGREE {
        result[i] = (i64::from(a[i]) - i64::from(b[i])).rem_euclid(i64::from(MODULUS_P)) as u32;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn main_ring_is_negacyclic() {
        let mut x_to_255 = [0_u32; DEGREE];
        x_to_255[DEGREE - 1] = 1;
        let mut x = [0_i32; DEGREE];
        x[1] = 1;
        let product = mul_q_signed(&x_to_255, &x);
        assert_eq!(product[0], MODULUS_Q - 1);
        assert!(product[1..].iter().all(|&coefficient| coefficient == 0));
    }

    #[test]
    fn paper_output_factor_and_multiplication_agree() {
        // (x^32 + r) divides x^256 + 1 exactly when r^8 = -1 mod p.
        let mut r_to_eight = 1_u64;
        for _ in 0..8 {
            r_to_eight = r_to_eight * u64::from(OUTPUT_POLYNOMIAL_CONSTANT) % u64::from(MODULUS_P);
        }
        assert_eq!(r_to_eight as u32, MODULUS_P - 1);

        let mut x_to_31 = [0_u32; OUTPUT_DEGREE];
        x_to_31[OUTPUT_DEGREE - 1] = 1;
        let mut x = [0_u32; OUTPUT_DEGREE];
        x[1] = 1;
        let product = mul_output(&x_to_31, &x);
        assert_eq!(product[0], MODULUS_P - OUTPUT_POLYNOMIAL_CONSTANT);
        assert!(product[1..].iter().all(|&coefficient| coefficient == 0));
    }
}
