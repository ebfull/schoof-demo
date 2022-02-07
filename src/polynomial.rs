//! Implementation of univariate polynomial arithmetic

use num_bigint::BigUint;
use num_traits::identities::{One, Zero};

use crate::util::{modinv, one, zero};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial<'a> {
    pub(crate) coeffs: Vec<BigUint>,
    pub(crate) modulus: &'a BigUint,
}

impl<'a> Polynomial<'a> {
    /// Constructs a new polynomial given the modulus and some coefficients in
    /// little endian order.
    pub fn new(modulus: &'a BigUint, coeffs: &[BigUint]) -> Self {
        assert!(coeffs.len() > 0);
        let mut tmp = Polynomial {
            coeffs: coeffs.iter().map(|int| int % modulus).collect(),
            modulus,
        };
        tmp.normalize();
        tmp
    }

    /// Ensures there is at least one coefficient, and that unless this is the
    /// zero polynomial then the leading term must be nonzero.
    fn normalize(&mut self) {
        let mut trim = 0;
        for coeff in self.coeffs.iter().rev() {
            if coeff.is_zero() {
                trim += 1;
            } else {
                break;
            }
        }
        let newlen = self.coeffs.len() - trim;
        self.coeffs.truncate(std::cmp::max(1, newlen));
    }

    /// Evaluate this polynomial at `point`
    pub fn eval(&self, point: &BigUint) -> BigUint {
        let point = &(point % self.modulus);
        let mut acc = zero();
        for coeff in self.coeffs.iter().rev() {
            acc = (acc * point + coeff) % self.modulus;
        }
        acc
    }

    /// Multiplies a polynomial with another polynomial
    pub fn mul(a: &Self, b: &Self) -> Self {
        assert_eq!(a.modulus, b.modulus);
        // schoolbook multiplication
        let mut result = vec![zero(); a.degree() + b.degree() + 1];
        for i in 0..a.coeffs.len() {
            for j in 0..b.coeffs.len() {
                result[i + j] += &a.coeffs[i] * &b.coeffs[j];
                result[i + j] = &result[i + j] % a.modulus;
            }
        }
        let mut tmp = Polynomial {
            coeffs: result,
            modulus: a.modulus,
        };
        tmp.normalize();
        tmp
    }

    /// Adds a polynomial to another polynomial
    pub fn add<'b>(mut a: &'b Self, mut b: &'b Self) -> Self {
        assert_eq!(a.modulus, b.modulus);
        let modulus = a.modulus;

        // Ensure a has larger or equal degree to b
        if a.degree() < b.degree() {
            std::mem::swap(&mut a, &mut b);
        }

        let mut result = a.coeffs.clone();
        for (result, b) in result.iter_mut().zip(b.coeffs.iter()) {
            *result = (&*result + b) % modulus;
        }

        let mut tmp = Polynomial {
            coeffs: result,
            modulus: a.modulus,
        };
        tmp.normalize();
        tmp
    }

    /// Negates this polynomial
    pub fn neg(&self) -> Self {
        let mut coeffs = self.coeffs.clone();
        for coeff in &mut coeffs {
            *coeff = (self.modulus - &*coeff) % self.modulus;
        }
        // No need to normalize, because leading term cannot be zero after
        // negation if it was not zero before.
        Polynomial {
            coeffs,
            modulus: self.modulus,
        }
    }

    /// Divides a polynomial by another, returning the quotient and remainder.
    pub fn divrem(dividend: &Self, divisor: &Self) -> (Self, Self) {
        assert_eq!(dividend.modulus, divisor.modulus);
        if divisor.is_zero() {
            panic!("division by zero");
        } else if dividend.degree() < divisor.degree() {
            (Self::new(dividend.modulus, &[zero()]), dividend.clone())
        } else {
            let modulus = divisor.modulus;
            // TODO: modulus is always prime here, so maybe exponentiating by
            // modulus - 2 would be more efficient?
            let inv = modinv(&divisor.leading_term(), modulus).unwrap();
            let mut remainder = dividend.clone();
            let mut quotient = vec![zero(); (remainder.degree() - divisor.degree()) + 1];

            while !remainder.is_zero() {
                let power = remainder.degree() - divisor.degree();
                let q = (remainder.leading_term() * &inv) % modulus;
                for (divisor_coeff, remainder_coeff) in divisor
                    .coeffs
                    .iter()
                    .zip(remainder.coeffs.iter_mut().skip(power))
                {
                    let tmp = (&q * divisor_coeff) % modulus;
                    let tmp = modulus - tmp;
                    *remainder_coeff = (&*remainder_coeff + tmp) % modulus;
                }
                quotient[power] = q;
                remainder.normalize();
                if remainder.degree() < divisor.degree() {
                    break;
                }
            }
            let mut quotient = Polynomial {
                modulus: divisor.modulus,
                coeffs: quotient,
            };
            quotient.normalize();

            (quotient, remainder)
        }
    }

    pub fn gcd<'b>(a: &'b Self, b: &'b Self) -> Self {
        assert_eq!(a.modulus, b.modulus);
        let mut result = Self::gcd_inner(a, b);
        // Force the GCD to be monic
        if !result.is_zero() {
            let modulus = result.modulus;
            let inv = modinv(result.leading_term(), result.modulus).unwrap();
            for coeff in result.coeffs.iter_mut() {
                *coeff = (&*coeff * &inv) % modulus;
            }
        }
        // Doesn't need to be normalized.
        result
    }

    fn gcd_inner<'b>(mut a: &'b Self, mut b: &'b Self) -> Self {
        if a.degree() < b.degree() {
            std::mem::swap(&mut a, &mut b);
        }

        if b.is_zero() {
            a.clone()
        } else {
            let (_, remainder) = Polynomial::divrem(&a, &b);
            Polynomial::gcd_inner(b, &remainder)
        }
    }

    pub fn inverse(&self, modulo: &Self) -> Option<Self> {
        assert_eq!(self.modulus, modulo.modulus);

        let mut r0 = self.clone();
        let mut s0 = Polynomial::new(self.modulus, &[one()]);
        let mut r1 = modulo.clone();
        let mut s1 = Polynomial::new(self.modulus, &[zero()]);

        while !r1.is_zero() {
            let (q, _) = Polynomial::divrem(&r0, &r1);
            let newr = Polynomial::add(&r0, &Polynomial::mul(&q, &r1).neg());
            let news = Polynomial::add(&s0, &Polynomial::mul(&q, &s1).neg());
            r0 = r1;
            s0 = s1;
            r1 = newr;
            s1 = news;
        }

        if r0.is_constant() {
            // compute inverse of leading term
            let inv = modinv(r0.leading_term(), r0.modulus).unwrap();
            // distribute over the coefficients of s0
            for coeff in s0.coeffs.iter_mut() {
                *coeff = (&*coeff * &inv) % r0.modulus;
            }
            Some(s0)
        } else {
            None
        }
    }

    /// Returns true iff this is a constant polynomial (ie. of degree $0$).
    pub fn is_constant(&self) -> bool {
        self.coeffs.len() == 1
    }

    /// Returns true iff this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.is_constant() && self.coeffs[0].is_zero()
    }

    /// Returns true iff this is the constant polynomial $1$.
    pub fn is_one(&self) -> bool {
        self.is_constant() && self.coeffs[0].is_one()
    }

    /// Returns the degree of this polynomial
    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    /// Returns the leading term of the polynomial -- the highest degree
    /// coefficient.
    pub fn leading_term(&self) -> &BigUint {
        self.coeffs.last().unwrap()
    }
}
