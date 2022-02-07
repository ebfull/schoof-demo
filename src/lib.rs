//! # Schoof's algorithm
//!
//! This crate contains an implementation of [Schoof's algorithm] for computing
//! the number of points on a short Weierstrass curve $E(\mathbb{F}_p) : Y^2 =
//! X^3 + aX + b$ constructed over prime field $\mathbb{F}_p$. **This crate is
//! just for educational purposes and is not optimized.**
//!
//! [Schoof's algorithm]: https://en.wikipedia.org/wiki/Schoof's_algorithm

pub mod polynomial;
pub mod util;

use std::convert::TryFrom;

use num_bigint::{BigInt, BigUint};
use num_integer::Integer;

use polynomial::Polynomial;
use util::{modinv, num, one, primes, zero};

/// Given prime $p \geq 3$ and constants $a, b$ defining the elliptic curve
/// $E(\mathbb{F}_p) : Y^2 = X^3 + aX + b$, this function uses [Schoof's
/// algorithm](https://en.wikipedia.org/wiki/Schoof's_algorithm) to compute the
/// number of points $q = \\#E(\mathbb{F}_p)$.
///
/// This function may fail if provided a non-prime or goofy elliptic curve
/// parameters that would cause supersingular curves to emerge.
pub fn schoof(p: &BigUint, a: &BigUint, b: &BigUint) -> BigUint {
    // We only want odd primes.
    assert!(p.is_odd());
    assert!(p > &num(2));

    // Reduce a, b mod p
    let a = &(a % p);
    let b = &(b % p);

    // This is the product of all the $\ell$ values we've attempted so far.
    let mut m = one();

    // This is our currect guess of the trace of Frobenius.
    let mut t = zero();

    // Once `m` becomes large enough (within the Hasse bound interval), `t` can
    // be uniquely determined.
    let goal = num(4) * p.sqrt();

    let mut primes = primes();
    while m < goal {
        // Some small prime
        let l = primes.next().unwrap();

        // Compute t (the trace of Frobenius) modulo `l`
        let t_mod_l = compute_t_mod_l(p, a, b, l);

        let l = &num(l as u32);

        // Better approximate `t` given the newest result. This is basically an
        // incremental version of the Chinese Remainder theorem.
        t = (modinv(&m, &l).unwrap() * &m * t_mod_l + modinv(&l, &m).unwrap() * l * t) % (&m * l);
        m = m * l;
    }

    // The actual trace may be negative.
    let t = if t > m.clone() / num(2) {
        let t = BigInt::from(t);
        t - BigInt::from(m)
    } else {
        BigInt::from(t)
    };

    BigUint::try_from(BigInt::from(p + one()) - t).unwrap()
}

/// Represents (a(x), b(x)y)
#[derive(Clone, Debug, PartialEq, Eq)]
struct Endo<'a> {
    a: Polynomial<'a>,
    b: Polynomial<'a>,
}

fn addendo<'a>(
    u: &Endo<'a>,
    v: &Endo<'a>,
    h: &Polynomial<'a>,
    fx: &Polynomial<'a>,
    a: &BigUint,
) -> Result<Option<Endo<'a>>, Polynomial<'a>> {
    let r = if u.a != v.a {
        let d = Polynomial::add(&u.a, &v.a.neg());
        if let Some(d) = d.inverse(&h) {
            let n = Polynomial::add(&u.b, &v.b.neg());
            Polynomial::divrem(&Polynomial::mul(&n, &d), h).1
        } else {
            // Oh my! Not invertible mod h. This means h and d have
            // common factors. Start over using the common factor
            // instead.
            return Err(Polynomial::gcd(&d, h));
        }
    } else {
        if u.b != v.b {
            return Ok(None);
        }
        // Same x-coordinates, same y-coordinates; doubling case
        let d = Polynomial::mul(&u.b, fx);
        let d = Polynomial::add(&d, &d);
        let d = Polynomial::divrem(&d, &h).1;
        if let Some(d) = d.inverse(&h) {
            let n = Polynomial::mul(&u.a, &u.a);
            let n2 = Polynomial::add(&n, &n);
            let n = Polynomial::add(&n, &n2);
            let modulus = n.modulus;
            let n = Polynomial::add(&n, &Polynomial::new(modulus, &[a.clone()]));
            Polynomial::divrem(&Polynomial::mul(&n, &d), h).1
        } else {
            // Same as before.
            return Err(Polynomial::gcd(&d, h));
        }
    };

    let a = Polynomial::divrem(&Polynomial::mul(&r, &r), h).1;
    let a = Polynomial::divrem(&Polynomial::mul(&a, fx), h).1;
    let a = Polynomial::add(&a, &u.a.neg());
    let a = Polynomial::add(&a, &v.a.neg());
    let a = Polynomial::divrem(&a, h).1;

    let b = Polynomial::add(&u.a.clone(), &a.neg());
    let b = Polynomial::mul(&b, &r);
    let b = Polynomial::add(&b, &u.b.neg());
    let b = Polynomial::divrem(&b, h).1;

    Ok(Some(Endo { a, b }))
}

/// Computes the trace of Frobenius modulo $l$ for the curve $E(\mathbb{F}_p) :
/// Y^2 = X^3 + aX + b$.
fn compute_t_mod_l(p: &BigUint, a: &BigUint, b: &BigUint, l: usize) -> BigUint {
    if l == 2 {
        compute_t_mod_2(p, a, b)
    } else {
        // f(X) = X^3 + aX + b
        let fx = Polynomial::new(p, &[b.clone(), a.clone(), num(0), num(1)]);

        // lth division polynomial modulo f(X)
        let mut h = division_poly(p, l, a, b);

        'newh: loop {
            // Multiplicative identity
            let id = Endo {
                a: Polynomial::new(p, &[zero(), one()]),
                b: Polynomial::new(p, &[one()]),
            };

            // Frobenius endomorphism
            // (X^p mod h, Y^p mod h)
            // = (X^p mod h, (f(X)^{(p - 1) / 2} mod h) Y)
            let frob = Endo {
                a: {
                    let x = Polynomial::new(p, &[zero(), one()]);
                    // exponentiate X by p (mod h)
                    let mut xacc = Polynomial::new(p, &[one()]);
                    for bit in p
                        .to_bytes_le()
                        .into_iter()
                        .rev()
                        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1) == 1))
                    {
                        xacc = Polynomial::mul(&xacc, &xacc); // square
                        xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        if bit {
                            xacc = Polynomial::mul(&xacc, &x); // multiply
                            xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        }
                    }

                    xacc
                },
                b: {
                    // exponentiate f(X) by (p - 1) / 2 (mod h)
                    let mut xacc = Polynomial::new(p, &[one()]);
                    let exponent: BigUint = (p - &one()) >> 1;
                    for bit in exponent
                        .to_bytes_le()
                        .into_iter()
                        .rev()
                        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1) == 1))
                    {
                        xacc = Polynomial::mul(&xacc, &xacc); // square
                        xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        if bit {
                            xacc = Polynomial::mul(&xacc, &fx); // multiply
                            xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        }
                    }

                    xacc
                },
            };

            // Frobenius endomorphism
            // (X^p mod h, Y^p mod h)
            // = (X^(p^2) mod h, (f(X)^{(p^2 - 1) / 2} mod h) Y)
            let frob2 = Endo {
                a: {
                    let x = Polynomial::new(p, &[zero(), one()]);
                    // exponentiate X by the p squared (mod h)
                    let mut xacc = Polynomial::new(p, &[one()]);
                    let modulus_squared = p * p;
                    for bit in modulus_squared
                        .to_bytes_le()
                        .into_iter()
                        .rev()
                        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1) == 1))
                    {
                        xacc = Polynomial::mul(&xacc, &xacc); // square
                        xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        if bit {
                            xacc = Polynomial::mul(&xacc, &x); // multiply
                            xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        }
                    }

                    xacc
                },
                b: {
                    // exponentiate f(X) by (p^2 - 1) / 2 (mod h)
                    let mut xacc = Polynomial::new(p, &[one()]);
                    let exponent: BigUint = ((p * p) - &one()) >> 1;
                    for bit in exponent
                        .to_bytes_le()
                        .into_iter()
                        .rev()
                        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1) == 1))
                    {
                        xacc = Polynomial::mul(&xacc, &xacc); // square
                        xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        if bit {
                            xacc = Polynomial::mul(&xacc, &fx); // multiply
                            xacc = Polynomial::divrem(&xacc, &h).1; // reduce
                        }
                    }

                    xacc
                },
            };

            // Compute rhs = [p (mod l)]
            let mut rhs = None;
            for bit in (p % num(l as u32))
                .to_bytes_le()
                .into_iter()
                .rev()
                .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1) == 1))
            {
                // double
                rhs = match rhs {
                    Some(rhs) => match addendo(&rhs, &rhs, &h, &fx, a) {
                        Err(g) => {
                            assert!(!g.is_one());
                            h = g;
                            continue 'newh;
                        }
                        Ok(res) => res,
                    },
                    None => None,
                };
                if bit {
                    // add
                    rhs = match rhs {
                        Some(rhs) => match addendo(&rhs, &id, &h, &fx, a) {
                            Err(g) => {
                                assert!(!g.is_one());
                                h = g;
                                continue 'newh;
                            }
                            Ok(res) => res,
                        },
                        None => Some(id.clone()),
                    };
                }
            }

            // Compute rhs = [q] + frob2
            rhs = match rhs {
                Some(rhs) => match addendo(&rhs, &frob2, &h, &fx, a) {
                    Err(g) => {
                        assert!(!g.is_one());
                        h = g;
                        continue 'newh;
                    }
                    Ok(res) => res,
                },
                None => Some(frob2),
            };

            if rhs.is_none() {
                // t (mod l) = 0
                return num(0);
            } else {
                // Find value of t < l such that [t] frob = rhs = [q] + frob2
                let rhs = rhs.unwrap();
                let mut lhs = frob.clone();
                let mut c = one();
                while lhs != rhs {
                    lhs = match addendo(&lhs, &frob, &h, &fx, a) {
                        Err(g) => {
                            assert!(!g.is_one());
                            h = g;
                            continue 'newh;
                        }
                        Ok(Some(res)) => res,
                        Ok(None) => panic!("that shouldn't happen.."),
                    };
                    c = c + one();
                }

                return c;
            }
        }
    }
}

/// Computes the trace of Frobenius modulo $2$ for the curve $E(\mathbb{F}_p) :
/// Y^2 = X^3 + aX + b$.
///
/// Given that $p$ is odd, $t = p + 1 - \\#E(\mathbb{F}_p)$ is divisible by $2$
/// if and only if $E(\mathbb{F}_p)$ has a point of order $2$, which would imply
/// a point $(x, 0)$ exists (all $2$-order points have $y = 0$) which means that
/// such a point exists if and only if $X^3 + aX + b$ has a root in
/// $\mathbb{F}_p$.
///
/// We can establish whether or not a root exists by finding $g(X) = \text{gcd}(X^p - X, X^3 + aX + b)$.
/// If $g$ has degree larger than $0$, then $X^3 + aX + b$ has a root. Otherwise, it does not.
///
/// Computing $\text{gcd}(X^p - X, X^3 + aX + b)$ would be difficult ordinarily
/// due to the degree of $X^p - X$, so instead we compute $X^p$ in the quotient
/// ring $\mathbb{F}_p[X]/(X^3 + aX + b)$. Then, we subtract $X$ and compute the GCD with
/// $X^3 + aX + b$.
fn compute_t_mod_2(p: &BigUint, a: &BigUint, b: &BigUint) -> BigUint {
    // X^3 + aX + b
    let fx = Polynomial::new(p, &[b.clone(), a.clone(), zero(), one()]);
    // X
    let x = Polynomial::new(p, &[zero(), one()]);

    // Exponentiate X by p modulo X^3 + AX + B
    let mut acc = Polynomial::new(p, &[one()]);
    for bit in p
        .to_bytes_le()
        .into_iter()
        .rev()
        .flat_map(|byte| (0..8).rev().map(move |i| ((byte >> i) & 1) == 1))
    {
        acc = Polynomial::mul(&acc, &acc); // square
        acc = Polynomial::divrem(&acc, &fx).1; // reduce
        if bit {
            acc = Polynomial::mul(&acc, &x); // multiply
            acc = Polynomial::divrem(&acc, &fx).1; // reduce
        }
    }

    // Subtract X
    acc = Polynomial::add(&acc, &x.neg());
    // Compute GCD
    acc = Polynomial::gcd(&acc, &fx);

    if acc.degree() > 0 {
        num(0)
    } else {
        num(1)
    }
}

/// Returns the `l`th division polynomial for odd `l`.
fn division_poly<'a>(p: &'a BigUint, l: usize, a: &BigUint, b: &BigUint) -> Polynomial<'a> {
    assert_eq!(l % 2, 1);
    assert!(l > 2);

    let f = Polynomial::new(p, &[b.clone(), a.clone(), num(0), num(1)]);
    let twoinv = &modinv(&num(2), p).unwrap();

    use std::collections::{BTreeMap, BTreeSet};

    fn populate_map(map: &mut BTreeSet<usize>, l: usize) {
        map.insert(l);
        if l > 4 {
            if l % 2 == 1 {
                // We're in the "odd" l = 2m + 1 case
                let m = (l - 1) >> 1;
                populate_map(map, m + 2);
                populate_map(map, m);
                populate_map(map, m - 1);
                populate_map(map, m + 1);
            } else {
                // We're in the "even" l = 2m case
                let m = l >> 1;
                populate_map(map, m);
                populate_map(map, m + 2);
                populate_map(map, m - 1);
                populate_map(map, m - 2);
                populate_map(map, m + 1);
            }
        }
    }

    let mut map: BTreeSet<usize> = BTreeSet::new();
    populate_map(&mut map, l);

    let mut polys: BTreeMap<usize, (Polynomial<'_>, usize)> = BTreeMap::new();

    for entry in map {
        polys.insert(
            entry,
            match entry {
                // \psi_0 = 0
                0 => (Polynomial::new(p, &[zero()]), 0),
                // \psi_1 = 1
                1 => (Polynomial::new(p, &[one()]), 0),
                // \psi_2 = 2Y
                2 => (Polynomial::new(p, &[num(2)]), 1),
                // \psi_3 = 3X^4 + 6aX^2 + 12bX - a^2
                3 => (
                    Polynomial::new(
                        p,
                        &[
                            (p - ((a * a) % p)),
                            (num(12) * b),
                            (num(6) * a),
                            num(0),
                            num(3),
                        ],
                    ),
                    0,
                ),
                // \psi_4 = 4Y(X^6 + 5aX^4 + 20bX^3 - 5a^2X^2 - 4abX - 8b^2 - a^3)
                4 => (
                    Polynomial::new(
                        p,
                        &[
                            (p - (((a * a * a) + num(8) * (b * b)) % p)) * num(4),
                            p - ((num(4) * a * b * num(4)) % p),
                            p - ((num(5) * a * a * num(4)) % p),
                            num(20) * b * num(4),
                            num(5) * a * num(4),
                            num(0),
                            one() * num(4),
                        ],
                    ),
                    1,
                ),
                entry => {
                    if (entry % 2) == 1 {
                        // We're in the "odd" l = 2m + 1 case
                        let m = (entry - 1) >> 1;

                        let psi_m_plus_2 = polys.get(&(m + 2)).unwrap();
                        let psi_m = polys.get(&(m)).unwrap();
                        let psi_m_minus_1 = polys.get(&(m - 1)).unwrap();
                        let psi_m_plus_1 = polys.get(&(m + 1)).unwrap();

                        // \psi_{m + 2} * \psi_{m}^3
                        let mut left_y_power = psi_m_plus_2.1 + 3 * psi_m.1;
                        let left = Polynomial::mul(&psi_m_plus_2.0, &psi_m.0);
                        let left = Polynomial::mul(&left, &psi_m.0);
                        let mut left = Polynomial::mul(&left, &psi_m.0);
                        while left_y_power > 1 {
                            // replace Y^2 with X^3 + aX + b to keep the
                            // polynomial at most linear in Y
                            left = Polynomial::mul(&left, &f);
                            left_y_power -= 2;
                        }

                        // \psi_{m - 1} * \psi_{m + 1}^3
                        let mut right_y_power = psi_m_minus_1.1 + 3 * psi_m_plus_1.1;
                        let right = Polynomial::mul(&psi_m_minus_1.0, &psi_m_plus_1.0);
                        let right = Polynomial::mul(&right, &psi_m_plus_1.0);
                        let mut right = Polynomial::mul(&right, &psi_m_plus_1.0);
                        while right_y_power > 1 {
                            // replace Y^2 with X^3 + aX + b to keep the
                            // polynomial at most linear in Y
                            right = Polynomial::mul(&right, &f);
                            right_y_power -= 2;
                        }

                        let mut result = Polynomial::add(&left, &right.neg());

                        // Factor out the Y factor, if it exists
                        assert_eq!(left_y_power, right_y_power);
                        let mut result_y_power = left_y_power;
                        while result_y_power > 1 {
                            // replace Y^2 with X^3 + aX + b to keep the
                            // polynomial at most linear in Y
                            result = Polynomial::mul(&result, &f);
                            result_y_power -= 2;
                        }

                        // Y vanishes from odd division polynomials
                        assert_eq!(result_y_power, 0);

                        (result, 0)
                    } else {
                        // We're in the "even" l = 2m case
                        let m = entry >> 1;

                        let psi_m = polys.get(&(m)).unwrap();
                        let psi_m_plus_2 = polys.get(&(m + 2)).unwrap();
                        let psi_m_minus_1 = polys.get(&(m - 1)).unwrap();
                        let psi_m_minus_2 = polys.get(&(m - 2)).unwrap();
                        let psi_m_plus_1 = polys.get(&(m + 1)).unwrap();

                        // \psi_{m + 2} * \psi_{m - 1}^2
                        let left_y_power = psi_m_plus_2.1 + 2 * psi_m_minus_1.1;
                        let left = Polynomial::mul(&psi_m_plus_2.0, &psi_m_minus_1.0);
                        let left = Polynomial::mul(&left, &psi_m_minus_1.0);

                        // \psi_{m - 2} * \psi_{m + 1}^2
                        let right_y_power = psi_m_minus_2.1 + 2 * psi_m_plus_1.1;
                        let right = Polynomial::mul(&psi_m_minus_2.0, &psi_m_plus_1.0);
                        let right = Polynomial::mul(&right, &psi_m_plus_1.0);

                        let mut result = Polynomial::add(&left, &right.neg());
                        drop(right);
                        // multiply by \psi_m
                        result = Polynomial::mul(&result, &psi_m.0);

                        assert_eq!(left_y_power, right_y_power);
                        let mut result_y_power = left_y_power + psi_m.1;

                        // Divide by 2Y
                        result_y_power -= 1;
                        for coeff in result.coeffs.iter_mut() {
                            *coeff = (&*coeff * twoinv) % p;
                        }
                        while result_y_power > 1 {
                            // replace Y^2 with X^3 + aX + b to keep the
                            // polynomial at most linear in Y
                            result = Polynomial::mul(&result, &f);
                            result_y_power -= 2;
                        }

                        assert_eq!(result_y_power, 1);

                        (result, result_y_power)
                    }
                }
            },
        );
    }

    polys.get(&l).unwrap().0.clone()
}

#[test]
fn test_compute_t_mod_2() {
    // Cases where there is a point of order 2
    assert_eq!(num(0), compute_t_mod_2(&num(191), &num(3), &num(9)));
    assert_eq!(num(0), compute_t_mod_2(&num(191), &num(3), &num(4)));
    assert_eq!(num(0), compute_t_mod_2(&num(191), &num(4), &num(4)));
    assert_eq!(num(0), compute_t_mod_2(&num(191), &num(2), &num(4)));
    assert_eq!(num(0), compute_t_mod_2(&num(191), &num(77), &num(1)));
    assert_eq!(num(0), compute_t_mod_2(&num(191), &num(79), &num(44)));

    // Cases where there is not a point of order 2
    assert_eq!(num(1), compute_t_mod_2(&num(191), &num(50), &num(10)));
    assert_eq!(num(1), compute_t_mod_2(&num(191), &num(92), &num(13)));
    assert_eq!(num(1), compute_t_mod_2(&num(191), &num(52), &num(99)));
    assert_eq!(num(1), compute_t_mod_2(&num(191), &num(27), &num(13)));
    assert_eq!(num(1), compute_t_mod_2(&num(191), &num(40), &num(46)));
    assert_eq!(num(1), compute_t_mod_2(&num(191), &num(180), &num(101)));
}

#[test]
fn test_division_polys() {
    let modulus = &BigUint::parse_bytes(
        b"40000000000000000000000000000000224698fc094cf91b992d30ed00000001",
        16,
    )
    .unwrap();
    let h = division_poly(modulus, 23, &num(599), &num(48));

    let roots = &[
        b"07880299896585187991636936802988827900157647004570637481343212533327149177376",
        b"25996367144729762015008052750121272433522355746668130243652725074929457995049",
        b"09773023107064905444398760106771465407920734241800898184312366832174088179389",
        b"11114995163399886746917747499793356201309249194425905117339875882470398214636",
        b"07019296339302623333694541253885837809319897818728630555900319187308885058310",
        b"09082241838164682015389552077097162298466974050043031218684190541228242227630",
        b"08632065024039024859740282588359834075582786582619275047218928878909492177390",
        b"10586452452564956615774385591718854013343033937630468159554544763437219916322",
        b"20514584287719675954929483152461009884577612156694358734405214469653517364268",
        b"07500153404017903557522817984446025147369697293701801273636287069799521715134",
        b"23896435016339869751471519976269806611473967444404286432948643716015847169964",
    ];

    for root in roots {
        assert_eq!(
            zero(),
            Polynomial::eval(&h, &BigUint::parse_bytes(&root[..], 10).unwrap())
        )
    }
}

#[test]
fn test_compute_t_mod_3() {
    assert_eq!(num(1), compute_t_mod_l(&num(191), &num(11), &num(49), 3));
    assert_eq!(num(0), compute_t_mod_l(&num(191), &num(11), &num(50), 3));
    assert_eq!(num(0), compute_t_mod_l(&num(191), &num(12), &num(50), 3));
    assert_eq!(num(0), compute_t_mod_l(&num(191), &num(50), &num(50), 3));
    assert_eq!(num(2), compute_t_mod_l(&num(191), &num(107), &num(59), 3));
    assert_eq!(num(1), compute_t_mod_l(&num(191), &num(104), &num(52), 3));
    assert_eq!(num(0), compute_t_mod_l(&num(191), &num(103), &num(53), 3));
}

#[test]
fn test_compute_t_mod_5() {
    assert_eq!(num(0), compute_t_mod_l(&num(191), &num(106), &num(158), 5));
    assert_eq!(num(3), compute_t_mod_l(&num(191), &num(69), &num(78), 5));
    assert_eq!(num(1), compute_t_mod_l(&num(191), &num(42), &num(167), 5));
    assert_eq!(num(0), compute_t_mod_l(&num(191), &num(6), &num(60), 5));
    assert_eq!(num(2), compute_t_mod_l(&num(191), &num(23), &num(171), 5));
}

#[test]
fn test_compute_t_mod_11() {
    assert_eq!(num(10), compute_t_mod_l(&num(191), &num(186), &num(20), 11));
}

#[test]
fn test_schoof() {
    assert_eq!(num(204), schoof(&num(191), &num(186), &num(20)));
    assert_eq!(num(65614), schoof(&num(65519), &num(14368), &num(6420)));
    assert_eq!(
        num(138161621),
        schoof(&num(138172777), &num(135939349), &num(38820686))
    );
}
