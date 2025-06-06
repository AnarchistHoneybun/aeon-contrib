use super::factor;
use crate::{
    rings::natural::factorization::primes::is_prime,
    structure::{FactoredSignature, SemiRingSignature},
};
use algebraeon_nzq::{Natural, NaturalCanonicalStructure, gcd, traits::ModPow};
use algebraeon_sets::structure::*;
use itertools::Itertools;
use std::collections::HashMap;

pub trait NaturalCanonicalFactorizationStructure {
    fn factorizations(&self) -> NaturalFactorizationStructure {
        NaturalFactorizationStructure {}
    }
}
impl NaturalCanonicalFactorizationStructure for NaturalCanonicalStructure {}

#[derive(Debug, Clone)]
pub struct FactoredNatural {
    primes: HashMap<Natural, Natural>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NaturalFactorizationStructure {}

impl Signature for NaturalFactorizationStructure {}

impl SetSignature for NaturalFactorizationStructure {
    type Set = FactoredNatural;

    fn is_element(&self, x: &Self::Set) -> bool {
        for (prime, power) in self.to_powers_unchecked(x) {
            if power == &Natural::ZERO {
                return false;
            }
            if self.try_object_is_prime(prime) == Some(false) {
                return false;
            }
        }
        true
    }
}

impl FactoredSignature for NaturalFactorizationStructure {
    type PrimeObject = Natural;
    type Object = Natural;

    fn object_divides(&self, a: &Self::Object, b: &Self::Object) -> bool {
        b % a == Natural::ZERO
    }

    fn try_object_is_prime(&self, object: &Self::PrimeObject) -> Option<bool> {
        Some(is_prime(object))
    }

    fn prime_into_object(&self, prime: Self::PrimeObject) -> Self::Object {
        prime
    }

    fn object_product(&self, objects: Vec<&Self::Object>) -> Self::Object {
        Natural::structure().product(objects)
    }

    fn new_powers_unchecked(&self, factor_powers: Vec<(Natural, Natural)>) -> Self::Set {
        Self::Set {
            primes: factor_powers.into_iter().collect(),
        }
    }

    fn to_powers_unchecked<'a>(&self, a: &'a Self::Set) -> Vec<(&'a Natural, &'a Natural)> {
        a.primes.iter().collect()
    }

    fn into_powers_unchecked(&self, a: Self::Set) -> Vec<(Natural, Natural)> {
        a.primes.into_iter().collect()
    }

    fn expanded(&self, a: &Self::Set) -> Natural {
        let mut t = Natural::ONE;
        for (p, k) in &a.primes {
            t *= p.pow(k);
        }
        t
    }

    fn mul(&self, mut a: Self::Set, b: Self::Set) -> Self::Set {
        for (p, k) in self.into_powers(b) {
            *a.primes.entry(p).or_insert(Natural::ZERO) += k;
        }
        a
    }
}

impl std::fmt::Display for FactoredNatural {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.primes.is_empty() {
            write!(f, "1")?;
        } else {
            for (i, (p, k)) in self
                .primes
                .iter()
                .sorted_by_cached_key(|(p, _k)| (*p).clone())
                .enumerate()
            {
                if i != 0 {
                    write!(f, " × ")?;
                }
                write!(f, "{}", p)?;
                if k != &Natural::ONE {
                    write!(f, "^")?;
                    write!(f, "{}", k)?;
                }
            }
        }
        Ok(())
    }
}

impl FactoredNatural {
    pub fn mul_prime(&mut self, p: Natural) {
        debug_assert!(is_prime(&p));
        *self.primes.entry(p).or_insert(Natural::ZERO) += Natural::ONE;
    }

    pub fn euler_totient(&self) -> Natural {
        let mut t = Natural::ONE;
        for (p, k) in &self.primes {
            t *= (p - &Natural::ONE) * p.pow(&(k - &Natural::ONE));
        }
        t
    }

    pub fn distinct_prime_factors(&self) -> Vec<&Natural> {
        let mut primes = vec![];
        for (p, _) in &self.primes {
            primes.push(p);
        }
        primes
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IsPrimitiveRootResult {
    NonUnit,
    No,
    Yes,
}
impl FactoredNatural {
    /// Return whether x is a primitive root modulo the value represented by self
    pub fn is_primitive_root(&self, x: &Natural) -> IsPrimitiveRootResult {
        let n_factored = self;
        let n = Natural::structure().factorizations().expanded(n_factored);
        if gcd(x.clone(), n.clone()) != Natural::ONE {
            IsPrimitiveRootResult::NonUnit
        } else {
            let phi_n = n_factored.euler_totient();
            let x_mod_n = x % &n;
            for p in factor(phi_n.clone()).unwrap().distinct_prime_factors() {
                if (&x_mod_n).mod_pow(&phi_n / p, &n) == Natural::ONE {
                    return IsPrimitiveRootResult::No;
                }
            }
            IsPrimitiveRootResult::Yes
        }
    }
}
