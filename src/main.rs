extern crate num_bigint;
extern crate num_traits;
use num_bigint::{BigInt, BigUint, ToBigInt};
use num_traits::{Num, One, Zero};
use std::mem::swap;


const P: &str = "115792089237316195423570985008687907853269984665640564039457584007908834671663";//2^256-2^32-977
//eqn y^2=x^3+7

// Define the Ecc_pt enum to represent finite points and the point at infinity
#[derive(Debug, PartialEq, Clone)]
enum EccPt {
    Infinity,
    Point {
        x: BigUint,
        y: BigUint,
    },
}

// Implement the modular inverse function using the Extended Euclidean Algorithm
fn mod_inverse(a: BigUint, m: BigUint) -> BigUint {
    let (mut t, mut new_t) = (BigInt::zero(), BigInt::from(1));
    let (mut r, mut new_r) = (m.to_bigint().unwrap(), a.to_bigint().unwrap());

    while new_r != BigInt::zero() {
        let quotient = &r / &new_r;

        t = t - &quotient * &new_t;
        swap(&mut t, &mut new_t);

        r = r - &quotient * &new_r;
        swap(&mut r, &mut new_r);
    }

    if r > BigInt::from(1) {
        panic!("a is not invertible"); // a is not invertible
    }

    if t < BigInt::zero() {
        t = t + m.to_bigint().unwrap();
    }

    t.to_biguint().unwrap()
}

// Implement methods for the EccPt enum
impl EccPt {
    // Constructor function to create a finite point
    fn new(x: BigUint, y: BigUint) -> Self {
        EccPt::Point { x, y }
    }

    // Function to create the point at infinity
    fn infinity() -> Self {
        EccPt::Infinity
    }
}

// Elliptic curve point addition using tangent-slope formula
fn tangent_sum(a: &EccPt, b: &EccPt) -> EccPt {
    match (a, b) {
        (EccPt::Point { x: ax, y: ay }, EccPt::Point { x: bx, y: by }) if ax == bx && ay == by => {
            if ay.is_zero() {
                return EccPt::infinity();
            }

            let p = BigUint::from_str_radix(P, 10).unwrap();
            let r1 = ((ax * ax * BigUint::from(3u8)) + BigUint::from(0u8)) % &p;
            let s2 = mod_inverse(ay * BigUint::from(2u8), p.clone());
            let m = (r1 * s2) % p.clone();
            let k = (m.clone() * m.clone() + (&p - BigUint::from(2u8)) * ax) % p.clone();
            let l = (((&p - &k + ax) * m) + (&p - ay)) % p;

            EccPt::Point { x: k, y: l }
        }
        _ => EccPt::infinity(),
    }
}

// Elliptic curve point addition using chord-slope formula
fn chord_sum(a: &EccPt, b: &EccPt) -> EccPt {
    match (a, b) {
        (EccPt::Infinity, point) | (point, EccPt::Infinity) => point.clone(),
        (EccPt::Point { x: ax, y: ay }, EccPt::Point { x: bx, y: by }) if ax == bx && ay == by => {
            tangent_sum(a, b)
        }
        (EccPt::Point { x: ax, y: ay }, EccPt::Point { x: bx, y: by }) if ax == bx && *ay == (BigUint::from_str_radix(P, 10).unwrap()) - by => {
            EccPt::Infinity
        }
        (EccPt::Point { x: ax, y: ay }, EccPt::Point { x: bx, y: by }) => {
            let p = BigUint::from_str_radix(P, 10).unwrap();

            let numerator = (by + (&p - ay)) % &p;
            let denominator = (bx + (&p - ax)) % &p;
            let lambda = (numerator * mod_inverse(denominator.clone(), p.clone())) % &p;

            let x3 = (&lambda * &lambda + (&p - ax) + (&p - bx + &p)) % &p;
            let y3 = (&lambda * (ax + (&p - &x3)) + (&p - ay)) % &p;

            EccPt::Point { x: x3, y: y3 }
        }
        _ => EccPt::infinity(),
    }
}

// Scalar multiplication over elliptic curve
fn scalar_mul(k: BigUint, point: &EccPt) -> EccPt {
    let mut n = k;
    let mut q = EccPt::Infinity;
    let mut p = point.clone();

    while n > BigUint::zero() {
        if &n & BigUint::one() == BigUint::one() {
            q = chord_sum(&q, &p);
        }

        p = tangent_sum(&p, &p);
        n >>= 1;
    }

    q
}
//verification whether a given set of pt exist on exist on elliptic curve
fn verify(a:&EccPt)->bool{
    match a{
        EccPt::Infinity=>true,
       ( EccPt::Point { x:m, y:n})if ((n*n)%BigUint::from_str_radix(P, 10).unwrap())==((m*m*m)+BigUint::from(7u8))%BigUint::from_str_radix(P, 10).unwrap() =>true,
        _=>false 
    }
   
}
fn main() {
    // Example of creating a finite point
    let gx = "4";
    let gy = "2";
    let gx_int = BigUint::from_str_radix(gx, 10).expect("Invalid string");
    let gy_int = BigUint::from_str_radix(gy, 10).expect("Invalid string");

    let point = EccPt::new(gx_int.clone(), gy_int.clone());
    println!("Point: {:?}", point);

    let gx1 = "4";
    let gy1 = "2";
    let gx1_int = BigUint::from_str_radix(gx1, 10).expect("Invalid string");
    let gy1_int = BigUint::from_str_radix(gy1, 10).expect("Invalid string");

    let point1 = EccPt::new(gx1_int.clone(), gy1_int.clone());
    let point2=EccPt::infinity();
    let gx3 = "0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
    let gy3 = "0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8";
   
    let gx3_int = BigUint::from_str_radix(&gx3[2..], 16).expect("Invalid hex string");
    let gy3_int = BigUint::from_str_radix(&gy3[2..], 16).expect("Invalid hex string");

    let point3 = EccPt::Point {
        x: gx3_int,
        y: gy3_int,
    };
    println!("Point: {:?}", point3);

    println!("Point: {:?}", point1);

    let chord_sum_result = chord_sum(&point3, &point3);
    println!("Chord Sum: {:?}", chord_sum_result);

    let scalar = BigUint::from(1u8); 
    let scalar_mul_result = scalar_mul(scalar, &point3);
    println!("Scalar Multiplication: {:?}", scalar_mul_result);
    let verify_result=verify(&point3);
    println!("Verify:{}",verify_result);
    let verify_result1=verify(&point1);
    println!("Verify:{}",verify_result1);
}
#[cfg(test)]
mod tests{
    use super::*;
    #[test]
    fn tangent_sum_result(){
        let p1=EccPt::infinity();
        let p2=EccPt::infinity();
        let p1_result=tangent_sum(&p1,&p1);
        assert_eq!(p2,p1_result);
    }
    #[test]
    fn chord_sum_result(){
        let p1=EccPt::infinity();
        let p2=EccPt::infinity();
        let p3=EccPt::infinity();
        let p1_p2_result=chord_sum(&p1,&p2);
        assert_eq!(p3,p1_p2_result);
    }
    #[test]
    fn scalar_mul_result(){
        let p1=EccPt::infinity();
        let p2=EccPt::infinity();
        let scalar = BigUint::from(1u8); 
        let scalar_mul_result = scalar_mul(scalar, &p1);
        assert_eq!(p2,scalar_mul_result);
    }
    #[test]
    fn verify1_result(){
        let gx = "0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
    let gy = "0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8";
   
    let gx_int = BigUint::from_str_radix(&gx[2..], 16).expect("Invalid hex string");
    let gy_int = BigUint::from_str_radix(&gy[2..], 16).expect("Invalid hex string");

    let point = EccPt::Point {
        x: gx_int,
        y: gy_int,
    };
    let verify_result1=verify(&point);
    assert_eq!(true,verify_result1);
    }
    #[test]
    fn verify2_result(){
        let gx = "2";
    let gy = "4";
   
    let gx_int = BigUint::from_str_radix(&gx[0..], 16).expect("Invalid hex string");
    let gy_int = BigUint::from_str_radix(&gy[0..], 16).expect("Invalid hex string");

    let point = EccPt::Point {
        x: gx_int,
        y: gy_int,
    };
    let verify_result2=verify(&point);
    assert_eq!(false,verify_result2);
    }
    #[test]
    fn verify3_result(){
    let point=EccPt::infinity();
    let verify_result1=verify(&point);
    assert_eq!(true,verify_result1);
    }
    
}
