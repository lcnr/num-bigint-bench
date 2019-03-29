extern crate criterion;
use criterion::*;

#[macro_use]
extern crate lazy_static;
extern crate num_bigint;
extern crate num_traits;
extern crate rand_xorshift;
extern crate rand;

use std::ops::{
    Add, AddAssign, Sub, SubAssign, Rem, RemAssign, Div, DivAssign, Mul, MulAssign, 
    /*, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Shl, ShlAssign, Shr, ShrAssign, */
};

use num_bigint::{BigUint, RandBigInt};
use rand_xorshift::XorShiftRng;
//use rand_core::{ };
use rand::{Rng, SeedableRng};

use num_traits::{One, Zero};

lazy_static! {
    /// fits inside of one BigDigit
    static ref BIGUINT_TINY: Vec<BigUint> = {
        let rng = &mut XorShiftRng::seed_from_u64(0);
        (0..100).map(|_| rng.gen::<u32>().into()).collect()
    };

    static ref BIGUINT_SMALL: Vec<BigUint> = {
        let rng = &mut XorShiftRng::seed_from_u64(1);
        let lower_limit = BigUint::one() << 32;
        let upper_limit = BigUint::one() << 100;
        (0..100).map(|_| rng.gen_biguint_range(&lower_limit, &upper_limit)).collect()
    };

    static ref BIGUINT_MEDIUM: Vec<BigUint> = {
        let rng = &mut XorShiftRng::seed_from_u64(2);
        let lower_limit = BigUint::one() << 100;
        let upper_limit = BigUint::one() << 1000;
        (0..100).map(|_| rng.gen_biguint_range(&lower_limit, &upper_limit)).collect()
    };

    static ref BIGUINT_LARGE: Vec<BigUint> = {
        let rng = &mut XorShiftRng::seed_from_u64(3);
        let lower_limit = BigUint::one() << 1000;
        let upper_limit = BigUint::one() << 10000;
        (0..100).map(|_| rng.gen_biguint_range(&lower_limit, &upper_limit)).collect()
    };

    static ref BIGUINT_ENORMOUS: Vec<BigUint> = {
        let rng = &mut XorShiftRng::seed_from_u64(4);
        let lower_limit = BigUint::one() << 10000;
        let upper_limit = BigUint::one() << 100000;
        (0..100).map(|_| rng.gen_biguint_range(&lower_limit, &upper_limit)).collect()
    };

    static ref U8: Vec<u8> = {
        let rng = &mut XorShiftRng::seed_from_u64(5);
        (0..100).map(|_| loop {
            let v = rng.gen();
            if v != 0 {
                break v;
            }
        }).collect()
    };

    static ref U16: Vec<u16> = {
        let rng = &mut XorShiftRng::seed_from_u64(6);
        (0..100).map(|_| loop {
            let v = rng.gen();
            if v != 0 {
                break v;
            }
        }).collect()
    };

    static ref U32: Vec<u32> = {
        let rng = &mut XorShiftRng::seed_from_u64(7);
        (0..100).map(|_| loop {
            let v = rng.gen();
            if v != 0 {
                break v;
            }
        }).collect()
    };

    static ref U64: Vec<u64> = {
        let rng = &mut XorShiftRng::seed_from_u64(8);
        (0..100).map(|_| loop {
            let v = rng.gen();
            if v != 0 {
                break v;
            }
        }).collect()
    };

    static ref U128: Vec<u128> = {
        let rng = &mut XorShiftRng::seed_from_u64(9);
        (0..100).map(|_| loop {
            let v = rng.gen();
            if v != 0 {
                break v;
            }
        }).collect()
    };
}



fn criterion_benchmark(c: &mut Criterion) {
    /// benches the following 4 versions of `binop`
    /// 
    /// - binop(a, b)
    /// - binop(&a, b)
    /// - binop(a, &b)
    /// - binop(&a, &b)
    macro_rules! bench_binop {
        ($binop:path, $lhs:expr, $rhs:expr) => {
            bench_binop!($binop, $lhs, $rhs, a, b, true);
        };
        ($binop:path, $lhs:expr, $rhs:expr, $a:ident, $b:ident, $check:expr) => {
            // prevent empty benchmarks from running/causing a panic in bench_function
            if $lhs.iter().zip($rhs.iter()).any(|($a, $b)| {
                // suppress unused variable warning without setting `allow(unused_variables)` for the whole functions
                let _ = (&$a, &$b);
                $check
            }) {
                c.bench_function(&format!("{}({}, {})", stringify!($binop), stringify!($lhs), stringify!($rhs)), |bencher| {
                    ($lhs.iter().zip($rhs.iter())).for_each(|($a, $b)| {
                        if $check {
                            bencher.iter_batched(|| ($a.clone(), $b.clone()), |(a, b)| {
                                $binop(a, b)
                            }, BatchSize::SmallInput);
                        }
                    })
                });

                c.bench_function(&format!("{}(&{}, {})", stringify!($binop), stringify!($lhs), stringify!($rhs)), |bencher| {
                    ($lhs.iter().zip($rhs.iter())).for_each(|($a, $b)| {
                        if $check {
                            bencher.iter_batched(|| ($a, $b.clone()), |(a, b)| {
                                $binop(a, b)
                            }, BatchSize::SmallInput);
                        }
                    })
                });

                c.bench_function(&format!("{}({}, &{})", stringify!($binop), stringify!($lhs), stringify!($rhs)), |bencher| {
                    ($lhs.iter().zip($rhs.iter())).for_each(|($a, $b)| {
                        if $check {
                            bencher.iter_batched(|| ($a.clone(), $b), |(a, b)| {
                                $binop(a, b)
                            }, BatchSize::SmallInput);
                        }
                    })
                });

                c.bench_function(&format!("{}(&{}, &{})", stringify!($binop), stringify!($lhs), stringify!($rhs)), |bencher| {
                    ($lhs.iter().zip($rhs.iter())).for_each(|($a, $b)| {
                        if $check {
                            bencher.iter_batched(|| ($a, $b), |(a, b)| {
                                $binop(a, b)
                            }, BatchSize::SmallInput);
                        }
                    })
                });
            }
        }
    }

    macro_rules! bench_binop_assign {
        ($binop:path, $lhs:expr, $rhs:expr) => {
            bench_binop_assign!($binop, $lhs, $rhs, a, b, true);
        };
        ($binop:path, $lhs:expr, $rhs:expr, $a:ident, $b:ident, $check:expr) => {
            // prevent empty benchmarks from running/causing a panic in bench_function
            if $lhs.iter().zip($rhs.iter()).any(|($a, $b)| {
                // suppress unused variable warning without setting `allow(unused_variables)` for the whole functions
                let _ = (&$a, &$b);
                $check
            }) {
                c.bench_function(&format!("{}(&mut {}, {})", stringify!($binop), stringify!($lhs), stringify!($rhs)), |bencher| {
                    ($lhs.iter().zip($rhs.iter())).for_each(|($a, $b)| {
                        if $check {
                            bencher.iter_batched(|| ($a.clone(), $b.clone()), |(mut a, b)| {
                                $binop(&mut a, b)
                            }, BatchSize::SmallInput);
                        }
                    })
                });
                
                // TODO: remove if BinopAssign<&X> does not get added or uncomment in case it does
                // bench_binop!($binop, &mut $lhs, &$rhs);
            }
        }
    }

    /// bench `Add`, `AddAssign`, `Sub`, `SubAssign`, `Mul`, `MulAssign`, `Div`, `DivAssign`, `Rem`, `RemAssign`
    macro_rules! bench_all_binop {
        ($lhs:expr, $rhs:expr) => {
            bench_binop!(Add::add, $lhs, $rhs);
            bench_binop_assign!(AddAssign::add_assign, $lhs, $rhs);

            bench_binop!(Sub::sub, $lhs, $rhs, a, b, a >= &(*b).into());
            bench_binop_assign!(SubAssign::sub_assign, $lhs, $rhs, a, b, a >= &(*b).into());

            bench_binop!(Mul::mul, $lhs, $rhs);
            bench_binop_assign!(MulAssign::mul_assign, $lhs, $rhs);

            bench_binop!(Div::div, $lhs, $rhs, a, b, !b.is_zero());
            bench_binop_assign!(DivAssign::div_assign, $lhs, $rhs);

            bench_binop!(Rem::rem, $lhs, $rhs);
            bench_binop_assign!(RemAssign::rem_assign, $lhs, $rhs);
        }
    }
    /* bench_all_binop!(BIGUINT_TINY, U8);
    bench_all_binop!(BIGUINT_SMALL, U8);
    bench_all_binop!(BIGUINT_MEDIUM, U8);
    bench_all_binop!(BIGUINT_LARGE, U8);
    bench_all_binop!(BIGUINT_ENORMOUS, U8);

    bench_all_binop!(BIGUINT_TINY, U16);
    bench_all_binop!(BIGUINT_SMALL, U16);
    bench_all_binop!(BIGUINT_MEDIUM, U16);
    bench_all_binop!(BIGUINT_LARGE, U16);
    bench_all_binop!(BIGUINT_ENORMOUS, U16);

    bench_all_binop!(BIGUINT_TINY, U32);
    bench_all_binop!(BIGUINT_SMALL, U32);
    bench_all_binop!(BIGUINT_MEDIUM, U32);
    bench_all_binop!(BIGUINT_LARGE, U32);
    bench_all_binop!(BIGUINT_ENORMOUS, U32);

    bench_all_binop!(BIGUINT_TINY, U64);
    bench_all_binop!(BIGUINT_SMALL, U64);
    bench_all_binop!(BIGUINT_MEDIUM, U64);
    bench_all_binop!(BIGUINT_LARGE, U64);
    bench_all_binop!(BIGUINT_ENORMOUS, U64);*/

    bench_all_binop!(BIGUINT_TINY, U128);
    bench_all_binop!(BIGUINT_SMALL, U128);
    bench_all_binop!(BIGUINT_MEDIUM, U128);
    bench_all_binop!(BIGUINT_LARGE, U128);
    bench_all_binop!(BIGUINT_ENORMOUS, U128);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
