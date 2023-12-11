use crate::field::LurkField;
use bellpepper::gadgets::multipack::pack_bits;
use bellpepper::gadgets::sha3::sha3;
use bellpepper_core::boolean::Boolean;
use bellpepper_core::{ConstraintSystem, SynthesisError};
use lurk_macros::Coproc;
use serde::{Deserialize, Serialize};
use sha3::Sha3_256;
use std::marker::PhantomData;

use crate::circuit::gadgets::pointer::AllocatedPtr;
use crate::coprocessor::{CoCircuit, Coprocessor};
use crate::lem::circuit::GlobalAllocator;
use crate::lem::pointers::Ptr;
use crate::lem::store::Store;
use crate::tag::{ExprTag, Tag};
use crate::z_ptr::ZPtr;
use crate::{self as lurk};

/// `Sha3Coprocessor` is a structure that represents a sha3 [`crate::coprocessor::Coprocessor`] to
/// be later bind to our [`crate::eval::lang::Lang`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Sha3Coprocessor<F: LurkField> {
    n: usize,
    pub(crate) _p: PhantomData<F>,
}

impl<F: LurkField> Sha3Coprocessor<F> {
    pub fn new(n: usize) -> Self {
        Self {
            n,
            _p: Default::default(),
        }
    }
}

impl<F: LurkField> CoCircuit<F> for Sha3Coprocessor<F> {
    fn arity(&self) -> usize {
        self.n
    }

    fn synthesize_simple<CS: ConstraintSystem<F>>(
        &self,
        cs: &mut CS,
        _g: &GlobalAllocator<F>,
        _s: &Store<F>,
        _not_dummy: &Boolean,
        args: &[AllocatedPtr<F>],
    ) -> Result<AllocatedPtr<F>, SynthesisError> {
        let zero = Boolean::constant(false);

        let mut bits = vec![];

        for arg in args {
            let tag_bits = arg
                .tag()
                .to_bits_le_strict(&mut cs.namespace(|| "preimage_tag_bits"))?;
            let hash_bits = arg
                .hash()
                .to_bits_le_strict(&mut cs.namespace(|| "preimage_hash_bits"))?;

            bits.extend(tag_bits);
            bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
            bits.extend(hash_bits);
            bits.push(zero.clone()); // need 256 bits (or some multiple of 8).
        }

        bits.reverse();

        // TODO implement
        let mut digest_bits = sha3(cs.namespace(|| "digest_bits"), &bits)?;

        digest_bits.reverse();

        // Fine to lose the last <1 bit of precision.
        let digest_scalar = pack_bits(cs.namespace(|| "digest_scalar"), &digest_bits)?;
        AllocatedPtr::alloc_tag(
            &mut cs.namespace(|| "output_expr"),
            ExprTag::Num.to_field(),
            digest_scalar,
        )
    }
}

impl<F: LurkField> Coprocessor<F> for Sha3Coprocessor<F> {
    fn eval_arity(&self) -> usize {
        self.n
    }

    fn has_circuit(&self) -> bool {
        true
    }

    fn evaluate_simple(&self, s: &Store<F>, args: &[Ptr]) -> Ptr {
        let z_ptrs = args.iter().map(|ptr| s.hash_ptr(ptr)).collect::<Vec<_>>();
        s.num(compute(self.n, &z_ptrs))
    }
}

fn compute<F: LurkField, T: Tag>(n: usize, z_ptrs: &[ZPtr<T, F>]) -> F {
    let mut hasher = Sha3_256::new();

    let mut input = vec![0u8; 64 * n];

    for (i, z_ptr) in z_ptrs.iter().enumerate() {
        let tag_zptr: F = z_ptr.tag().to_field();
        let hash_zptr = z_ptr.value();
        input[(64 * i)..(64 * i + 32)].copy_from_slice(&tag_zptr.to_bytes());
        input[(64 * i + 32)..(64 * (i + 1))].copy_from_slice(&hash_zptr.to_bytes());
    }

    input.reverse();

    hasher.update(input);
    let mut bytes = hasher.finalize();
    bytes.reverse();
    let l = bytes.len();
    // Discard the two most significant bits.
    bytes[l - 1] &= 0b00111111;

    F::from_bytes(&bytes).unwrap()
}

/// `Sha3Coproc` is an enum that can be used to instantiate a [`crate::eval::lang::Lang`] that has
/// only one [`crate::coprocessor::Coprocessor`], [`crate::coprocessor::sha3::Sha3Coprocessor`].
#[derive(Clone, Debug, Coproc, Serialize, Deserialize)]
pub enum Sha3Coproc<F: LurkField> {
    SC(Sha3Coprocessor<F>),
}
