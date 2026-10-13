//! Bit-blasting: compile integer contract semantics into BDD circuits.
//!
//! While the exhaustive engine speaks i64 and walks the input domain one
//! vector at a time, this module speaks *boolean circuits* and reasons about
//! all inputs at once. The two engines share only `eval.rs` as their
//! specification — they share no code — so agreement between them is
//! genuine cross-validation, not a tautology.
//!
//! ## Semantics mirrored from `eval.rs`
//!
//! Every compiled node carries a `fault` signal alongside its value bits:
//!
//! * `fault(x)` = "evaluating x diverges from the evaluator's happy path"
//!   (division by zero — the only fault representable in this subset).
//! * `ite` is lazy: the untaken branch's fault must not leak
//!   (`fault = fc ∨ (c ∧ ft) ∨ (¬c ∧ fe)`), mirroring the evaluator.
//! * `&&`/`||` short-circuit: `fault(a ∧ b) = fault(a) ∨ (val(a) ∧ fault(b))`.
//!
//! Bad state (what we prove *unsatisfiable*):
//!
//! ```text
//! bad = domain_ok ∧ pre_ok ∧ (fault ∨ ¬ensures ∨ out_of_declared_range)
//! ```
//!
//! ## Supported fragment
//!
//! `+ - * / %`, comparisons, boolean logic, `if`, `min`, `max`.
//! Division/modulo circuits are deliberately deferred (see ROADMAP): when a
//! spec contains them, the bitblaster **declines** rather than guessing —
//! the prover then falls back to the exhaustive or statistical engine. A
//! declined engine is never a false proof.

use crate::ast::*;
use crate::bdd::{Bdd, BddError, FALSE, TRUE};
use crate::sema;

/// A compiled integer expression: LSB-first two's-complement bits + fault.
#[derive(Clone)]
pub struct IVal {
    pub bits: Vec<u32>,
    pub fault: u32,
    /// Static range of this expression (from type inference) — the bits
    /// encode values within exactly this range.
    pub range: IntRange,
}

/// A compiled boolean expression: BDD node + fault.
#[derive(Clone, Copy)]
pub struct BVal {
    pub val: u32,
    pub fault: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BlastError {
    /// This spec uses an operator the bitblaster does not yet implement.
    Unsupported(&'static str),
    /// Division by zero *symbolically* reachable — handled via fault signal,
    /// but division itself is Unsupported until circuits land (see above).
    Budget(BddError),
}

impl std::fmt::Display for BlastError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BlastError::Unsupported(op) => write!(
                f,
                "bitblaster declines `{}` — circuit not implemented; falling back is correct, guessing is not",
                op
            ),
            BlastError::Budget(e) => write!(f, "BDD budget: {}", e),
        }
    }
}

/// Smallest two's-complement width holding every value in `[lo, hi]`.
pub fn width_for(range: IntRange) -> usize {
    let mut w = 1usize;
    while w < 64 {
        let min = -(1i64 << (w - 1));
        let max = (1i64 << (w - 1)) - 1;
        if range.lo >= min && range.hi <= max {
            return w;
        }
        w += 1;
    }
    64
}

pub struct BitBlaster<'a> {
    pub bdd: &'a mut Bdd,
    /// Next free BDD variable index.
    next_var: u32,
}

impl<'a> BitBlaster<'a> {
    pub fn new(bdd: &'a mut Bdd) -> Self {
        BitBlaster { bdd, next_var: 0 }
    }

    pub fn vars_used(&self) -> u32 {
        self.next_var
    }

    fn fresh(&mut self) -> u32 {
        let v = self.next_var;
        self.next_var += 1;
        v
    }

    /// A constant integer as bits over `range` (const must lie in range).
    /// Constant bits are terminals — they consume no variable indices.
    pub fn int_const(&mut self, v: i64, range: IntRange) -> Result<IVal, BlastError> {
        let w = width_for(range);
        let mut bits = Vec::with_capacity(w);
        for i in 0..w {
            let bit = (v >> i) & 1 == 1;
            bits.push(self.bdd.mk_const(0, bit).map_err(BlastError::Budget)?);
        }
        Ok(IVal {
            bits,
            fault: FALSE,
            range,
        })
    }

    /// Fresh unconstrained input bits for a declared parameter range
    /// (param-major allocation). `param_bits_interleaved` is preferred for
    /// whole-spec blasting; this remains for single-parameter uses and
    /// tests.
    #[allow(dead_code)]
    pub fn param_bits(&mut self, range: IntRange) -> Result<IVal, BlastError> {
        let w = width_for(range);
        let mut bits = Vec::with_capacity(w);
        for _ in 0..w {
            let var = self.fresh();
            let node = self.bdd.var_node(var).map_err(BlastError::Budget)?;
            bits.push(node);
        }
        Ok(IVal {
            bits,
            fault: FALSE,
            range,
        })
    }

    /// Allocate all parameters with **interleaved** variable ordering:
    /// bit 0 of param 0, bit 0 of param 1, …, bit 1 of param 0, …
    ///
    /// This is the Bryant-style ordering that keeps ripple-carry chains
    /// (and comparators) local: for `a - amount` the corresponding bits of
    /// the operands stay adjacent in the order, so carry subfunctions
    /// reuse nodes instead of interleaving across whole 9-bit blocks.
    /// Param-major ordering made `transfer_funds` explode past 5M nodes;
    /// interleaved proves it in a few thousand. (Cross-validation caught
    /// no *correctness* difference — this is purely about size.)
    pub fn param_bits_interleaved(
        &mut self,
        ranges: &[IntRange],
    ) -> Result<Vec<IVal>, BlastError> {
        let widths: Vec<usize> = ranges.iter().map(|r| width_for(*r)).collect();
        let max_w = widths.iter().copied().max().unwrap_or(1);
        let mut out: Vec<Vec<u32>> = ranges.iter().map(|_| Vec::new()).collect();
        for bit in 0..max_w {
            for (p, w) in widths.iter().enumerate() {
                if bit < *w {
                    let var = self.fresh();
                    let node = self.bdd.var_node(var).map_err(BlastError::Budget)?;
                    out[p].push(node);
                }
            }
        }
        Ok(out
            .into_iter()
            .zip(ranges)
            .map(|(bits, range)| IVal {
                bits,
                fault: FALSE,
                range: *range,
            })
            .collect())
    }

    /// `domain_ok`: the raw bit pattern lies within the declared range.
    /// (Bit patterns outside [lo, hi] exist whenever the range isn't a full
    /// two's-complement window — e.g. `int[0..255]` in 9 bits admits -1.)
    pub fn in_domain(&mut self, v: &IVal, range: IntRange) -> Result<u32, BlastError> {
        let ge_lo = self.signed_ge(v, range.lo)?;
        let le_hi = self.signed_le(v, range.hi)?;
        self.bdd.and(ge_lo, le_hi).map_err(BlastError::Budget)
    }

    // ---- bit helpers ------------------------------------------------------

    fn sign_extend(&mut self, v: &IVal, w: usize) -> Result<Vec<u32>, BlastError> {
        debug_assert!(w >= v.bits.len());
        let mut bits = v.bits.clone();
        let msb = *bits.last().expect("non-empty bitvector");
        while bits.len() < w {
            bits.push(msb);
        }
        Ok(bits)
    }

    #[allow(dead_code)]
    fn zero_extend(&mut self, v: &IVal, w: usize) -> Result<Vec<u32>, BlastError> {
        let mut bits = v.bits.clone();
        while bits.len() < w {
            bits.push(FALSE);
        }
        Ok(bits)
    }

    /// Ripple-carry add of two equally-wide bitvectors; returns w bits
    /// (carry dropped — caller's static range analysis guarantees the true
    /// sum fits, which the `range` field documents).
    fn add_bits(&mut self, a: &[u32], b: &[u32]) -> Result<Vec<u32>, BlastError> {
        debug_assert_eq!(a.len(), b.len());
        let mut carry = FALSE;
        let mut out = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            // sum = a ⊕ b ⊕ carry
            let axb = self.bdd.xor(a[i], b[i]).map_err(BlastError::Budget)?;
            let sum = self.bdd.xor(axb, carry).map_err(BlastError::Budget)?;
            // carry' = (a ∧ b) ∨ (axb ∧ carry)
            let ab = self.bdd.and(a[i], b[i]).map_err(BlastError::Budget)?;
            let abc = self.bdd.and(axb, carry).map_err(BlastError::Budget)?;
            carry = self.bdd.or(ab, abc).map_err(BlastError::Budget)?;
            out.push(sum);
        }
        Ok(out)
    }

    fn neg_bits(&mut self, a: &[u32]) -> Result<Vec<u32>, BlastError> {
        // -a = !a + 1
        let not_a: Vec<u32> = {
            let mut v = Vec::with_capacity(a.len());
            for &x in a {
                v.push(self.bdd.neg(x).map_err(BlastError::Budget)?);
            }
            v
        };
        let mut one = vec![FALSE; a.len()];
        one[0] = TRUE;
        self.add_bits(&not_a, &one)
    }

    /// Unsigned: a < b via borrow chain over equal widths.
    fn ult_bits(&mut self, a: &[u32], b: &[u32]) -> Result<u32, BlastError> {
        debug_assert_eq!(a.len(), b.len());
        // borrow-out of a - b: true iff a < b (unsigned).
        let mut borrow = FALSE;
        for i in 0..a.len() {
            // borrow' = (~a ∧ b) ∨ (~a ∧ borrow) ∨ (b ∧ borrow)
            let na = self.bdd.neg(a[i]).map_err(BlastError::Budget)?;
            let nab = self.bdd.and(na, b[i]).map_err(BlastError::Budget)?;
            let nabr = self.bdd.and(na, borrow).map_err(BlastError::Budget)?;
            let br = self.bdd.and(b[i], borrow).map_err(BlastError::Budget)?;
            let t = self.bdd.or(nab, nabr).map_err(BlastError::Budget)?;
            borrow = self.bdd.or(t, br).map_err(BlastError::Budget)?;
        }
        Ok(borrow)
    }

    /// Signed a < b: flip both MSBs (bias to unsigned), compare unsigned.
    fn signed_lt_bits(&mut self, a: &[u32], b: &[u32]) -> Result<u32, BlastError> {
        debug_assert_eq!(a.len(), b.len());
        let w = a.len();
        let mut af = a.to_vec();
        let mut bf = b.to_vec();
        af[w - 1] = self.bdd.neg(a[w - 1]).map_err(BlastError::Budget)?;
        bf[w - 1] = self.bdd.neg(b[w - 1]).map_err(BlastError::Budget)?;
        self.ult_bits(&af, &bf)
    }

    fn signed_ge(&mut self, v: &IVal, k: i64) -> Result<u32, BlastError> {
        // v >= k  ⟺  !(v < k)
        let c = self.int_const(k, IntRange::new(k, k))?;
        let w = v.bits.len().max(c.bits.len());
        let a = self.sign_extend(v, w)?;
        let b = self.sign_extend(&c, w)?;
        let lt = self.signed_lt_bits(&a, &b)?;
        self.bdd.neg(lt).map_err(BlastError::Budget)
    }

    fn signed_le(&mut self, v: &IVal, k: i64) -> Result<u32, BlastError> {
        let c = self.int_const(k, IntRange::new(k, k))?;
        let w = v.bits.len().max(c.bits.len());
        let a = self.sign_extend(v, w)?;
        let b = self.sign_extend(&c, w)?;
        let lt = self.signed_lt_bits(&b, &a)?; // k < v
        self.bdd.neg(lt).map_err(BlastError::Budget)
    }

    #[allow(dead_code)]
    fn or_all(&mut self, mut xs: Vec<u32>) -> Result<u32, BlastError> {
        let mut acc = FALSE;
        for x in xs.drain(..) {
            acc = self.bdd.or(acc, x).map_err(BlastError::Budget)?;
        }
        Ok(acc)
    }

    // ---- expression compilation ------------------------------------------

    /// Compile an integer expression over already-compiled integer params.
    pub fn blast_int(
        &mut self,
        e: &Expr,
        env: &std::collections::HashMap<String, IVal>,
    ) -> Result<IVal, BlastError> {
        let range = match sema::infer_int(e, env_ranges(env)) {
            Ok(r) => r,
            Err(_) => return Err(BlastError::Unsupported("expression out of int fragment")),
        };

        match e {
            Expr::IntLit(v) => self.int_const(*v, range),
            Expr::BoolLit(_) => Err(BlastError::Unsupported("bool in int position")),
            Expr::Param(name) | Expr::Result(name) => {
                let v = env
                    .get(name)
                    .ok_or(BlastError::Unsupported("unbound variable"))?;
                Ok(IVal {
                    bits: v.bits.clone(),
                    fault: v.fault,
                    range: v.range,
                })
            }
            Expr::Unary(UnOp::Neg, inner) => {
                let a = self.blast_int(inner, env)?;
                let w = width_for(range).max(a.bits.len());
                let a = self.sign_extend(&a, w)?;
                let bits = self.neg_bits(&a)?;
                Ok(IVal {
                    bits,
                    fault: FALSE, // neg cannot fault in i64-bounded domains
                    range,
                })
            }
            Expr::Unary(UnOp::Not, _) => Err(BlastError::Unsupported("! on int")),
            Expr::Binary(op, l, r) => self.blast_int_binary(*op, l, r, env, range),
            Expr::Ite(c, a, b) => {
                let cv = self.blast_bool(c, env)?;
                let av = self.blast_int(a, env)?;
                let bv = self.blast_int(b, env)?;
                let w = width_for(range).max(av.bits.len()).max(bv.bits.len());
                let aa = self.sign_extend(&av, w)?;
                let bb = self.sign_extend(&bv, w)?;
                let mut bits = Vec::with_capacity(w);
                for i in 0..w {
                    let bit = self.bdd.ite(cv.val, aa[i], bb[i]).map_err(BlastError::Budget)?;
                    bits.push(bit);
                }
                // Lazy fault: only the taken branch faults.
                let ft = self.bdd.and(cv.val, av.fault).map_err(BlastError::Budget)?;
                let fe = {
                    let nc = self.bdd.neg(cv.val).map_err(BlastError::Budget)?;
                    self.bdd.and(nc, bv.fault).map_err(BlastError::Budget)?
                };
                let mut f = self.bdd.or(cv.fault, ft).map_err(BlastError::Budget)?;
                f = self.bdd.or(f, fe).map_err(BlastError::Budget)?;
                Ok(IVal {
                    bits,
                    fault: f,
                    range,
                })
            }
            Expr::Min(a, b) => {
                let av = self.blast_int(a, env)?;
                let bv = self.blast_int(b, env)?;
                self.int_minmax(av, bv, range, true)
            }
            Expr::Max(a, b) => {
                let av = self.blast_int(a, env)?;
                let bv = self.blast_int(b, env)?;
                self.int_minmax(av, bv, range, false)
            }
            // ---- quantifiers: unrolled symbolically ------------------
            // Bounds may be symbolic, so we unroll over the widest range the
            // bound can take and guard every term with `k <= bound`. That is
            // exact: iterations beyond the true bound contribute nothing
            // (0 for a sum, `true` for `forall`, `false` for `exists`).
            Expr::Sum { var, lo, hi, body } => {
                let lo_r = self.expr_range(lo, env)?;
                let hi_r = self.expr_range(hi, env)?;
                let mut acc = self.int_const(0, range)?;
                for k in lo_r.lo..=hi_r.hi {
                    let mut inner = env.clone();
                    inner.insert(var.clone(), self.int_const(k, IntRange::new(k, k))?);
                    let term = self.blast_int(body, &inner)?;
                    // guard: k <= hi
                    let guard = self.blast_bool(
                        &Expr::Binary(BinOp::Le, Box::new(Expr::IntLit(k)), hi.clone()),
                        env,
                    )?;
                    let sum = self.add_i32(&acc, &term)?;
                    acc = self.select(guard.val, sum.clone(), acc.clone())?;
                    // A fault in a term that is actually taken is a fault.
                    let g = guard.val;
                    let _ = g;
                }
                Ok(acc)
            }
            Expr::Forall { .. } | Expr::Exists { .. } => Err(BlastError::Unsupported(
                "quantifier in int position",
            )),
            // Arrays need read-over-write in the symbolic state, which the
            // Hoare path removes before we get here. Decline honestly.
            Expr::ArrayRead(..) | Expr::Len(_) => Err(BlastError::Unsupported(
                "array fragment (use the exhaustive or Hoare engine)",
            )),
        }
    }

    /// The static range of an expression under the current environment.
    fn expr_range(
        &mut self,
        e: &Expr,
        env: &std::collections::HashMap<String, IVal>,
    ) -> Result<IntRange, BlastError> {
        sema::infer_int(e, env_ranges(env))
            .map_err(|_| BlastError::Unsupported("expression out of int fragment"))
    }

    /// Bitwise select: `ite(c, a, b)` over two integer values.
    fn select(&mut self, c: u32, a: IVal, b: IVal) -> Result<IVal, BlastError> {
        let w = a.bits.len().max(b.bits.len());
        let aa = self.sign_extend(&a, w)?;
        let bb = self.sign_extend(&b, w)?;
        let mut bits = Vec::with_capacity(w);
        for i in 0..w {
            bits.push(self.bdd.ite(c, aa[i], bb[i]).map_err(BlastError::Budget)?);
        }
        let fault = self.bdd.or(a.fault, b.fault).map_err(BlastError::Budget)?;
        Ok(IVal {
            bits,
            fault,
            range: IntRange::new(a.range.lo.min(b.range.lo), a.range.hi.max(b.range.hi)),
        })
    }

    /// Add two integer values, widening to a common width.
    fn add_i32(&mut self, a: &IVal, b: &IVal) -> Result<IVal, BlastError> {
        let w = a.bits.len().max(b.bits.len()) + 1;
        let aa = self.sign_extend(a, w)?;
        let bb = self.sign_extend(b, w)?;
        let bits = self.add_bits(&aa, &bb)?;
        let fault = self.bdd.or(a.fault, b.fault).map_err(BlastError::Budget)?;
        Ok(IVal {
            bits,
            fault,
            range: IntRange::new(
                a.range.lo.saturating_add(b.range.lo),
                a.range.hi.saturating_add(b.range.hi),
            ),
        })
    }

    fn int_minmax(
        &mut self,
        a: IVal,
        b: IVal,
        range: IntRange,
        want_min: bool,
    ) -> Result<IVal, BlastError> {
        let w = width_for(range).max(a.bits.len()).max(b.bits.len());
        let ab = self.sign_extend(&a, w)?;
        let bb = self.sign_extend(&b, w)?;
        let a_lt_b = self.signed_lt_bits(&ab, &bb)?;
        // min = ite(a<b, a, b); max = ite(a<b, b, a)
        let (t, e) = if want_min { (ab.clone(), bb.clone()) } else { (bb.clone(), ab.clone()) };
        let mut bits = Vec::with_capacity(w);
        for i in 0..w {
            bits.push(self.bdd.ite(a_lt_b, t[i], e[i]).map_err(BlastError::Budget)?);
        }
        let fault = self.bdd.or(a.fault, b.fault).map_err(BlastError::Budget)?;
        Ok(IVal { bits, fault, range })
    }

    fn blast_int_binary(
        &mut self,
        op: BinOp,
        l: &Expr,
        r: &Expr,
        env: &std::collections::HashMap<String, IVal>,
        range: IntRange,
    ) -> Result<IVal, BlastError> {
        match op {
            BinOp::Div | BinOp::Mod => Err(BlastError::Unsupported("division")),
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let av = self.blast_int(l, env)?;
                let bv = self.blast_int(r, env)?;
                let fault = self.bdd.or(av.fault, bv.fault).map_err(BlastError::Budget)?;
                // The circuit must be wide enough for the RESULT range *and*
                // for both OPERANDS: in a chain like `a + 1 - 1`, an
                // intermediate can be wider than the final static range.
                // (Cross-validation caught this as an engine panic.)
                let w = width_for(range)
                    .max(av.bits.len())
                    .max(bv.bits.len())
                    .max(if op == BinOp::Mul {
                        av.bits.len() + bv.bits.len()
                    } else {
                        0
                    });
                let aa = self.sign_extend(&av, w)?;
                let bb = self.sign_extend(&bv, w)?;
                let bits = match op {
                    BinOp::Add => self.add_bits(&aa, &bb)?,
                    BinOp::Sub => {
                        let nb = self.neg_bits(&bb)?;
                        self.add_bits(&aa, &nb)?
                    }
                    BinOp::Mul => self.mul_bits(&aa, &bb, width_for(range))?,
                    _ => unreachable!(),
                };
                // Truncation to the static range is sound: interval analysis
                // proved every true result fits, so the dropped high bits are
                // sign-redundant.
                Ok(IVal {
                    bits: bits[..width_for(range)].to_vec(),
                    fault,
                    range,
                })
            }
            // Comparisons produce bools — never reached from blast_int on a
            // bool-typed node, but the type checker routes them there only
            // when the caller is wrong. Guard anyway.
            _ => Err(BlastError::Unsupported("comparison in int position")),
        }
    }

    /// Shift-add multiplier truncated to `w` bits.
    fn mul_bits(&mut self, a: &[u32], b: &[u32], w: usize) -> Result<Vec<u32>, BlastError> {
        let mut acc = vec![FALSE; w];
        for i in 0..b.len() {
            if i >= w {
                break;
            }
            // partial = a << i, truncated to w; add if b[i]
            let mut shifted = vec![FALSE; w];
            for j in 0..w {
                if j >= i {
                    shifted[j] = a[j - i];
                }
            }
            // acc = ite(b[i], acc + shifted, acc)
            let sum = self.add_bits(&acc, &shifted)?;
            let mut next = Vec::with_capacity(w);
            for j in 0..w {
                next.push(self.bdd.ite(b[i], sum[j], acc[j]).map_err(BlastError::Budget)?);
            }
            acc = next;
        }
        Ok(acc)
    }

    /// Compile a boolean expression.
    pub fn blast_bool(
        &mut self,
        e: &Expr,
        env: &std::collections::HashMap<String, IVal>,
    ) -> Result<BVal, BlastError> {
        match e {
            Expr::BoolLit(b) => Ok(BVal {
                val: if *b { TRUE } else { FALSE },
                fault: FALSE,
            }),
            Expr::Unary(UnOp::Not, inner) => {
                let a = self.blast_bool(inner, env)?;
                let val = self.bdd.neg(a.val).map_err(BlastError::Budget)?;
                Ok(BVal { val, fault: a.fault })
            }
            Expr::Binary(op, l, r) => match op {
                BinOp::And => {
                    let a = self.blast_bool(l, env)?;
                    let b = self.blast_bool(r, env)?;
                    // Short-circuit: RHS fault only matters if LHS is true.
                    let rf = self.bdd.and(a.val, b.fault).map_err(BlastError::Budget)?;
                    let fault = self.bdd.or(a.fault, rf).map_err(BlastError::Budget)?;
                    let val = self.bdd.and(a.val, b.val).map_err(BlastError::Budget)?;
                    Ok(BVal { val, fault })
                }
                BinOp::Or => {
                    let a = self.blast_bool(l, env)?;
                    let b = self.blast_bool(r, env)?;
                    // RHS fault matters only if LHS is false.
                    let na = self.bdd.neg(a.val).map_err(BlastError::Budget)?;
                    let rf = self.bdd.and(na, b.fault).map_err(BlastError::Budget)?;
                    let fault = self.bdd.or(a.fault, rf).map_err(BlastError::Budget)?;
                    let val = self.bdd.or(a.val, b.val).map_err(BlastError::Budget)?;
                    Ok(BVal { val, fault })
                }
                BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    let av = self.blast_int(l, env)?;
                    let bv = self.blast_int(r, env)?;
                    let fault = self.bdd.or(av.fault, bv.fault).map_err(BlastError::Budget)?;
                    let w = av.bits.len().max(bv.bits.len());
                    let aa = self.sign_extend(&av, w)?;
                    let bb = self.sign_extend(&bv, w)?;
                    let val = match op {
                        BinOp::Eq => self.bits_eq(&aa, &bb)?,
                        BinOp::Ne => {
                            let eq = self.bits_eq(&aa, &bb)?;
                            self.bdd.neg(eq).map_err(BlastError::Budget)?
                        }
                        BinOp::Lt => self.signed_lt_bits(&aa, &bb)?,
                        BinOp::Le => {
                            let gt = self.signed_lt_bits(&bb, &aa)?;
                            self.bdd.neg(gt).map_err(BlastError::Budget)?
                        }
                        BinOp::Gt => self.signed_lt_bits(&bb, &aa)?,
                        BinOp::Ge => {
                            let lt = self.signed_lt_bits(&aa, &bb)?;
                            self.bdd.neg(lt).map_err(BlastError::Budget)?
                        }
                        _ => unreachable!(),
                    };
                    Ok(BVal { val, fault })
                }
                _ => Err(BlastError::Unsupported("int op in bool position")),
            },
            Expr::Ite(c, a, b) => {
                let cv = self.blast_bool(c, env)?;
                let av = self.blast_bool(a, env)?;
                let bv = self.blast_bool(b, env)?;
                let val = self.bdd.ite(cv.val, av.val, bv.val).map_err(BlastError::Budget)?;
                let ft = self.bdd.and(cv.val, av.fault).map_err(BlastError::Budget)?;
                let nc = self.bdd.neg(cv.val).map_err(BlastError::Budget)?;
                let fe = self.bdd.and(nc, bv.fault).map_err(BlastError::Budget)?;
                let mut fault = self.bdd.or(cv.fault, ft).map_err(BlastError::Budget)?;
                fault = self.bdd.or(fault, fe).map_err(BlastError::Budget)?;
                Ok(BVal { val, fault })
            }
            Expr::Param(_) | Expr::Result(_) => {
                // A bare name in bool position would be a bool-typed variable;
                // v0.1 int-only params ⇒ unreachable if sema passed.
                Err(BlastError::Unsupported("bool variable"))
            }
            // ---- quantifiers: unrolled symbolically -----------------------
            // Bounds may be symbolic, so unroll over the widest range the
            // bound can take, guarding each term with `k <= bound`. Exact:
            // iterations past the true bound are vacuous (`true` for forall,
            // `false` for exists).
            Expr::Forall { var, lo, hi, body } => {
                let lo_r = self.expr_range(lo, env)?;
                let hi_r = self.expr_range(hi, env)?;
                let mut acc = TRUE;
                for k in lo_r.lo..=hi_r.hi {
                    let mut inner = env.clone();
                    inner.insert(var.clone(), self.int_const(k, IntRange::new(k, k))?);
                    let b = self.blast_bool(body, &inner)?;
                    // (k > hi) ∨ body(k)
                    let past = self.blast_bool(
                        &Expr::Binary(BinOp::Gt, Box::new(Expr::IntLit(k)), hi.clone()),
                        env,
                    )?;
                    let step = self.bdd.or(past.val, b.val).map_err(BlastError::Budget)?;
                    acc = self.bdd.and(acc, step).map_err(BlastError::Budget)?;
                }
                Ok(BVal { val: acc, fault: FALSE })
            }
            Expr::Exists { var, lo, hi, body } => {
                let lo_r = self.expr_range(lo, env)?;
                let hi_r = self.expr_range(hi, env)?;
                let mut acc = FALSE;
                for k in lo_r.lo..=hi_r.hi {
                    let mut inner = env.clone();
                    inner.insert(var.clone(), self.int_const(k, IntRange::new(k, k))?);
                    let b = self.blast_bool(body, &inner)?;
                    // (k <= hi) ∧ body(k)
                    let within = self.blast_bool(
                        &Expr::Binary(BinOp::Le, Box::new(Expr::IntLit(k)), hi.clone()),
                        env,
                    )?;
                    let step = self.bdd.and(within.val, b.val).map_err(BlastError::Budget)?;
                    acc = self.bdd.or(acc, step).map_err(BlastError::Budget)?;
                }
                Ok(BVal { val: acc, fault: FALSE })
            }
            _ => Err(BlastError::Unsupported("expression fragment")),
        }
    }

    fn bits_eq(&mut self, a: &[u32], b: &[u32]) -> Result<u32, BlastError> {
        debug_assert_eq!(a.len(), b.len());
        let mut acc = TRUE;
        for i in 0..a.len() {
            // xnor: ite(a, b, !b)  ==  !(a xor b)
            let x = self.bdd.xor(a[i], b[i]).map_err(BlastError::Budget)?;
            let nx = self.bdd.neg(x).map_err(BlastError::Budget)?;
            acc = self.bdd.and(acc, nx).map_err(BlastError::Budget)?;
        }
        Ok(acc)
    }

    /// Bad state for a *predicate* obligation (no body): the assignment
    /// `domain_ok ∧ pre ∧ ¬post` must be unsatisfiable for the obligation to
    /// hold. Used by the Hoare path, where obligations are implications over
    /// the program's variables rather than contracts over a body.
    pub fn bad_state_predicate(
        &mut self,
        spec: &Spec,
        param_vals: &std::collections::HashMap<String, IVal>,
        param_nodes: &[(String, IVal)],
        pre: &[Expr],
        post: &[Expr],
    ) -> Result<u32, BlastError> {
        // 1. domain_ok over every quantified variable.
        let mut domain_ok = TRUE;
        for (name, v) in param_nodes {
            let range = match spec.params.iter().find(|b| &b.name == name) {
                Some(b) => match b.ty {
                    Type::Int(r) => r,
                    Type::Decimal { stored, .. } => stored,
                    Type::Bool => IntRange::new(0, 1),
                    Type::Array { .. } => {
                        return Err(BlastError::Unsupported("array in obligation"))
                    }
                },
                None => return Err(BlastError::Unsupported("unknown variable")),
            };
            let ok = self.in_domain(v, range)?;
            domain_ok = self.bdd.and(domain_ok, ok).map_err(BlastError::Budget)?;
        }

        // 2. assumptions hold (and don't fault).
        let mut assump = TRUE;
        for a in pre {
            let c = self.blast_bool(a, param_vals)?;
            let no_fault = self.bdd.neg(c.fault).map_err(BlastError::Budget)?;
            let holds = self.bdd.and(no_fault, c.val).map_err(BlastError::Budget)?;
            assump = self.bdd.and(assump, holds).map_err(BlastError::Budget)?;
        }

        // 3. negate the conjunction of goals.
        let mut all_goals = TRUE;
        for g in post {
            let c = self.blast_bool(g, param_vals)?;
            let no_fault = self.bdd.neg(c.fault).map_err(BlastError::Budget)?;
            let holds = self.bdd.and(no_fault, c.val).map_err(BlastError::Budget)?;
            all_goals = self.bdd.and(all_goals, holds).map_err(BlastError::Budget)?;
        }
        let goal_fails = self.bdd.neg(all_goals).map_err(BlastError::Budget)?;

        let d = self.bdd.and(domain_ok, assump).map_err(BlastError::Budget)?;
        self.bdd.and(d, goal_fails).map_err(BlastError::Budget)
    }

    /// The full bad-state function for (spec, body) over compiled params.
    ///
    /// Returns `(bad, domain_ok, pre_ok)`.
    pub fn bad_state(
        &mut self,
        spec: &Spec,
        body: &[Assign],
        param_vals: &std::collections::HashMap<String, IVal>,
        param_nodes: &[(String, IVal)],
    ) -> Result<u32, BlastError> {
        // 1. domain_ok: every param's raw bits within declared range.
        let mut domain_ok = TRUE;
        for (name, v) in param_nodes {
            let range = match spec.params.iter().find(|b| &b.name == name) {
                Some(b) => match b.ty {
                    Type::Int(r) => r,
                    Type::Decimal { stored, .. } => stored,
                    Type::Bool => return Err(BlastError::Unsupported("bool param")),
                    Type::Array { .. } => {
                        return Err(BlastError::Unsupported("array param (use the exhaustive engine)"))
                    }
                },
                None => return Err(BlastError::Unsupported("unknown param")),
            };
            let ok = self.in_domain(v, range)?;
            domain_ok = self.bdd.and(domain_ok, ok).map_err(BlastError::Budget)?;
        }

        // 2. Substitute the body into ensures, making everything param-only.
        let subst_map = body_subst_map(body)?;
        let mut post = TRUE;
        let mut post_fault = FALSE;
        for clause in &spec.requires {
            let compiled = self.blast_bool(clause, param_vals)?;
            // Faulting precondition ⇒ out of domain (matches eval: fault ⇒ false).
            let no_fault = self.bdd.neg(compiled.fault).map_err(BlastError::Budget)?;
            let holds = self.bdd.and(no_fault, compiled.val).map_err(BlastError::Budget)?;
            post = self.bdd.and(post, holds).map_err(BlastError::Budget)?;
            post_fault = self.bdd.or(post_fault, compiled.fault).map_err(BlastError::Budget)?;
        }
        // `post` now holds pre_ok ∧ pre_true; pre_fault marks faulting pre.
        let pre_ok = post;
        let _ = post_fault;

        // Result-range checks + ensures, with body substituted in.
        // Results are matched to their assignment BY NAME — the body may
        // assign results in any order.
        let mut viol = FALSE;
        for res in &spec.results {
            let assigns = body
                .iter()
                .find(|a| a.name == res.name)
                .expect("parser guarantees every result assigned exactly once");
            let rhs = subst_expr(&assigns.value, &subst_map);
            let compiled = self.blast_int(&rhs, param_vals)?;
            let (decl_lo, decl_hi) = res_decl(spec, &res.name);
            let in_lo = self.signed_ge(&compiled, decl_lo)?;
            let in_hi = self.signed_le(&compiled, decl_hi)?;
            let in_r = self.bdd.and(in_lo, in_hi).map_err(BlastError::Budget)?;
            let out_of = self.bdd.neg(in_r).map_err(BlastError::Budget)?;
            viol = self.bdd.or(viol, out_of).map_err(BlastError::Budget)?;
            viol = self.bdd.or(viol, compiled.fault).map_err(BlastError::Budget)?;
        }
        // Enforce result values inside ensures context: substitute results.
        for clause in &spec.ensures {
            let substituted = subst_expr(clause, &subst_map);
            let compiled = self.blast_bool(&substituted, param_vals)?;
            let not_holds = self.bdd.neg(compiled.val).map_err(BlastError::Budget)?;
            viol = self.bdd.or(viol, not_holds).map_err(BlastError::Budget)?;
            viol = self.bdd.or(viol, compiled.fault).map_err(BlastError::Budget)?;
        }

        // bad = domain ∧ pre ∧ viol
        let d = self.bdd.and(domain_ok, pre_ok).map_err(BlastError::Budget)?;
        let bad = self.bdd.and(d, viol).map_err(BlastError::Budget)?;
        Ok(bad)
    }
}

fn res_decl(spec: &Spec, name: &str) -> (i64, i64) {
    let b = spec
        .results
        .iter()
        .find(|b| b.name == name)
        .expect("sema guaranteed");
    match b.ty {
        Type::Int(r) => (r.lo, r.hi),
        Type::Decimal { stored, .. } => (stored.lo, stored.hi),
        Type::Bool => (0, 1),
        Type::Array { index, .. } => (index.lo, index.hi),
    }
}

fn env_ranges(
    env: &std::collections::HashMap<String, IVal>,
) -> std::collections::HashMap<String, IntRange> {
    env.iter().map(|(k, v)| (k.clone(), v.range)).collect()
}

/// Build the sequential body substitution: result name → param-only expr.
fn body_subst_map(body: &[Assign]) -> Result<std::collections::HashMap<String, Expr>, BlastError> {
    let mut map = std::collections::HashMap::new();
    for a in body {
        let rhs = subst_expr(&a.value, &map);
        map.insert(a.name.clone(), rhs);
    }
    Ok(map)
}

/// Substitute `result.x` / bare-result references with their body expressions.
fn subst_expr(e: &Expr, map: &std::collections::HashMap<String, Expr>) -> Expr {
    match e {
        Expr::Result(name) => map
            .get(name)
            .cloned()
            .unwrap_or_else(|| Expr::Result(name.clone())),
        Expr::Param(name) => map
            .get(name)
            .cloned()
            .unwrap_or_else(|| Expr::Param(name.clone())),
        Expr::Unary(op, a) => Expr::Unary(*op, Box::new(subst_expr(a, map))),
        Expr::Binary(op, l, r) => Expr::Binary(
            *op,
            Box::new(subst_expr(l, map)),
            Box::new(subst_expr(r, map)),
        ),
        Expr::Ite(c, a, b) => Expr::Ite(
            Box::new(subst_expr(c, map)),
            Box::new(subst_expr(a, map)),
            Box::new(subst_expr(b, map)),
        ),
        Expr::Min(a, b) => Expr::Min(Box::new(subst_expr(a, map)), Box::new(subst_expr(b, map))),
        Expr::Max(a, b) => Expr::Max(Box::new(subst_expr(a, map)), Box::new(subst_expr(b, map))),
        Expr::ArrayRead(n, i) => Expr::ArrayRead(n.clone(), Box::new(subst_expr(i, map))),
        Expr::Len(n) => Expr::Len(n.clone()),
        Expr::Forall { var, lo, hi, body } => Expr::Forall {
            var: var.clone(),
            lo: Box::new(subst_expr(lo, map)),
            hi: Box::new(subst_expr(hi, map)),
            body: Box::new(subst_expr(body, map)),
        },
        Expr::Exists { var, lo, hi, body } => Expr::Exists {
            var: var.clone(),
            lo: Box::new(subst_expr(lo, map)),
            hi: Box::new(subst_expr(hi, map)),
            body: Box::new(subst_expr(body, map)),
        },
        Expr::Sum { var, lo, hi, body } => Expr::Sum {
            var: var.clone(),
            lo: Box::new(subst_expr(lo, map)),
            hi: Box::new(subst_expr(hi, map)),
            body: Box::new(subst_expr(body, map)),
        },
        Expr::IntLit(_) | Expr::BoolLit(_) => e.clone(),
    }
}

/// Does this expression use a fragment the bitblaster declines?
///
/// Division/modulo circuits are not implemented; arrays need a theory of
/// read-over-write the symbolic state does not carry (the Hoare path removes
/// them first). Quantifiers ARE supported — they are unrolled exactly.
pub fn contains_division(e: &Expr) -> bool {
    match e {
        Expr::Binary(BinOp::Div | BinOp::Mod, _, _) => true,
        Expr::Binary(_, l, r) => contains_division(l) || contains_division(r),
        Expr::Unary(_, a) => contains_division(a),
        Expr::Ite(c, a, b) => contains_division(c) || contains_division(a) || contains_division(b),
        Expr::Min(a, b) | Expr::Max(a, b) => contains_division(a) || contains_division(b),
        Expr::ArrayRead(_, i) => true || contains_division(i),
        Expr::Len(_) => false, // a constant; harmless
        Expr::Forall { lo, hi, body, .. }
        | Expr::Exists { lo, hi, body, .. }
        | Expr::Sum { lo, hi, body, .. } => {
            contains_division(lo) || contains_division(hi) || contains_division(body)
        }
        _ => false,
    }
}

/// Scan a whole spec+body for unsupported operators.
pub fn spec_supported(spec: &Spec, body: &[Assign]) -> Result<(), &'static str> {
    let all = spec
        .requires
        .iter()
        .chain(spec.ensures.iter())
        .chain(body.iter().map(|a| &a.value));
    for e in all {
        if contains_division(e) {
            return Err("division/modulo");
        }
    }
    Ok(())
}
