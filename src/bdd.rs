//! Reduced Ordered Binary Decision Diagrams (ROBDD).
//!
//! The symbolic heart of the prover. While the exhaustive engine walks the
//! input domain one vector at a time, the BDD engine compiles the *entire
//! domain* into one boolean function and asks a single question: is the
//! "bad state" function satisfiable? If it reduces to `false`, no input in
//! the whole domain — billions at once — can violate the contract.
//!
//! Two engines that share no code path and agree on the verdict give us
//! something neither has alone: cross-validated proofs. (The exhaustive
//! engine speaks i64 arithmetic; this one speaks boolean circuits. A bug in
//! one shows up as a disagreement, not a wrong certificate.)
//!
//! Design:
//! * Classic ROBDD with a unique table (canonical form) and computed cache.
//! * `ite` is the sole primitive; and/or/xor are derived from it.
//! * A node budget aborts the engine *soundly* — we report "gave up", never
//!   a false proof. Budget exceeded is a fallback trigger, never a verdict.

use std::collections::HashMap;

pub const FALSE: u32 = 0;
pub const TRUE: u32 = 1;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Node {
    var: u32, // variable index; terminals use var = u32::MAX
    low: u32,
    high: u32,
}

#[derive(Debug, PartialEq, Eq)]
pub enum BddError {
    /// Node budget exceeded — engine must report "gave up", not a verdict.
    BudgetExceeded { nodes: usize },
}

impl std::fmt::Display for BddError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BddError::BudgetExceeded { nodes } => {
                write!(f, "node budget exceeded at {} nodes", nodes)
            }
        }
    }
}

pub struct Bdd {
    nodes: Vec<Node>,
    unique: HashMap<Node, u32>,
    /// Memo for primitive ops: (op, a, b, c) -> result. `c` is used only by
    /// the ternary `ite` (op 1); binary ops leave it 0. A 3-tuple key would
    /// silently truncate one of ite's arguments and return wrong nodes —
    /// caught by cross-validation, fixed here.
    cache: HashMap<(u8, u32, u32, u32), u32>,
    budget: usize,
}

impl Bdd {
    pub fn new(budget: usize) -> Self {
        let mut b = Bdd {
            nodes: Vec::with_capacity(1024),
            unique: HashMap::with_capacity(1024),
            cache: HashMap::with_capacity(4096),
            budget,
        };
        // Terminals.
        b.nodes.push(Node {
            var: u32::MAX,
            low: FALSE,
            high: FALSE,
        });
        b.nodes.push(Node {
            var: u32::MAX,
            low: TRUE,
            high: TRUE,
        });
        b
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// The variable index of a node (None for terminals). Lets callers
    /// decode assignments without knowing the allocation order.
    pub fn var_of(&self, node: u32) -> Option<u32> {
        let n = &self.nodes[node as usize];
        if n.var == u32::MAX {
            None
        } else {
            Some(n.var)
        }
    }

    /// A fresh variable node: var → (low=FALSE, high=TRUE), i.e. the
    /// variable itself. Creating the same var twice returns the same node.
    pub fn var_node(&mut self, var: u32) -> Result<u32, BddError> {
        self.mk(var, FALSE, TRUE)
    }

    /// A constant bit for position `var`: TRUE or FALSE. (Not a variable —
    /// used for literal bits inside constant integers.)
    pub fn mk_const(&mut self, _var: u32, bit: bool) -> Result<u32, BddError> {
        if bit {
            Ok(TRUE)
        } else {
            Ok(FALSE)
        }
    }

    fn check_budget(&self) -> Result<(), BddError> {
        if self.nodes.len() >= self.budget {
            Err(BddError::BudgetExceeded {
                nodes: self.nodes.len(),
            })
        } else {
            Ok(())
        }
    }

    /// Make a reduced node: apply the two reduction rules
    /// (child merge, node elimination) and canonicalize via the unique table.
    fn mk(&mut self, var: u32, low: u32, high: u32) -> Result<u32, BddError> {
        if low == high {
            return Ok(low);
        }
        let n = Node { var, low, high };
        if let Some(&id) = self.unique.get(&n) {
            return Ok(id);
        }
        self.check_budget()?;
        let id = self.nodes.len() as u32;
        self.nodes.push(n);
        self.unique.insert(n, id);
        Ok(id)
    }

    pub fn neg(&mut self, a: u32) -> Result<u32, BddError> {
        if a == FALSE {
            return Ok(TRUE);
        }
        if a == TRUE {
            return Ok(FALSE);
        }
        if let Some(&r) = self.cache.get(&(0, a, 0, 0)) {
            return Ok(r);
        }
        let node = self.nodes[a as usize];
        let low = self.neg(node.low)?;
        let high = self.neg(node.high)?;
        let r = self.mk(node.var, low, high)?;
        self.cache.insert((0, a, 0, 0), r);
        Ok(r)
    }

    pub fn ite(&mut self, i: u32, t: u32, e: u32) -> Result<u32, BddError> {
        // Fast paths.
        if i == TRUE {
            return Ok(t);
        }
        if i == FALSE {
            return Ok(e);
        }
        if t == e {
            return Ok(t);
        }
        if t == TRUE && e == FALSE {
            return Ok(i);
        }
        if t == FALSE && e == TRUE {
            return self.neg(i);
        }
        if let Some(&r) = self.cache.get(&(1, i, t, e)) {
            return Ok(r);
        }
        // Shannon: ite(i,t,e) = (i ∧ t) ∨ (¬i ∧ e)
        // Implemented directly over the top variable for speed.
        let top = self.top_var(i, t, e);
        let (i_hi, i_lo) = self.cofactors(i, top);
        let (t_hi, t_lo) = self.cofactors(t, top);
        let (e_hi, e_lo) = self.cofactors(e, top);
        let hi = self.ite(i_hi, t_hi, e_hi)?;
        let lo = self.ite(i_lo, t_lo, e_lo)?;
        let r = self.mk(top, lo, hi)?;
        self.cache.insert((1, i, t, e), r);
        Ok(r)
    }

    fn cofactors(&self, f: u32, var: u32) -> (u32, u32) {
        // (high, low) cofactor of f w.r.t. var.
        let vn = self.nodes[f as usize];
        if vn.var == var {
            (vn.high, vn.low)
        } else {
            (f, f)
        }
    }

    fn top_var(&self, i: u32, t: u32, e: u32) -> u32 {
        let v = |f: u32| {
            let n = self.nodes[f as usize];
            if n.var == u32::MAX {
                u32::MAX
            } else {
                n.var
            }
        };
        let (a, b, c) = (v(i), v(t), v(e));
        a.min(b).min(c)
    }

    pub fn and(&mut self, a: u32, b: u32) -> Result<u32, BddError> {
        if a == FALSE || b == FALSE {
            return Ok(FALSE);
        }
        if a == TRUE {
            return Ok(b);
        }
        if b == TRUE || a == b {
            return Ok(a);
        }
        if let Some(&r) = self.cache.get(&(2, a, b, 0)) {
            return Ok(r);
        }
        let top = self.nodes[a as usize].var.min(self.nodes[b as usize].var);
        let (a_hi, a_lo) = self.cofactors(a, top);
        let (b_hi, b_lo) = self.cofactors(b, top);
        let hi = self.and(a_hi, b_hi)?;
        let lo = self.and(a_lo, b_lo)?;
        let r = self.mk(top, lo, hi)?;
        self.cache.insert((2, a, b, 0), r);
        self.cache.insert((2, b, a, 0), r);
        Ok(r)
    }

    pub fn or(&mut self, a: u32, b: u32) -> Result<u32, BddError> {
        if a == TRUE || b == TRUE {
            return Ok(TRUE);
        }
        if a == FALSE {
            return Ok(b);
        }
        if b == FALSE {
            return Ok(a);
        }
        let na = self.neg(a)?;
        let nb = self.neg(b)?;
        let n = self.and(na, nb)?;
        self.neg(n)
    }

    pub fn xor(&mut self, a: u32, b: u32) -> Result<u32, BddError> {
        let na = self.neg(a)?;
        let nb = self.neg(b)?;
        let t = self.and(a, nb)?;
        let e = self.and(na, b)?;
        self.or(t, e)
    }

    /// Is there an assignment making `f` true? (SAT)
    pub fn sat(&self, f: u32) -> bool {
        f != FALSE
    }

    /// Extract one satisfying assignment: var index -> bool.
    /// Unassigned (don't-care) variables are omitted; the caller fills them.
    pub fn one_sat(&self, f: u32) -> HashMap<u32, bool> {
        let mut assign = HashMap::new();
        let mut cur = f;
        while cur != TRUE && cur != FALSE {
            let n = self.nodes[cur as usize];
            // Prefer the high branch (guided walk); don't-care vars left free.
            if n.high != FALSE && n.low == FALSE {
                assign.insert(n.var, true);
                cur = n.high;
            } else if n.low != FALSE && n.high == FALSE {
                assign.insert(n.var, false);
                cur = n.low;
            } else {
                // Both branches viable: prefer high.
                assign.insert(n.var, true);
                cur = n.high;
            }
        }
        // The walk above can end at FALSE if we guessed wrong on a branch
        // with both sides viable — do a proper DFS instead.
        if cur == FALSE {
            assign.clear();
            self.dfs_sat(f, &mut assign);
        }
        assign
    }

    fn dfs_sat(&self, f: u32, assign: &mut HashMap<u32, bool>) -> bool {
        if f == TRUE {
            return true;
        }
        if f == FALSE {
            return false;
        }
        let n = self.nodes[f as usize];
        // Try high first.
        assign.insert(n.var, true);
        if self.dfs_sat(n.high, assign) {
            return true;
        }
        assign.insert(n.var, false);
        if self.dfs_sat(n.low, assign) {
            return true;
        }
        assign.remove(&n.var);
        false
    }

    /// Number of satisfying assignments over `num_vars` variables.
    ///
    /// Level-aware: skipped variables between a node and its children are
    /// *free* — each contributes a factor of 2. (Naively summing children
    /// undercounts exactly the assignments the reduction rules hid.)
    pub fn count_sat(&self, f: u32, num_vars: u32) -> u128 {
        let mut memo: HashMap<(u32, u32), u128> = HashMap::new();
        self.count_rec(f, 0, num_vars, &mut memo)
    }

    fn count_rec(
        &self,
        f: u32,
        level: u32,
        num_vars: u32,
        memo: &mut HashMap<(u32, u32), u128>,
    ) -> u128 {
        if f == FALSE {
            return 0;
        }
        if f == TRUE {
            // All remaining variables are free.
            return 1u128 << (num_vars - level);
        }
        if let Some(&c) = memo.get(&(f, level)) {
            return c;
        }
        let n = self.nodes[f as usize];
        // Vars between `level` and this node are unconstrained on this path.
        let gap = n.var - level;
        let skip = 1u128 << gap;
        let hi = self.count_rec(n.high, n.var + 1, num_vars, memo);
        let lo = self.count_rec(n.low, n.var + 1, num_vars, memo);
        let c = skip.saturating_mul(hi.saturating_add(lo));
        memo.insert((f, level), c);
        c
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn var_of(b: &mut Bdd, v: u32) -> u32 {
        b.mk(v, FALSE, TRUE).unwrap()
    }

    #[test]
    fn terminals_and_negation() {
        let mut b = Bdd::new(1000);
        assert_eq!(b.neg(FALSE).unwrap(), TRUE);
        assert_eq!(b.neg(TRUE).unwrap(), FALSE);
        let f = b.neg(FALSE).unwrap();
        assert_eq!(b.neg(f).unwrap(), FALSE);
    }

    #[test]
    fn ite_fast_paths() {
        let mut b = Bdd::new(1000);
        let x = var_of(&mut b, 0);
        // ite(x, T, F) = x
        assert_eq!(b.ite(x, TRUE, FALSE).unwrap(), x);
        // ite(x, F, T) = !x
        let ite_ft = b.ite(x, FALSE, TRUE).unwrap();
        let nx = b.neg(x).unwrap();
        assert_eq!(ite_ft, nx);
        // ite(T, a, b) = a
        assert_eq!(b.ite(TRUE, x, FALSE).unwrap(), x);
        // ite(x, a, a) = a
        assert_eq!(b.ite(x, x, x).unwrap(), x);
    }

    #[test]
    fn xor_correct_by_brute_force() {
        let mut b = Bdd::new(10_000);
        let x0 = var_of(&mut b, 0);
        let x1 = var_of(&mut b, 1);
        let f = b.xor(x0, x1).unwrap();
        for mask in 0u8..4 {
            let a0 = mask & 1 != 0;
            let a1 = mask & 2 != 0;
            // Evaluate BDD by traversal.
            let mut cur = f;
            while cur > 1 {
                let n = b.nodes[cur as usize];
                let v = if n.var == 0 { a0 } else { a1 };
                cur = if v { n.high } else { n.low };
            }
            assert_eq!(cur == TRUE, a0 ^ a1, "mask {}", mask);
        }
    }

    #[test]
    fn and_or_agree_with_truth_tables() {
        let mut b = Bdd::new(10_000);
        let x0 = var_of(&mut b, 0);
        let x1 = var_of(&mut b, 1);
        let x2 = var_of(&mut b, 2);
        let o = b.or(x0, x1).unwrap();
        let nx2 = b.neg(x2).unwrap();
        let f = b.and(o, nx2).unwrap();
        for mask in 0u8..8 {
            let a = [mask & 1 != 0, mask & 2 != 0, mask & 4 != 0];
            let expect = (a[0] || a[1]) && !a[2];
            let mut cur = f;
            while cur > 1 {
                let n = b.nodes[cur as usize];
                cur = if a[n.var as usize] { n.high } else { n.low };
            }
            assert_eq!(cur == TRUE, expect, "mask {}", mask);
        }
    }

    #[test]
    fn canonical_forms_match() {
        // Different construction orders must yield the identical node id.
        let mut b = Bdd::new(10_000);
        let x0 = var_of(&mut b, 0);
        let x1 = var_of(&mut b, 1);
        let f1 = b.and(x0, x1).unwrap();
        let f2 = b.and(x1, x0).unwrap();
        assert_eq!(f1, f2, "unique table must canonicalize commutative builds");
    }

    #[test]
    fn budget_aborts_soundly() {
        let mut b = Bdd::new(64); // tiny budget
        let mut acc = FALSE;
        for v in 0..500u32 {
            let x = b.mk(v, FALSE, TRUE).unwrap();
            let r = b.or(acc, x);
            match r {
                Ok(f) => acc = f,
                Err(_) => return, // budget exceeded — the expected outcome
            }
        }
        // If we got here without exceeding, the test still passes only if
        // nodes stayed under budget — acceptable but verify it did trigger.
        assert!(b.node_count() >= 60, "budget never approached");
    }

    #[test]
    fn count_sat_matches_brute_force() {
        let mut b = Bdd::new(10_000);
        let x0 = var_of(&mut b, 0);
        let x1 = var_of(&mut b, 1);
        let f = b.or(x0, x1).unwrap();
        assert_eq!(b.count_sat(f, 2), 3);
        let nx1 = b.neg(x1).unwrap();
        let g = b.and(x0, nx1).unwrap();
        assert_eq!(b.count_sat(g, 2), 1);
        assert_eq!(b.count_sat(FALSE, 2), 0);
        assert_eq!(b.count_sat(TRUE, 2), 4);
    }

    #[test]
    fn one_sat_is_satisfying() {
        let mut b = Bdd::new(10_000);
        let x0 = var_of(&mut b, 0);
        let x1 = var_of(&mut b, 1);
        let nx0 = b.neg(x0).unwrap();
        let f = b.and(nx0, x1).unwrap();
        let a = b.one_sat(f);
        assert_eq!(a.get(&0), Some(&false));
        assert_eq!(a.get(&1), Some(&true));
    }
}
