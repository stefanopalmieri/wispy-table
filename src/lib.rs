//! # wispy-table
//!
//! The 32x32 Cayley table for algebraic type dispatch. 1KB. Lean-proved.
//!
//! Every type dispatch decision is a single table lookup: `CAYLEY[op][tag]`.
//! The table is `const`, lives in `.rodata` (flash on embedded), and is
//! transparent to the optimizer.
//!
//! The 12-element algebraic core encodes three independent capabilities:
//! - **Self-representation:** Q/E are mutual inverses (homoiconicity with a proof)
//! - **Self-description:** TAU classifies any value by type in one lookup
//! - **Self-execution:** RHO dispatches on the classifier, Y provides fixed points
//!
//! 14 Lean-verified theorems, zero `sorry`.
//!
//! ```
//! use wispy_table::*;
//!
//! assert_eq!(dot(CAR, T_PAIR), T_PAIR); // car of pair → valid
//! assert_eq!(dot(CAR, T_STR), BOT);     // car of string → type error
//! assert_eq!(dot(E, dot(Q, CAR)), CAR); // QE retraction round-trip
//! ```

#![cfg_attr(not(feature = "std"), no_std)]

/// Table dimension.
pub const N: usize = 32;

// ── Algebraic core (0-11) ────────────────────────────────────────

pub const TOP: u8 = 0;     // ⊤, nil, '()
pub const BOT: u8 = 1;     // ⊥, #f, type error
pub const Q: u8 = 2;       // quote / encoder
pub const E: u8 = 3;       // eval / decoder
pub const CAR: u8 = 4;     // first projection
pub const CDR: u8 = 5;     // second projection (= ρ ∘ cons)
pub const CONS: u8 = 6;    // pair constructor, core-preserving
pub const RHO: u8 = 7;     // branch (conditional dispatch)
pub const APPLY: u8 = 8;   // explicit application
pub const CC: u8 = 9;      // call/cc
pub const TAU: u8 = 10;    // classifier (type predicate)
pub const Y: u8 = 11;      // Y combinator (fixed point)

// ── R4RS type tags (12-19) ───────────────────────────────────────

pub const T_PAIR: u8 = 12;
pub const T_SYM: u8 = 13;
pub const T_CLS: u8 = 14;  // closure / procedure
pub const T_STR: u8 = 15;
pub const T_VEC: u8 = 16;
pub const T_CHAR: u8 = 17;
pub const T_CONT: u8 = 18; // first-class continuation
pub const T_PORT: u8 = 19;

// ── Special values (20-22) ───────────────────────────────────────

pub const TRUE: u8 = 20;   // #t
pub const EOF: u8 = 21;    // eof-object
pub const VOID: u8 = 22;   // void (unspecified)

// ── Core element list ────────────────────────────────────────────

pub const CORE: [u8; 10] = [Q, E, CAR, CDR, CONS, RHO, APPLY, CC, TAU, Y];
pub const TYPE_TAGS: [u8; 8] = [T_PAIR, T_SYM, T_CLS, T_STR, T_VEC, T_CHAR, T_CONT, T_PORT];

// ── The table ────────────────────────────────────────────────────

pub static CAYLEY: [[u8; 32]; 32] = [
    [ 0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0],  // ⊤
    [ 1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1],  // ⊥
    [ 2,  2,  3,  2, 11,  4,  6,  7,  9,  5,  8, 10,  0,  2,  2, 13,  2,  2,  2,  2,  2,  2,  2,  2,  0,  2,  2,  2,  2,  2,  2,  2],  // Q
    [ 0,  1,  3,  2,  5,  9,  6,  7, 10,  8, 11,  4,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0],  // E
    [ 2,  0,  1,  3,  2,  0, 10,  6,  0, 10,  0, 23, 12,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  0],  // car
    [ 1,  2,  2, 10,  6, 23, 10,  0, 10,  6,  0,  6, 12,  1,  1,  1,  1,  1,  1,  1,  1,  1,  1,  0,  0,  0,  0,  0,  0,  0,  0,  1],  // cdr
    [ 0,  2,  4,  9,  8, 11,  9, 10,  6,  8, 10,  7,  2,  2,  2,  2,  2,  2,  2,  2,  2,  0,  2,  0,  0,  0,  0,  3,  0,  2,  2,  2],  // cons
    [ 2,  2,  1,  3,  2, 11, 10,  6,  6, 10,  0, 23,  2,  2,  2,  2,  2, 31,  2,  2,  2,  2,  2,  2,  2,  2,  0,  0,  0,  0,  0, 11],  // ρ
    [ 0,  2,  4,  4, 11, 11,  7,  2,  2,  2,  0, 11,  3,  2,  2,  2,  2,  0,  2,  2,  2,  2,  2,  2,  0,  2,  2,  1,  2,  0,  2,  3],  // apply
    [ 0,  3,  4,  3,  6,  2,  2,  2, 10,  9, 11, 11,  4,  2,  2,  2,  0,  2,  3,  2,  2,  2,  2,  0,  2,  2,  2,  0,  0,  0,  2,  4],  // cc
    [ 0,  1,  0,  0,  0,  1,  0,  0,  1,  0,  0,  0, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22,  0,  1,  0,  0,  0,  0,  0,  0,  0],  // τ
    [ 2,  2,  2,  3,  9, 11,  7,  3, 10,  9,  2, 11,  0,  2,  2,  2,  2,  2,  2,  2,  2,  2, 15,  2,  2,  2,  0,  1,  3,  2,  2,  5],  // Y
    [ 0,  1, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],  // pair
    [ 0,  1, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13],  // sym
    [ 0,  1, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14],  // cls
    [ 0,  1, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15],  // str
    [ 0,  1, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16],  // vec
    [ 0,  1, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17],  // char
    [ 0,  1, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18, 18],  // cont
    [ 0,  1, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19, 19],  // port
    [ 0,  1, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20],  // #t
    [ 0,  1, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21],  // eof
    [ 0,  1, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22, 22],  // void
    [ 0, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23, 23],  // _23
    [ 0, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24],  // _24
    [ 0, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25],  // _25
    [ 0, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26],  // _26
    [ 0, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27],  // _27
    [ 0, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28],  // _28
    [ 0, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29],  // _29
    [ 0, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30],  // _30
    [ 0, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31, 31],  // _31
];

/// Apply element `a` to element `b` via the Cayley table.
#[inline(always)]
pub fn dot(a: u8, b: u8) -> u8 {
    CAYLEY[a as usize][b as usize]
}

/// Check if an operation is valid on a type (result is not BOT).
#[inline(always)]
pub fn type_valid(op: u8, tag: u8) -> bool {
    dot(op, tag) != BOT
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn absorbers() {
        for j in 0..N as u8 {
            assert_eq!(dot(TOP, j), TOP);
            assert_eq!(dot(BOT, j), BOT);
        }
    }

    #[test]
    fn extensionality() {
        let mut rows: Vec<Vec<u8>> = (0..N).map(|i| CAYLEY[i].to_vec()).collect();
        rows.sort();
        rows.dedup();
        assert_eq!(rows.len(), N);
    }

    #[test]
    fn retraction_qe() {
        for &x in &CORE {
            assert_eq!(dot(E, dot(Q, x)), x, "E(Q({x}))!={x}");
            assert_eq!(dot(Q, dot(E, x)), x, "Q(E({x}))!={x}");
        }
    }

    #[test]
    fn classifier_core() {
        for &x in &CORE {
            let tx = dot(TAU, x);
            assert!(tx == TOP || tx == BOT, "tau({x})={tx}");
        }
    }

    #[test]
    fn classifier_type_tags() {
        for &t in &TYPE_TAGS {
            assert_eq!(dot(TAU, t), t, "tau should return type tag for type {t}");
        }
    }

    #[test]
    fn branch() {
        for &x in &CORE {
            if dot(TAU, x) == TOP {
                assert_eq!(dot(RHO, x), dot(CAR, x));
            } else {
                assert_eq!(dot(RHO, x), dot(CONS, x));
            }
        }
    }

    #[test]
    fn composition() {
        for &x in &CORE {
            assert_eq!(dot(CDR, x), dot(RHO, dot(CONS, x)));
        }
    }

    #[test]
    fn y_fixed_point() {
        let yp = dot(Y, RHO);
        assert!(yp >= 2);
        assert_eq!(dot(RHO, yp), yp);
    }

    #[test]
    fn car_type_dispatch() {
        assert_eq!(dot(CAR, T_PAIR), T_PAIR);
        for &t in &TYPE_TAGS {
            if t != T_PAIR {
                assert_eq!(dot(CAR, t), BOT, "car({t}) should be error");
            }
        }
    }

    #[test]
    fn table_size() {
        assert_eq!(core::mem::size_of_val(&CAYLEY), 1024, "table should be 1KB");
    }
}
