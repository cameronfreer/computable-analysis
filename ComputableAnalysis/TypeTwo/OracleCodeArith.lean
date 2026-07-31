/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Eval

/-!
# Explicit arithmetic oracle codes

Closed first-order `OracleCode` terms for the small numeric operations that code
constructions need, each with a total evaluation law. They live here rather than behind
`Nat.Partrec.Code.exists_code` so that the consumers depending on them stay **axiom-free**:
`#print axioms` is empty for every definition in this file.

* projection helpers on paired inputs (`eval_left_pair`, `eval_right_pair`,
  `eval_right_right_pair`);
* `addCode`, `predCode`, `subCode` (truncated), `doubleCode`;
* `caseszCode`, a case split on a paired flag;
* `div2mod2Code`, division and remainder by two jointly.

These codes sit **below the stream/continuity layer**: they need only coordinate-level
evaluation, so this module imports `TypeTwo.Eval` rather than `TypeTwo.Continuity`.

Consumers so far: the track kit of `TypeTwo/Tracks.lean` (index rewirings) and the
`Lim`/`LPO` calibration (`Weihrauch/Principles/LimParallelizeLPO.lean`, whose stability
questions need a `≠` test built from truncated subtraction).
-/

namespace ComputableAnalysis

namespace OracleCode

/-- `left` on a paired input, with the projection computed. -/
theorem eval_left_pair (p : Baire) (a b : ℕ) :
    OracleCode.left.eval p (Nat.pair a b) = Part.some a := by
  rw [eval_left, Nat.unpair_pair]

/-- `right` on a paired input, with the projection computed. -/
theorem eval_right_pair (p : Baire) (a b : ℕ) :
    OracleCode.right.eval p (Nat.pair a b) = Part.some b := by
  rw [eval_right, Nat.unpair_pair]

/-- The double right projection on a doubly paired input. -/
theorem eval_right_right_pair (p : Baire) (a b c : ℕ) :
    (comp right right).eval p (Nat.pair a (Nat.pair b c)) = Part.some c := by
  rw [eval_comp_some (eval_right_pair p a (Nat.pair b c)), eval_right_pair]

/-- Addition on a paired input: `Nat.pair a b ↦ a + b`, by primitive recursion on `b`. -/
def addCode : OracleCode := prec .id (comp succ (comp right right))

theorem eval_addCode (p : Baire) (a b : ℕ) :
    addCode.eval p (Nat.pair a b) = Part.some (a + b) := by
  induction b with
  | zero => simp [addCode]
  | succ b ih =>
      simp only [addCode] at ih ⊢
      rw [eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some,
        eval_comp_some (eval_right_right_pair p a b (a + b)), eval_succ]
      exact congrArg Part.some (by omega)

/-- Predecessor: `k ↦ k - 1`, by primitive recursion. -/
def predCode : OracleCode := comp (prec zero (comp left right)) (pair zero .id)

theorem eval_predCode (p : Baire) (k : ℕ) : predCode.eval p k = Part.some (k - 1) := by
  simp only [predCode]
  rw [eval_comp_some (show (pair zero .id).eval p k = Part.some (Nat.pair 0 k) by
    simp [Seq.seq, pure, PFun.pure])]
  induction k with
  | zero => rw [eval_prec_zero]; rfl
  | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some,
        eval_comp_some (eval_right_pair p 0 (Nat.pair k (k - 1))), eval_left_pair]
      exact congrArg Part.some (by omega)

/-- Truncated subtraction on a paired input: `Nat.pair a b ↦ a - b`, by primitive
recursion on `b`. -/
def subCode : OracleCode := prec .id (comp predCode (comp right right))

theorem eval_subCode (p : Baire) (a b : ℕ) :
    subCode.eval p (Nat.pair a b) = Part.some (a - b) := by
  induction b with
  | zero => simp [subCode]
  | succ b ih =>
      simp only [subCode] at ih ⊢
      rw [eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some,
        eval_comp_some (eval_right_right_pair p a b (a - b)), eval_predCode]
      exact congrArg Part.some (by omega)

/-- Doubling: `m ↦ 2 * m`, as addition of `m` with itself. -/
def doubleCode : OracleCode := comp addCode (pair .id .id)

theorem eval_doubleCode (p : Baire) (m : ℕ) : doubleCode.eval p m = Part.some (2 * m) := by
  simp only [doubleCode]
  rw [eval_comp_some (show (pair .id .id).eval p m = Part.some (Nat.pair m m) by
    simp [Seq.seq]), eval_addCode, two_mul]

/-- Case split on a paired flag: on `Nat.pair x 0` run `cthen` on `x`; on `Nat.pair x (r+1)`
run `celse` on `x` (provided `cthen` converges at `x`, which primitive recursion consults
once). -/
def caseszCode (cthen celse : OracleCode) : OracleCode := prec cthen (comp celse left)

theorem eval_caseszCode_zero (cthen celse : OracleCode) (p : Baire) (x : ℕ) :
    (caseszCode cthen celse).eval p (Nat.pair x 0) = cthen.eval p x :=
  eval_prec_zero ..

theorem eval_caseszCode_one {cthen : OracleCode} (celse : OracleCode) {p : Baire} {x v : ℕ}
    (h : cthen.eval p x = Part.some v) :
    (caseszCode cthen celse).eval p (Nat.pair x 1) = celse.eval p x := by
  simp only [caseszCode]
  rw [eval_prec_succ, eval_prec_zero, h, Part.bind_eq_bind, Part.bind_some]
  rw [eval_comp_some (show OracleCode.left.eval p (Nat.pair x (Nat.pair 0 v)) = Part.some x by
    simp [Nat.unpair_pair])]

/-- The step code of `div2mod2Code`: from the running pair `⟨q, r⟩` (quotient and 2-remainder
so far) produce `⟨q, 1⟩` if `r = 0` and `⟨q + 1, 0⟩` otherwise. -/
private def div2mod2Step : OracleCode :=
  comp (caseszCode (pair left (.const 1)) (pair (comp succ left) zero))
    (pair (comp right right) (comp right (comp right right)))

private theorem eval_div2mod2Step (p : Baire) (a y q r : ℕ) (hr : r ≤ 1) :
    div2mod2Step.eval p (Nat.pair a (Nat.pair y (Nat.pair q r))) =
      Part.some (if r = 0 then Nat.pair q 1 else Nat.pair (q + 1) 0) := by
  simp only [div2mod2Step]
  rw [eval_comp_some (show (pair (comp right right) (comp right (comp right right))).eval p
      (Nat.pair a (Nat.pair y (Nat.pair q r))) = Part.some (Nat.pair (Nat.pair q r) r) from
    eval_pair_some (eval_right_right_pair ..)
      (by rw [eval_comp_some (eval_right_right_pair p a y (Nat.pair q r)), eval_right_pair]))]
  obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.mp hr
  · rw [eval_caseszCode_zero, if_pos rfl]
    exact eval_pair_some (eval_left_pair ..) (eval_const ..)
  · rw [eval_caseszCode_one _
      (eval_pair_some (eval_left_pair p q 1) (eval_const p 1 (Nat.pair q 1))), if_neg one_ne_zero]
    exact eval_pair_some (by rw [eval_comp_some (eval_left_pair p q 1), eval_succ]) rfl

/-- Division and remainder by two, jointly: `k ↦ Nat.pair (k / 2) (k % 2)`. -/
def div2mod2Code : OracleCode := comp (prec zero div2mod2Step) (pair zero .id)

theorem eval_div2mod2Code (p : Baire) (k : ℕ) :
    div2mod2Code.eval p k = Part.some (Nat.pair (k / 2) (k % 2)) := by
  simp only [div2mod2Code]
  rw [eval_comp_some (show (pair zero .id).eval p k = Part.some (Nat.pair 0 k) by
    simp [Seq.seq, pure, PFun.pure])]
  induction k with
  | zero => rw [eval_prec_zero]; rfl
  | succ k ih =>
      rw [eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some,
        eval_div2mod2Step p 0 k (k / 2) (k % 2) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one k with h | h
      · have h1 : (k + 1) / 2 = k / 2 := by omega
        have h2 : (k + 1) % 2 = 1 := by omega
        rw [if_pos h, h1, h2]
      · have h1 : (k + 1) / 2 = k / 2 + 1 := by omega
        have h2 : (k + 1) % 2 = 0 := by omega
        rw [if_neg (by omega), h1, h2]

end OracleCode

end ComputableAnalysis
