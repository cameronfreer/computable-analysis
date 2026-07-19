/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Universal
import Mathlib.Computability.Halting
import Mathlib.Topology.MetricSpace.Basic

/-!
# Coded rationals and computable metric presentations

`RatCode` codes the rationals **totally and surjectively** as unnormalized fractions:
`ratOfCode (Nat.pair (Nat.pair a b) c) = (a - b) / (c + 1)`. This coding — never
mathlib's `Encodable ℚ`/`Primcodable ℚ` — is the project's rational interface
(convention 7's thresholds and unit 16's real names both go through it): the two mathlib
instances are *different* numberings with no `Primrec`/`Computable` arithmetic lemmas,
while on `RatCode` every rational operation is `Nat.pair` arithmetic.

A `ComputableMetricPresentation` (convention 7) is an **explicit bundle** — data, never a
typeclass: a dense sequence together with uniform `REPred` *semidecisions* of both strict
rational-threshold comparisons. Semidecisions only: a decision oracle for `dist < q`
would be too strong (it decides equality of computable reals in the limit).

The presentation lives over `PseudoMetricSpace`; name decoding (unit 15's `cauchyRep`)
happens in a `MetricSpace` context, where limits are unique.
-/

namespace ComputableAnalysis

universe u

/-- Codes of rationals: bare naturals, decoded by `ratOfCode`. -/
abbrev RatCode := ℕ

/-- Total surjective decoding of a rational code as an unnormalized fraction:
`Nat.pair (Nat.pair a b) c ↦ (a - b) / (c + 1)`. -/
def ratOfCode (m : RatCode) : ℚ :=
  ((m.unpair.1.unpair.1 : ℚ) - m.unpair.1.unpair.2) / (m.unpair.2 + 1)

/-- Every rational is coded: numerator sign splits into the `a`/`b` slots and the
positive denominator lands in the `c + 1` slot. -/
theorem ratOfCode_surjective : Function.Surjective ratOfCode := by
  intro q
  refine ⟨Nat.pair (Nat.pair (q.num.toNat) ((-q.num).toNat)) (q.den - 1), ?_⟩
  have hden : 0 < q.den := q.den_pos
  rw [ratOfCode]
  simp only [Nat.unpair_pair]
  have hnum : ((q.num.toNat : ℚ)) - ((-q.num).toNat : ℚ) = (q.num : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (Int.toNat_sub_toNat_neg q.num)
  rw [hnum]
  have hd : ((q.den - 1 : ℕ) : ℚ) + 1 = (q.den : ℚ) := by
    have : (q.den - 1) + 1 = q.den := Nat.succ_pred_eq_of_pos hden
    exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) this
  rw [hd, Rat.num_div_den]

/-- A computable presentation of a (pseudo)metric space: a dense sequence with uniform
`REPred` semidecisions of both strict rational-threshold comparisons (convention 7).
Explicit data, never a typeclass. -/
structure ComputableMetricPresentation (X : Type u) [PseudoMetricSpace X] where
  /-- The dense sequence. -/
  dense : ℕ → X
  /-- Density of the sequence. -/
  denseRange : DenseRange dense
  /-- Uniform semidecision of `dist (dense i) (dense j) < q` at coded thresholds. -/
  ltSemidec : REPred fun w : ℕ × ℕ × RatCode =>
    dist (dense w.1) (dense w.2.1) < (ratOfCode w.2.2 : ℝ)
  /-- Uniform semidecision of `q < dist (dense i) (dense j)` at coded thresholds. -/
  gtSemidec : REPred fun w : ℕ × ℕ × RatCode =>
    (ratOfCode w.2.2 : ℝ) < dist (dense w.1) (dense w.2.1)

/-! ### The coded zero and the `REPred` threshold builder

When a presentation's dense-point distances are *exactly* coded — dyadic distances on
Cantor space (unit 24), coded-rational dense sequences, exact mass tables — each
convention 7 threshold comparison is a strict comparison of two primitively computed
rational codes. On codes that comparison is the decidable `Nat.pair` cross-multiplication
test, so the semidecisions come for free: `repred_of_ratLt` packages this reduction once.
`zeroCode` is the canonical coded distance of coincident dense points. -/

/-- The canonical code of `0`: the unnormalized fraction `(0 - 0) / (0 + 1)`. -/
def zeroCode : RatCode := Nat.pair (Nat.pair 0 0) 0

/-- `zeroCode` decodes to `0`. -/
theorem ratOfCode_zeroCode : ratOfCode zeroCode = 0 := by
  simp [ratOfCode, zeroCode]

private theorem primrec_unpairFst : Primrec fun m : ℕ => m.unpair.1 :=
  Primrec.fst.comp Primrec.unpair

private theorem primrec_unpairSnd : Primrec fun m : ℕ => m.unpair.2 :=
  Primrec.snd.comp Primrec.unpair

/-- Strict comparison of coded rationals is the ℕ cross-multiplication comparison. -/
private theorem ratOfCode_lt_iff (m₁ m₂ : ℕ) :
    ratOfCode m₁ < ratOfCode m₂ ↔
      m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.2 * (m₁.unpair.2 + 1)
        < m₂.unpair.1.unpair.1 * (m₁.unpair.2 + 1)
            + m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1) := by
  have h₁ : (0 : ℚ) < (m₁.unpair.2 : ℚ) + 1 := by positivity
  have h₂ : (0 : ℚ) < (m₂.unpair.2 : ℚ) + 1 := by positivity
  rw [ratOfCode, ratOfCode, div_lt_div_iff₀ h₁ h₂, sub_mul, sub_mul, sub_lt_sub_iff]
  exact_mod_cast Iff.rfl

/-- **The threshold builder.** Any predicate equivalent to a strict comparison of
primitively computed rational codes is r.e. — decidable coded-rational comparisons are
`REPred` via `PrimrecPred.computablePred.to_re`. Both semidecisions of a presentation
with exactly coded distances are instances (units 24 and 26+). -/
theorem repred_of_ratLt {q : ℕ × ℕ × RatCode → Prop} {f g : ℕ × ℕ × RatCode → ℕ}
    (hf : Primrec f) (hg : Primrec g)
    (hq : ∀ w, q w ↔ ratOfCode (f w) < ratOfCode (g w)) : REPred q := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  have hd : Primrec fun m : ℕ => m.unpair.2 + 1 := Primrec.succ.comp primrec_unpairSnd
  have hnat : PrimrecPred fun w : ℕ × ℕ × RatCode =>
      (f w).unpair.1.unpair.1 * ((g w).unpair.2 + 1)
          + (g w).unpair.1.unpair.2 * ((f w).unpair.2 + 1)
        < (g w).unpair.1.unpair.1 * ((f w).unpair.2 + 1)
            + (f w).unpair.1.unpair.2 * ((g w).unpair.2 + 1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (ha.comp hf) (hd.comp hg))
        (Primrec.nat_mul.comp (hb.comp hg) (hd.comp hf)))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (ha.comp hg) (hd.comp hf))
        (Primrec.nat_mul.comp (hb.comp hf) (hd.comp hg)))
  exact ((hnat.of_eq fun w =>
    ((ratOfCode_lt_iff (f w) (g w)).symm.trans (hq w).symm)).computablePred).to_re

end ComputableAnalysis
