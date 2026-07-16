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

end ComputableAnalysis
