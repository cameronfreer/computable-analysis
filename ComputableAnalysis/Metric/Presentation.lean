/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.REPredClosure
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

/-- **The comparison builder.** Strict comparison of primitively computed rational codes is
a `PrimrecPred`: the coding puts it at cross-multiplication of the numerator and denominator
projections, all of them primitive recursive. Every decision a realizer makes about coded
rationals — thresholds, majority tests, sign tests — factors through this. -/
theorem primrecPred_ratLt {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred fun a => ratOfCode (f a) < ratOfCode (g a) := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  have hd : Primrec fun m : ℕ => m.unpair.2 + 1 := Primrec.succ.comp primrec_unpairSnd
  have hnat : PrimrecPred fun a : α =>
      (f a).unpair.1.unpair.1 * ((g a).unpair.2 + 1)
          + (g a).unpair.1.unpair.2 * ((f a).unpair.2 + 1)
        < (g a).unpair.1.unpair.1 * ((f a).unpair.2 + 1)
            + (f a).unpair.1.unpair.2 * ((g a).unpair.2 + 1) :=
    Primrec.nat_lt.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (ha.comp hf) (hd.comp hg))
        (Primrec.nat_mul.comp (hb.comp hg) (hd.comp hf)))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (ha.comp hg) (hd.comp hf))
        (Primrec.nat_mul.comp (hb.comp hf) (hd.comp hg)))
  exact hnat.of_eq fun a => (ratOfCode_lt_iff (f a) (g a)).symm

/-- **The threshold builder.** Any predicate equivalent to a strict comparison of
primitively computed rational codes is r.e. — decidable coded-rational comparisons are
`REPred` via `PrimrecPred.computablePred.to_re`. Both semidecisions of a presentation
with exactly coded distances are instances (units 24 and 26+). -/
theorem repred_of_ratLt {q : ℕ × ℕ × RatCode → Prop} {f g : ℕ × ℕ × RatCode → ℕ}
    (hf : Primrec f) (hg : Primrec g)
    (hq : ∀ w, q w ↔ ratOfCode (f w) < ratOfCode (g w)) : REPred q :=
  (((primrecPred_ratLt hf hg).of_eq fun w => (hq w).symm).computablePred).to_re

/-! ### The presented product (the product slice of deferred unit 17) -/

section Prod

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

namespace ComputableMetricPresentation

/-- Separability of a presented space, from the dense sequence. -/
theorem separableSpace (P : ComputableMetricPresentation X) :
    TopologicalSpace.SeparableSpace X :=
  ⟨⟨Set.range P.dense, Set.countable_range _, P.denseRange⟩⟩

/-- The `X`-side comparison triple of a product-comparison triple.

Binding discipline: state the `repred_comp` results with `fstTriple`/`sndTriple` still
*applied* (rather than hand-projected `w.1.unpair.1` forms) — asking the unifier for the
defeq `(fstTriple w).1 ≡ w.1.unpair.1` inside the `REPred` lambda sends it into a
`Nat.unpair`/`Nat.sqrt` whnf explosion (deterministic timeout); the conversion to the
product-distance shape must be a *directed* `simp only [fstTriple, sndTriple,
Prod.dist_eq, …]` rewrite. -/
private def fstTriple (w : ℕ × ℕ × RatCode) : ℕ × ℕ × RatCode :=
  (w.1.unpair.1, w.2.1.unpair.1, w.2.2)

/-- The `Y`-side comparison triple of a product-comparison triple. -/
private def sndTriple (w : ℕ × ℕ × RatCode) : ℕ × ℕ × RatCode :=
  (w.1.unpair.2, w.2.1.unpair.2, w.2.2)

private theorem computable_fstTriple : Computable fstTriple :=
  (((Primrec.fst.comp Primrec.unpair).comp Primrec.fst).pair
    (((Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))).to_comp

private theorem computable_sndTriple : Computable sndTriple :=
  (((Primrec.snd.comp Primrec.unpair).comp Primrec.fst).pair
    (((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))).to_comp

/-- **The presented product** (the product slice of deferred unit 17): dense sequence
`Nat.pair i j ↦ (P.dense i, Q.dense j)` against the max metric (`Prod.dist_eq`); the
`lt` semidecision is the conjunction of the factors' (`max < q`), the `gt` semidecision
the disjunction (`q < max`), through the `REPred` closure riders `repred_and` /
`repred_or` / `repred_comp`. -/
def prod (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y) :
    ComputableMetricPresentation (X × Y) where
  dense n := (P.dense n.unpair.1, Q.dense n.unpair.2)
  denseRange := by
    rw [Metric.denseRange_iff]
    intro z ε hε
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.denseRange z.1 ε hε
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp Q.denseRange z.2 ε hε
    refine ⟨Nat.pair i j, ?_⟩
    rw [Prod.dist_eq]
    simp only [Nat.unpair_pair]
    exact max_lt hi hj
  ltSemidec := by
    have hP : REPred fun w : ℕ × ℕ × RatCode =>
        dist (P.dense (fstTriple w).1) (P.dense (fstTriple w).2.1)
          < (ratOfCode (fstTriple w).2.2 : ℝ) :=
      repred_comp P.ltSemidec computable_fstTriple
    have hQ : REPred fun w : ℕ × ℕ × RatCode =>
        dist (Q.dense (sndTriple w).1) (Q.dense (sndTriple w).2.1)
          < (ratOfCode (sndTriple w).2.2 : ℝ) :=
      repred_comp Q.ltSemidec computable_sndTriple
    have hpred : (fun w : ℕ × ℕ × RatCode =>
          (dist (P.dense (fstTriple w).1) (P.dense (fstTriple w).2.1)
              < (ratOfCode (fstTriple w).2.2 : ℝ))
            ∧ dist (Q.dense (sndTriple w).1) (Q.dense (sndTriple w).2.1)
              < (ratOfCode (sndTriple w).2.2 : ℝ))
        = fun w : ℕ × ℕ × RatCode =>
            dist ((P.dense w.1.unpair.1, Q.dense w.1.unpair.2) : X × Y)
              (P.dense w.2.1.unpair.1, Q.dense w.2.1.unpair.2) < (ratOfCode w.2.2 : ℝ) := by
      funext w
      simp only [fstTriple, sndTriple, Prod.dist_eq, max_lt_iff]
    exact hpred ▸ repred_and hP hQ
  gtSemidec := by
    have hP : REPred fun w : ℕ × ℕ × RatCode =>
        (ratOfCode (fstTriple w).2.2 : ℝ)
          < dist (P.dense (fstTriple w).1) (P.dense (fstTriple w).2.1) :=
      repred_comp P.gtSemidec computable_fstTriple
    have hQ : REPred fun w : ℕ × ℕ × RatCode =>
        (ratOfCode (sndTriple w).2.2 : ℝ)
          < dist (Q.dense (sndTriple w).1) (Q.dense (sndTriple w).2.1) :=
      repred_comp Q.gtSemidec computable_sndTriple
    have hpred : (fun w : ℕ × ℕ × RatCode =>
          ((ratOfCode (fstTriple w).2.2 : ℝ)
              < dist (P.dense (fstTriple w).1) (P.dense (fstTriple w).2.1))
            ∨ (ratOfCode (sndTriple w).2.2 : ℝ)
              < dist (Q.dense (sndTriple w).1) (Q.dense (sndTriple w).2.1))
        = fun w : ℕ × ℕ × RatCode =>
            (ratOfCode w.2.2 : ℝ)
              < dist ((P.dense w.1.unpair.1, Q.dense w.1.unpair.2) : X × Y)
                  (P.dense w.2.1.unpair.1, Q.dense w.2.1.unpair.2) := by
      funext w
      simp only [fstTriple, sndTriple, Prod.dist_eq, lt_max_iff]
    exact hpred ▸ repred_or hP hQ

end ComputableMetricPresentation

end Prod

end ComputableAnalysis
