/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.Conditioning
import ComputableAnalysis.Measure.Integration
import ComputableAnalysis.Metric.RatCodeArith
import Mathlib.Probability.Kernel.WithDensity

/-!
# Positive conditioning: the bounded-Lipschitz, everywhere-positive specialization

Unit 37 (part B of the conditioning layer): conditioning **is** computable when the joint
law carries a bounded-Lipschitz, everywhere-positive conditional density.  This is the
bounded-Lipschitz, everywhere-positive **specialization** of Ackerman–Freer–Roy,
"On the computability of conditional probability" (J. ACM 66(3), 2019), Proposition 9.4 —
NOT the paper's exact hypotheses: the paper assumes a positive bounded computable
conditional density, and bounded-Lipschitz is strictly narrower.  The full
computable-density and independent-noise corollaries are deferred.

The library conditions Y given X (AFR dictionary `(X, Y) = (T, S)`): the observed
variable is the first coordinate, the "prior" is the second marginal `ν = μ.snd`, and the
density datum is a single two-variable bounded-Lipschitz function `q` on the presented
product with the pinned identity `μ = (ρ ⊗ ν).withDensity q` for some σ-finite reference
measure `ρ` on X.  Nonnegativity of `q` is an explicit conjunct of the hypothesis package
`IsCondDensityPair` — the density is genuinely `q` itself, never a silent
`ENNReal.ofReal` clamp.

* `bayesZ`, `bayesKernel`, `disintegrate_bayesKernel`, `isCondKernel_bayesKernel` — the
  fully proved mathematical layer: the Bayes-ratio kernel
  `κ x = (q (x, ·) / Z x) · ν` disintegrates the joint law over its first marginal,
  through mathlib's own `Measure.IsCondKernel`.
* `IsCondDensityPair` — the frozen hypothesis package; `IsCondDensityPair.isCondKernel`
  discharges the blueprint version relation, and `bayesLaw` is the produced conditional.
* `BoundedLipschitzFun.slice`, `sndMarginal`, `reweight` and their computability
  theorems `computableMap_blSlice`, `computableMap_sndMarginal`,
  `computableMap_reweight` — the three realizer stages: slice the density at the
  observed point, project the joint name to the prior's weak name, and normalize the
  bounded-Lipschitz reweighting.  The normalizer's positivity is Σ₁ from the names (an
  `rfind` search through the frozen integration operation certifies a rational lower
  bound with NO modulus datum, the same search pattern as `computableMap_realInv_pos`);
  the division by the normalizer is exact coded-rational arithmetic inside the emitted
  atomic weights.
* `computableMap_bayesCond` — the uncurried positive theorem: from a name of the
  density–joint-law pair (the subtype representation `densityPairRep`) and a name of the
  point, the conditional law `bayesLaw` is computed as a weak measure name.
* `computableMap_bayesCond_curried` — the curried headline: the map into the
  `condFunSpace` function space is computable, and the output is
  `(Condition P Q).accepts`-ed at the pair's joint law (with everywhere — not just
  a.e. — agreement).

Implementation notes.  The coded-rational combinators come from
`Metric/RatCodeArith.lean`; the clamped-weight evaluation lemmas and the sign/fusion
riders on top of them are still private re-derivations of other units' private helpers
(units 27/28/31/33 carry their own copies).  The Lévy–Prokhorov stability of
normalized reweighting (`levyProkhorovDist_reweight_le`) is proved by the same
superlevel-set/interval-integral engine as unit 31's Prokhorov stability estimate,
applied to restricted measures.
-/

set_option linter.style.longFile 2500

namespace ComputableAnalysis

open MeasureTheory ProbabilityTheory Metric Encodable Denumerable OracleCode
open scoped ENNReal NNReal

/-! ### The Bayes normalizer and the Bayes-ratio kernel (generic measurable spaces) -/

section MathLayer

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The Bayes normalizer: `Z x = ∫⁻ y, q (x, y) ∂ν` (AFR's marginal density `p_T` of the
conditioning variable, up to the reference measure). -/
noncomputable def bayesZ (ν : Measure Y) (q : X × Y → ℝ) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (q (x, y)) ∂ν

/-- The Bayes normalizer is measurable in the conditioning point. -/
theorem measurable_bayesZ (ν : Measure Y) [SFinite ν] {q : X × Y → ℝ}
    (hq : Measurable q) : Measurable (bayesZ ν q) :=
  Measurable.lintegral_prod_right' (ENNReal.measurable_ofReal.comp hq)

omit [MeasurableSpace X] in
/-- Boundedness of the density makes the normalizer finite (the bounded-Lipschitz
package's bound head discharges the finiteness hypothesis of the version relation). -/
theorem bayesZ_ne_top_of_bound (ν : Measure Y) [IsFiniteMeasure ν] {q : X × Y → ℝ}
    {B : ℕ} (hB : ∀ z, |q z| ≤ (B : ℝ)) (x : X) : bayesZ ν q x ≠ ∞ := by
  have hle : bayesZ ν q x ≤ ENNReal.ofReal (B : ℝ) * ν Set.univ :=
    calc bayesZ ν q x
        ≤ ∫⁻ _, ENNReal.ofReal (B : ℝ) ∂ν :=
          lintegral_mono fun y =>
            ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hB (x, y)))
      _ = ENNReal.ofReal (B : ℝ) * ν Set.univ := lintegral_const _
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν Set.univ)) hle

/-- **The Bayes-ratio kernel**: `κ x = (q (x, ·) / Z x) · ν`, through mathlib's
`Kernel.withDensity` over the constant kernel at the prior `ν`. -/
noncomputable def bayesKernel (ν : Measure Y) [SFinite ν] (q : X × Y → ℝ) :
    Kernel X Y :=
  Kernel.withDensity (Kernel.const X ν) fun x y =>
    ENNReal.ofReal (q (x, y)) / bayesZ ν q x

private theorem measurable_bayesRatio (ν : Measure Y) [SFinite ν] {q : X × Y → ℝ}
    (hq : Measurable q) :
    Measurable (Function.uncurry fun x y =>
      ENNReal.ofReal (q (x, y)) / bayesZ ν q x) := by
  have h1 : Measurable fun z : X × Y => ENNReal.ofReal (q z) :=
    ENNReal.measurable_ofReal.comp hq
  exact h1.div ((measurable_bayesZ ν hq).comp measurable_fst)

/-- The Bayes-ratio kernel at a point is the prior reweighted by the density ratio. -/
theorem bayesKernel_apply (ν : Measure Y) [SFinite ν] {q : X × Y → ℝ}
    (hq : Measurable q) (x : X) :
    bayesKernel ν q x
      = ν.withDensity fun y => ENNReal.ofReal (q (x, y)) / bayesZ ν q x := by
  rw [bayesKernel, Kernel.withDensity_apply _ (measurable_bayesRatio ν hq),
    Kernel.const_apply]

private theorem bayesKernel_apply_set (ν : Measure Y) [SFinite ν] {q : X × Y → ℝ}
    (hq : Measurable q) (x : X) {s : Set Y} (hs : MeasurableSet s)
    (h0 : bayesZ ν q x ≠ 0) :
    bayesKernel ν q x s
      = (∫⁻ y in s, ENNReal.ofReal (q (x, y)) ∂ν) * (bayesZ ν q x)⁻¹ := by
  rw [bayesKernel_apply ν hq x, withDensity_apply _ hs]
  simp_rw [div_eq_mul_inv]
  exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr h0)

/-- The Bayes-ratio kernel is Markov whenever the normalizer is everywhere nonzero and
finite. -/
theorem isMarkovKernel_bayesKernel {ν : Measure Y} [SFinite ν] {q : X × Y → ℝ}
    (hq : Measurable q) (h0 : ∀ x, bayesZ ν q x ≠ 0)
    (htop : ∀ x, bayesZ ν q x ≠ ∞) : IsMarkovKernel (bayesKernel ν q) := by
  refine ⟨fun x => ⟨?_⟩⟩
  rw [bayesKernel_apply_set ν hq x MeasurableSet.univ (h0 x), Measure.restrict_univ]
  exact ENNReal.mul_inv_cancel (h0 x) (htop x)

/-- The first marginal of a product-with-density is the reference measure with the
normalizer as density (Tonelli). -/
private theorem fst_withDensity_prod (ρ : Measure X) [SFinite ρ] (ν : Measure Y)
    [SFinite ν] {q : X × Y → ℝ} (hq : Measurable q) :
    ((ρ.prod ν).withDensity fun z => ENNReal.ofReal (q z)).fst
      = ρ.withDensity (bayesZ ν q) := by
  have hmeas : Measurable fun z : X × Y => ENNReal.ofReal (q z) :=
    ENNReal.measurable_ofReal.comp hq
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (measurable_fst hs),
    withDensity_apply _ hs]
  calc ∫⁻ z in Prod.fst ⁻¹' s, ENNReal.ofReal (q z) ∂(ρ.prod ν)
      = ∫⁻ z, (Prod.fst ⁻¹' s).indicator (fun z => ENNReal.ofReal (q z)) z
          ∂(ρ.prod ν) :=
        (lintegral_indicator (measurable_fst hs) _).symm
    _ = ∫⁻ x, ∫⁻ y, (Prod.fst ⁻¹' s).indicator
          (fun z => ENNReal.ofReal (q z)) (x, y) ∂ν ∂ρ :=
        lintegral_prod _ ((hmeas.indicator (measurable_fst hs)).aemeasurable)
    _ = ∫⁻ x, s.indicator (bayesZ ν q) x ∂ρ := by
        refine lintegral_congr fun x => ?_
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx]
          exact lintegral_congr fun y =>
            Set.indicator_of_mem (Set.mem_preimage.mpr hx) _
        · rw [Set.indicator_of_notMem hx]
          exact (lintegral_congr fun y =>
            Set.indicator_of_notMem (fun h => hx (Set.mem_preimage.mp h)) _).trans
            lintegral_zero
    _ = ∫⁻ x in s, bayesZ ν q x ∂ρ := lintegral_indicator hs _

/-- **The Bayes-ratio disintegration** (the version relation): if the joint law is the
product-with-density `q · (ρ ⊗ ν)` and the normalizer is everywhere nonzero and finite,
the Bayes-ratio kernel disintegrates it over its first marginal. -/
theorem disintegrate_bayesKernel (ρ : Measure X) [SFinite ρ] {ν : Measure Y}
    [SFinite ν] {μ : Measure (X × Y)} {q : X × Y → ℝ} (hq : Measurable q)
    (hμ : μ = (ρ.prod ν).withDensity fun z => ENNReal.ofReal (q z))
    (h0 : ∀ x, bayesZ ν q x ≠ 0) (htop : ∀ x, bayesZ ν q x ≠ ∞) :
    μ.fst ⊗ₘ bayesKernel ν q = μ := by
  subst hμ
  have hmk : IsMarkovKernel (bayesKernel ν q) := isMarkovKernel_bayesKernel hq h0 htop
  have hmeas : Measurable fun z : X × Y => ENNReal.ofReal (q z) :=
    ENNReal.measurable_ofReal.comp hq
  ext s hs
  rw [Measure.compProd_apply hs, fst_withDensity_prod ρ ν hq,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_bayesZ ν hq)
      (Kernel.measurable_kernel_prodMk_left hs)]
  calc ∫⁻ x, (bayesZ ν q * fun x => bayesKernel ν q x (Prod.mk x ⁻¹' s)) x ∂ρ
      = ∫⁻ x, ∫⁻ y in Prod.mk x ⁻¹' s, ENNReal.ofReal (q (x, y)) ∂ν ∂ρ := by
        refine lintegral_congr fun x => ?_
        rw [Pi.mul_apply, bayesKernel_apply_set ν hq x
          (hs.preimage measurable_prodMk_left) (h0 x), mul_left_comm,
          ENNReal.mul_inv_cancel (h0 x) (htop x), mul_one]
    _ = ((ρ.prod ν).withDensity fun z => ENNReal.ofReal (q z)) s := by
        rw [withDensity_apply _ hs, ← lintegral_indicator hs,
          lintegral_prod _ ((hmeas.indicator hs).aemeasurable)]
        refine lintegral_congr fun x => ?_
        rw [← lintegral_indicator (hs.preimage measurable_prodMk_left)]
        refine lintegral_congr fun y => ?_
        by_cases hxy : (x, y) ∈ s
        · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hxy),
            Set.indicator_of_mem hxy]
        · rw [Set.indicator_of_notMem (fun h => hxy (Set.mem_preimage.mp h)),
            Set.indicator_of_notMem hxy]

/-- **The Bayes kernel is a version of the conditional**, through mathlib's own
`Measure.IsCondKernel` proposition (orientation `μ.fst ⊗ₘ κ = μ`, matching the
library's Y-given-X convention). -/
theorem isCondKernel_bayesKernel (ρ : Measure X) [SFinite ρ] {ν : Measure Y}
    [SFinite ν] {μ : Measure (X × Y)} {q : X × Y → ℝ} (hq : Measurable q)
    (hμ : μ = (ρ.prod ν).withDensity fun z => ENNReal.ofReal (q z))
    (h0 : ∀ x, bayesZ ν q x ≠ 0) (htop : ∀ x, bayesZ ν q x ≠ ∞) :
    μ.IsCondKernel (bayesKernel ν q) :=
  ⟨disintegrate_bayesKernel ρ hq hμ h0 htop⟩

end MathLayer

/-! ### The frozen hypothesis package and the produced conditional law -/

section Pinned

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [BorelSpace X] [BorelSpace Y] in
/-- **The pinned part-B hypothesis package** (the bounded-Lipschitz, everywhere-positive
specialization of AFR's positive-theorem hypotheses): the joint law `μ` carries a
conditional density of X given Y with respect to SOME σ-finite reference measure `ρ` on
X, presented as a two-variable bounded-Lipschitz datum `q` (the carrier of
`blRep (P.prod Q)`), nonnegative everywhere, with everywhere-positive Bayes normalizer.

Pin notes:
* `μ = (ρ ⊗ μ.snd).withDensity q` IS "q is a conditional density of the first coordinate
  given the second, with the second marginal as prior" — the a.e. normalization
  `∫ q (·, y) dρ = 1` follows and is not a separate conjunct;
* nonnegativity `∀ z, 0 ≤ q z` is an explicit conjunct — the density is genuinely `q`
  itself, never a silent `ENNReal.ofReal` clamp;
* normalizer positivity is pointwise (`Z x ≠ 0`, AFR's `p_T(t) > 0`); no uniform rational
  lower bound is pinned — positivity is Σ₁ from the names, so the realizer searches for
  its own certificate;
* finiteness `Z x ≠ ∞` is derived from the bounded-Lipschitz bound head
  (`bayesZ_ne_top_of_bound`), not a conjunct;
* `ρ` is existential and propositional: the Bayes algorithm never touches it (both
  integrals in the ratio are against `μ.snd`). -/
def IsCondDensityPair (μ : ProbabilityMeasure (X × Y))
    (q : BoundedLipschitzFun (X × Y)) : Prop :=
  ∃ ρ : Measure X, SFinite ρ ∧
    μ.toMeasure
      = (ρ.prod μ.toMeasure.snd).withDensity
          (fun z => ENNReal.ofReal (q.toFun z)) ∧
    (∀ z, 0 ≤ q.toFun z) ∧
    ∀ x, bayesZ μ.toMeasure.snd q.toFun x ≠ 0

namespace IsCondDensityPair

variable {μ : ProbabilityMeasure (X × Y)} {q : BoundedLipschitzFun (X × Y)}

omit [BorelSpace X] [BorelSpace Y] in
/-- The normalizer of the pinned package is everywhere nonzero. -/
theorem bayesZ_ne_zero (h : IsCondDensityPair μ q) (x : X) :
    bayesZ μ.toMeasure.snd q.toFun x ≠ 0 := by
  obtain ⟨ρ, -, -, -, h0⟩ := h
  exact h0 x

omit [BorelSpace X] [BorelSpace Y] in
/-- The density datum of the pinned package is everywhere nonnegative. -/
theorem nonneg (h : IsCondDensityPair μ q) (z : X × Y) : 0 ≤ q.toFun z := by
  obtain ⟨ρ, -, -, hnn, -⟩ := h
  exact hnn z

omit [BorelSpace X] [BorelSpace Y] in
/-- The normalizer of the pinned package is everywhere finite. -/
theorem bayesZ_ne_top (_h : IsCondDensityPair μ q) (x : X) :
    bayesZ μ.toMeasure.snd q.toFun x ≠ ∞ := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  obtain ⟨L, B, hL, hB⟩ := q.exists_bounds
  exact bayesZ_ne_top_of_bound μ.toMeasure.snd hB x

/-- **The pinned package discharges the version relation**: the Bayes-ratio kernel is a
Markov conditional kernel of the joint law, in the blueprint's `IsCondKernel` sense.
Second countability of the observed factor (automatic over a presentation, through
`ComputableMetricPresentation.separableSpace`) links the Lipschitz continuity of the
density datum to product-σ-algebra measurability. -/
theorem isCondKernel [SecondCountableTopology X] (h : IsCondDensityPair μ q) :
    IsCondKernel μ (bayesKernel μ.toMeasure.snd q.toFun) := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  have htop : ∀ x, bayesZ μ.toMeasure.snd q.toFun x ≠ ∞ := h.bayesZ_ne_top
  obtain ⟨ρ, hsf, hjoint, hnn, h0⟩ := h
  haveI := hsf
  obtain ⟨L, B, hL, hB⟩ := q.exists_bounds
  have hq : Measurable q.toFun := hL.continuous.measurable
  exact ⟨isMarkovKernel_bayesKernel hq h0 htop,
    isCondKernel_bayesKernel ρ hq hjoint h0 htop⟩

end IsCondDensityPair

/-- The conditional law produced by the Bayes route, as a probability measure: the prior
`ν = μ.snd` reweighted by the density slice `q (x, ·)` and normalized by the Bayes
normalizer.  Stated at the measure level (only the slice's measurability in `Y` is
consumed); `bayesLaw_toMeasure_eq_bayesKernel` identifies it with the Bayes-ratio
kernel. -/
noncomputable def bayesLaw (μ : ProbabilityMeasure (X × Y))
    (q : BoundedLipschitzFun (X × Y)) (h : IsCondDensityPair μ q) (x : X) :
    ProbabilityMeasure Y := by
  refine ⟨(bayesZ μ.toMeasure.snd q.toFun x)⁻¹ •
    μ.toMeasure.snd.withDensity (fun y => ENNReal.ofReal (q.toFun (x, y))), ⟨?_⟩⟩
  have hZ : μ.toMeasure.snd.withDensity
      (fun y => ENNReal.ofReal (q.toFun (x, y))) Set.univ
        = bayesZ μ.toMeasure.snd q.toFun x := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, bayesZ]
  rw [Measure.smul_apply, hZ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (h.bayesZ_ne_zero x) (h.bayesZ_ne_top x)

omit [BorelSpace X] [BorelSpace Y] in
/-- The produced conditional law, unbundled: the normalized slice reweighting. -/
theorem bayesLaw_toMeasure {μ : ProbabilityMeasure (X × Y)}
    {q : BoundedLipschitzFun (X × Y)} (h : IsCondDensityPair μ q) (x : X) :
    (bayesLaw μ q h x).toMeasure
      = (bayesZ μ.toMeasure.snd q.toFun x)⁻¹ •
          μ.toMeasure.snd.withDensity (fun y => ENNReal.ofReal (q.toFun (x, y))) := rfl

/-- Under product-σ-algebra measurability of the density (automatic over a
presentation), the produced conditional law is exactly the Bayes-ratio kernel. -/
theorem bayesLaw_toMeasure_eq_bayesKernel [SecondCountableTopology X]
    {μ : ProbabilityMeasure (X × Y)} {q : BoundedLipschitzFun (X × Y)}
    (h : IsCondDensityPair μ q) (x : X) :
    (bayesLaw μ q h x).toMeasure = bayesKernel μ.toMeasure.snd q.toFun x := by
  obtain ⟨L, B, hL, hB⟩ := q.exists_bounds
  have hq : Measurable q.toFun := hL.continuous.measurable
  have hslice : Measurable fun y => ENNReal.ofReal (q.toFun (x, y)) :=
    (ENNReal.measurable_ofReal.comp hq).comp measurable_prodMk_left
  rw [bayesLaw_toMeasure, bayesKernel_apply _ hq]
  have hfun : (fun y => ENNReal.ofReal (q.toFun (x, y)) / bayesZ μ.toMeasure.snd q.toFun x)
      = (bayesZ μ.toMeasure.snd q.toFun x)⁻¹ •
          fun y => ENNReal.ofReal (q.toFun (x, y)) := by
    funext y
    rw [Pi.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul]
  rw [hfun, withDensity_smul _ hslice]

end Pinned

/-! ### The carrier maps of the Bayes route: slice, second marginal, reweighting -/

section Carriers

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The slice of a two-variable bounded-Lipschitz function at an observed first
coordinate, with the same Lipschitz and bound certificates (the section
`y ↦ (x, y)` is `1`-Lipschitz for the max product metric). -/
def BoundedLipschitzFun.slice (q : BoundedLipschitzFun (X × Y)) (x : X) :
    BoundedLipschitzFun Y where
  toFun y := q.toFun (x, y)
  exists_bounds := by
    obtain ⟨L, B, hL, hB⟩ := q.exists_bounds
    refine ⟨L, B, ?_, fun y => hB (x, y)⟩
    simpa [Function.comp_def] using hL.comp (LipschitzWith.prodMk_left x)

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The slice applies as the section of the underlying function. -/
@[simp]
theorem BoundedLipschitzFun.slice_apply (q : BoundedLipschitzFun (X × Y)) (x : X)
    (y : Y) : (q.slice x).toFun y = q.toFun (x, y) := rfl

omit [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The second marginal of a joint probability law, bundled. -/
noncomputable def sndMarginal (μ : ProbabilityMeasure (X × Y)) :
    ProbabilityMeasure Y := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  exact ⟨μ.toMeasure.snd, inferInstance⟩

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The bundled second marginal is `Measure.snd`. -/
@[simp]
theorem sndMarginal_toMeasure (μ : ProbabilityMeasure (X × Y)) :
    (sndMarginal μ).toMeasure = μ.toMeasure.snd := rfl

end Carriers

section Reweight

variable {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Bounded Lipschitz functions are integrable against finite measures. -/
private theorem integrable_blFun (f : BoundedLipschitzFun Y) (ν : Measure Y)
    [IsFiniteMeasure ν] : Integrable f.toFun ν := by
  obtain ⟨L, B, hL, hB⟩ := f.exists_bounds
  exact ⟨hL.continuous.stronglyMeasurable.aestronglyMeasurable, .of_bounded (C := (B : ℝ))
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)⟩

/-- The lower integral of the clamped density is the `ENNReal.ofReal` of the Bochner
integral (nonnegativity makes the clamp invisible). -/
private theorem lintegral_ofReal_blFun (f : BoundedLipschitzFun Y) (ν : Measure Y)
    [IsFiniteMeasure ν] (hnn : ∀ y, 0 ≤ f.toFun y) :
    ∫⁻ y, ENNReal.ofReal (f.toFun y) ∂ν = ENNReal.ofReal (∫ y, f.toFun y ∂ν) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_blFun f ν)
    (Filter.Eventually.of_forall hnn)).symm

/-- **The positive-reweighting hypothesis pair**: a nonnegative bounded-Lipschitz
density with positive mean against the prior — the domain of the normalized
reweighting operation. -/
def PosDensityPair (w : BoundedLipschitzFun Y × ProbabilityMeasure Y) : Prop :=
  (∀ y, 0 ≤ w.1.toFun y) ∧ 0 < ∫ y, w.1.toFun y ∂w.2.toMeasure

/-- **Normalized reweighting**: the probability measure `(f · ν) / ∫ f dν` of a
positive-density pair — the output carrier of the Bayes route, with the normalization
performed at the measure level. -/
noncomputable def reweight (w : {w : BoundedLipschitzFun Y × ProbabilityMeasure Y //
    PosDensityPair w}) : ProbabilityMeasure Y := by
  haveI : IsProbabilityMeasure w.val.2.toMeasure := w.val.2.prop
  refine ⟨(∫⁻ y, ENNReal.ofReal (w.val.1.toFun y) ∂w.val.2.toMeasure)⁻¹ •
    w.val.2.toMeasure.withDensity (fun y => ENNReal.ofReal (w.val.1.toFun y)), ⟨?_⟩⟩
  have hZ : w.val.2.toMeasure.withDensity
      (fun y => ENNReal.ofReal (w.val.1.toFun y)) Set.univ
        = ∫⁻ y, ENNReal.ofReal (w.val.1.toFun y) ∂w.val.2.toMeasure := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hlt : ∫⁻ y, ENNReal.ofReal (w.val.1.toFun y) ∂w.val.2.toMeasure
      = ENNReal.ofReal (∫ y, w.val.1.toFun y ∂w.val.2.toMeasure) :=
    lintegral_ofReal_blFun _ _ w.prop.1
  rw [Measure.smul_apply, hZ, smul_eq_mul, hlt,
    ENNReal.inv_mul_cancel (by simp [ENNReal.ofReal_eq_zero, not_le, w.prop.2])
      ENNReal.ofReal_ne_top]

/-- The reweighted measure, unbundled. -/
theorem reweight_toMeasure (w : {w : BoundedLipschitzFun Y × ProbabilityMeasure Y //
    PosDensityPair w}) :
    (reweight w).toMeasure
      = (∫⁻ y, ENNReal.ofReal (w.val.1.toFun y) ∂w.val.2.toMeasure)⁻¹ •
          w.val.2.toMeasure.withDensity (fun y => ENNReal.ofReal (w.val.1.toFun y)) :=
  rfl

/-- Evaluating the normalized reweighting: the ratio of Bochner integrals. -/
private theorem reweight_toMeasure_apply
    (w : {w : BoundedLipschitzFun Y × ProbabilityMeasure Y // PosDensityPair w})
    {A : Set Y} (hA : MeasurableSet A) :
    (reweight w).toMeasure A
      = ENNReal.ofReal ((∫ y in A, w.val.1.toFun y ∂w.val.2.toMeasure)
          / ∫ y, w.val.1.toFun y ∂w.val.2.toMeasure) := by
  haveI : IsProbabilityMeasure w.val.2.toMeasure := w.val.2.prop
  have hZpos : 0 < ∫ y, w.val.1.toFun y ∂w.val.2.toMeasure := w.prop.2
  have hlt : ∫⁻ y in A, ENNReal.ofReal (w.val.1.toFun y) ∂w.val.2.toMeasure
      = ENNReal.ofReal (∫ y in A, w.val.1.toFun y ∂w.val.2.toMeasure) :=
    (ofReal_integral_eq_lintegral_ofReal (integrable_blFun _ _).integrableOn
      (Filter.Eventually.of_forall w.prop.1)).symm
  rw [reweight_toMeasure, Measure.smul_apply, withDensity_apply _ hA, smul_eq_mul,
    lintegral_ofReal_blFun _ _ w.prop.1, hlt, ENNReal.ofReal_div_of_pos hZpos,
    ENNReal.div_eq_inv_mul]

end Reweight

/-! ### The package's positive pair, and `bayesLaw` as a reweighting -/

section Bridge

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {μ : ProbabilityMeasure (X × Y)} {q : BoundedLipschitzFun (X × Y)}

omit [BorelSpace X] in
/-- The pinned package slices to a positive-density pair at every observed point:
nonnegativity is the package's explicit conjunct, and positivity of the mean is the
everywhere-positivity of the Bayes normalizer. -/
theorem IsCondDensityPair.posDensityPair (h : IsCondDensityPair μ q) (x : X) :
    PosDensityPair (q.slice x, sndMarginal μ) := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  refine ⟨fun y => h.nonneg (x, y), ?_⟩
  by_contra hcon
  refine h.bayesZ_ne_zero x ?_
  have h0 : ∫ y, (q.slice x).toFun y ∂μ.toMeasure.snd ≤ 0 := le_of_not_gt hcon
  have hZ : bayesZ μ.toMeasure.snd q.toFun x
      = ENNReal.ofReal (∫ y, (q.slice x).toFun y ∂μ.toMeasure.snd) :=
    lintegral_ofReal_blFun (q.slice x) μ.toMeasure.snd fun y => h.nonneg (x, y)
  rw [hZ, ENNReal.ofReal_eq_zero]
  exact h0

omit [BorelSpace X] in
/-- The produced conditional law IS the normalized slice reweighting — the exact bridge
between the Bayes route's mathematical layer and its realizer. -/
theorem bayesLaw_eq_reweight (h : IsCondDensityPair μ q) (x : X) :
    bayesLaw μ q h x = reweight ⟨(q.slice x, sndMarginal μ), h.posDensityPair x⟩ :=
  Subtype.ext rfl

end Bridge

/-! ### Lévy–Prokhorov stability of normalized reweighting

The superlevel-set engine of unit 31's Prokhorov stability estimate, applied to
restricted measures: mass of `f · ν₁` on `A` moves into the `ε`-thickening of `A`
under `f · ν₂` at cost `(L + B) · ε`, whence the normalized reweightings are
LP-close whenever the priors are. -/

section DiracSums

variable {Z : Type} [MeasurableSpace Z]

/-- Evaluating a finite atomic measure on a measurable set: indicator sums (private
re-derivation of unit 27's helper). -/
private theorem sum_smul_dirac_apply {k : ℕ} (a : Fin k → ℝ) (x : Fin k → Z) {A : Set Z}
    (hA : MeasurableSet A) :
    (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) A
      = ∑ i, A.indicator (fun _ => ENNReal.ofReal (a i)) (x i) := by
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  by_cases hi : x i ∈ A
  · simp [Set.indicator_of_mem hi]
  · simp [Set.indicator_of_notMem hi]

end DiracSums

section ReweightStability

variable {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [MetricSpace Y] [BorelSpace Y] in
/-- A probability measure forces the space to be nonempty (private re-derivation). -/
private theorem nonempty_of_prob (ν : Measure Y) [IsProbabilityMeasure ν] :
    Nonempty Y := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : ν Set.univ = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
  exact zero_ne_one h1

/-- Finite-to-finite `ℝ≥0∞` inequalities with an `ofReal` error descend to `toReal`. -/
private theorem toReal_le_add_of_le {a b : ℝ≥0∞} {ε : ℝ} (hb : b ≠ ∞) (hε : 0 ≤ ε)
    (h : a ≤ b + ENNReal.ofReal ε) : a.toReal ≤ b.toReal + ε := by
  have hne : b + ENNReal.ofReal ε ≠ ∞ := ENNReal.add_ne_top.mpr ⟨hb, ENNReal.ofReal_ne_top⟩
  calc a.toReal ≤ (b + ENNReal.ofReal ε).toReal := ENNReal.toReal_mono hne h
    _ = b.toReal + ε := by rw [ENNReal.toReal_add hb ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε]

/-- **One-sided Lévy–Prokhorov stability of set integrals** of nonnegative bounded
Lipschitz integrands: `∫_A f dν₁ ≤ ∫_{A^ε} f dν₂ + (L + B) ε` whenever
`levyProkhorovEDist ν₁ ν₂ < ε` — the superlevel-set engine on restricted measures. -/
private theorem setIntegral_le_thickening_add
    {ν₁ ν₂ : Measure Y} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    {f : Y → ℝ} {L : ℝ≥0} {B : ℝ} (hLip : LipschitzWith L f) (hnn : ∀ y, 0 ≤ f y)
    (hB : ∀ y, |f y| ≤ B) {ε : ℝ} (hε : 0 < ε)
    (hd : levyProkhorovEDist ν₁ ν₂ < ENNReal.ofReal ε) {A : Set Y}
    (hA : MeasurableSet A) :
    ∫ y in A, f y ∂ν₁ ≤ (∫ y in thickening ε A, f y ∂ν₂) + ((L : ℝ) + B) * ε := by
  have hne : Nonempty Y := nonempty_of_prob ν₁
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB hne.some)
  have hφc : Continuous f := hLip.continuous
  have hAε : MeasurableSet (thickening ε A) := isOpen_thickening.measurableSet
  -- `f` as a bounded continuous function
  set fBC : BoundedContinuousFunction Y ℝ :=
    .ofNormedAddCommGroup f hφc B (fun y => by rw [Real.norm_eq_abs]; exact hB y)
    with hfBC_def
  have hfeq : ∀ y, fBC y = f y := fun _ => rfl
  have hfnorm : ‖fBC‖ ≤ B := BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hB0 _
  have hf0 : (0 : ℝ) ≤ ‖fBC‖ := norm_nonneg fBC
  -- superlevel sets are measurable
  have hlev : ∀ t : ℝ, MeasurableSet {a : Y | t ≤ fBC a} := fun t =>
    measurableSet_le measurable_const fBC.continuous.measurable
  -- the layer-cake identities on the two restricted measures
  have hlhs : ∫ y in A, f y ∂ν₁
      = ∫ t in Set.Ioc 0 ‖fBC‖, (ν₁.restrict A).real {a | t ≤ fBC a} := by
    exact BoundedContinuousFunction.integral_eq_integral_meas_le fBC (ν₁.restrict A)
      (Filter.Eventually.of_forall fun y => hnn y)
  -- the shifted superlevel mass of the thickening-restricted `ν₂`
  set g : ℝ → ℝ := fun s => (ν₂.restrict (thickening ε A)).real {a | s ≤ fBC a}
    with hg_def
  have hganti : Antitone g := fun s₁ s₂ h =>
    measureReal_mono (fun a (ha : s₂ ≤ fBC a) => h.trans ha) (measure_ne_top _ _)
  have hg0 : ∀ s, 0 ≤ g s := fun _ => measureReal_nonneg
  have hg1 : ∀ s, g s ≤ 1 := fun s => by
    simp only [hg_def]
    rw [measureReal_def, Measure.restrict_apply (hlev s)]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  -- the per-level LP move
  have hlevel : ∀ t : ℝ,
      (ν₁.restrict A).real {a | t ≤ fBC a} ≤ g (t - (L : ℝ) * ε) + ε := by
    intro t
    have hmove : ν₁ ({a | t ≤ fBC a} ∩ A)
        ≤ ν₂ ({a | t - (L : ℝ) * ε ≤ fBC a} ∩ thickening ε A) + ENNReal.ofReal ε := by
      have h1 : ν₁ ({a | t ≤ fBC a} ∩ A)
          ≤ ν₂ (thickening (ENNReal.ofReal ε).toReal ({a | t ≤ fBC a} ∩ A))
              + ENNReal.ofReal ε :=
        left_measure_le_of_levyProkhorovEDist_lt hd ((hlev t).inter hA)
      rw [ENNReal.toReal_ofReal hε.le] at h1
      refine h1.trans (add_le_add (measure_mono fun a ha => ?_) le_rfl)
      obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.mp ha
      have hfz : dist (f a) (f z) ≤ (L : ℝ) * dist a z := hLip.dist_le_mul a z
      rw [Real.dist_eq] at hfz
      have h3 := (abs_le.mp (hfz.trans
        (mul_le_mul_of_nonneg_left hdist.le L.coe_nonneg))).1
      have hzf : t ≤ f z := hfeq z ▸ hz.1
      refine ⟨?_, Metric.mem_thickening_iff.mpr ⟨z, hz.2, hdist⟩⟩
      simp only [Set.mem_setOf_eq, hfeq a]
      linarith
    simp only [hg_def]
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hlev t),
      Measure.restrict_apply (hlev _)]
    exact toReal_le_add_of_le (measure_ne_top _ _) hε.le hmove
  -- integrate the per-level move over `Ioc 0 ‖fBC‖`
  have hmble_lhs : Antitone fun t => (ν₁.restrict A).real {a | t ≤ fBC a} :=
    fun s₁ s₂ h => measureReal_mono (fun a (ha : s₂ ≤ fBC a) => h.trans ha)
      (measure_ne_top _ _)
  have hlhs1 : ∀ t, (ν₁.restrict A).real {a | t ≤ fBC a} ≤ 1 := fun t => by
    rw [measureReal_def, Measure.restrict_apply (hlev t)]
    refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  have hint_lhs : IntegrableOn (fun t => (ν₁.restrict A).real {a | t ≤ fBC a})
      (Set.Ioc 0 ‖fBC‖) := by
    apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    · exact hmble_lhs.measurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact hlhs1 t
  have hganti' : Antitone fun t => g (t - (L : ℝ) * ε) := fun t₁ t₂ h =>
    hganti (by linarith)
  have hint_shift : IntegrableOn (fun t => g (t - (L : ℝ) * ε))
      (Set.Ioc 0 ‖fBC‖) := by
    apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    · exact hganti'.measurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
        exact hg1 _
  have step_int : (∫ t in Set.Ioc 0 ‖fBC‖, (ν₁.restrict A).real {a | t ≤ fBC a})
      ≤ ∫ t in Set.Ioc 0 ‖fBC‖, (g (t - (L : ℝ) * ε) + ε) :=
    setIntegral_mono_on hint_lhs (hint_shift.add (integrableOn_const (C := ε) (by simp)))
      measurableSet_Ioc fun t _ => hlevel t
  have hsplit : ∫ t in Set.Ioc 0 ‖fBC‖, (g (t - (L : ℝ) * ε) + ε)
      = (∫ t in Set.Ioc 0 ‖fBC‖, g (t - (L : ℝ) * ε)) + ε * ‖fBC‖ := by
    rw [integral_add hint_shift (integrableOn_const (C := ε) (by simp)),
      setIntegral_const, smul_eq_mul]
    congr 1
    rw [measureReal_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hf0, mul_comm]
  -- the shift argument on the interval integral (unit 31's steps 4–8)
  have hLε0 : 0 ≤ (L : ℝ) * ε := mul_nonneg L.coe_nonneg hε.le
  have hgIntble : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    fun _ _ => hganti.intervalIntegrable
  have step4 : ∫ t in Set.Ioc 0 ‖fBC‖, g (t - (L : ℝ) * ε)
      = ∫ t in (0 : ℝ)..‖fBC‖, g (t - (L : ℝ) * ε) :=
    (intervalIntegral.integral_of_le hf0).symm
  have step5 : ∫ t in (0 : ℝ)..‖fBC‖, g (t - (L : ℝ) * ε)
      = ∫ t in (0 - (L : ℝ) * ε)..(‖fBC‖ - (L : ℝ) * ε), g t :=
    intervalIntegral.integral_comp_sub_right g ((L : ℝ) * ε)
  have step6 : ∫ t in (0 - (L : ℝ) * ε)..(‖fBC‖ - (L : ℝ) * ε), g t
      ≤ ∫ t in (0 - (L : ℝ) * ε)..‖fBC‖, g t :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun s => hg0 s) (hgIntble _ _)
  have step7 : ∫ t in (0 - (L : ℝ) * ε)..‖fBC‖, g t
      = (∫ t in (0 - (L : ℝ) * ε)..(0 : ℝ), g t) + ∫ t in (0 : ℝ)..‖fBC‖, g t :=
    (intervalIntegral.integral_add_adjacent_intervals (hgIntble _ _) (hgIntble _ _)).symm
  have step8 : ∫ t in (0 - (L : ℝ) * ε)..(0 : ℝ), g t ≤ (L : ℝ) * ε := by
    have h1 : ∫ t in (0 - (L : ℝ) * ε)..(0 : ℝ), g t
        ≤ ∫ _t in (0 - (L : ℝ) * ε)..(0 : ℝ), (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) (hgIntble _ _)
        intervalIntegrable_const fun s _ => hg1 s
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
    linarith
  have step9 : ∫ t in (0 : ℝ)..‖fBC‖, g t
      = ∫ y in thickening ε A, f y ∂ν₂ := by
    rw [intervalIntegral.integral_of_le hf0]
    exact (BoundedContinuousFunction.integral_eq_integral_meas_le fBC
      (ν₂.restrict (thickening ε A)) (Filter.Eventually.of_forall fun y => hnn y)).symm
  have hεnorm : ε * ‖fBC‖ ≤ ε * B := mul_le_mul_of_nonneg_left hfnorm hε.le
  rw [hlhs]
  calc (∫ t in Set.Ioc 0 ‖fBC‖, (ν₁.restrict A).real {a | t ≤ fBC a})
      ≤ (∫ t in Set.Ioc 0 ‖fBC‖, g (t - (L : ℝ) * ε)) + ε * ‖fBC‖ := by
        rw [← hsplit]
        exact step_int
    _ ≤ (∫ y in thickening ε A, f y ∂ν₂) + ((L : ℝ) + B) * ε := by
        have := step6
        rw [step7] at this
        nlinarith [step4, step5, step8, step9, hεnorm]

/-- The real-arithmetic core of the normalized comparison: numerators within `c`,
denominators within `c`, first denominator at least `z`, and an `ε'` budget of at least
`2 c / z` absorb the normalization error. -/
private theorem div_ratio_le {r₁ r₂ Z₁ Z₂ c z ε' : ℝ} (hz : 0 < z) (hzZ : z ≤ Z₁)
    (hZ₂ : 0 < Z₂) (hc : 0 ≤ c) (hr₂0 : 0 ≤ r₂) (h₁ : r₁ ≤ r₂ + c) (h₂ : r₂ ≤ Z₂)
    (h₃ : Z₂ ≤ Z₁ + c) (hε' : 2 * c / z ≤ ε') : r₁ / Z₁ ≤ r₂ / Z₂ + ε' := by
  have hZ₁ : 0 < Z₁ := lt_of_lt_of_le hz hzZ
  have hε'0 : 0 ≤ ε' := le_trans (div_nonneg (by linarith) hz.le) hε'
  have h2cz : 2 * c ≤ ε' * z := (div_le_iff₀ hz).mp hε'
  rw [div_add' _ _ _ hZ₂.ne', div_le_div_iff₀ hZ₁ hZ₂]
  -- goal: `r₁ * Z₂ ≤ (r₂ + ε' * Z₂) * Z₁`
  have key1 : r₂ * Z₂ ≤ r₂ * Z₁ + Z₂ * c := by
    rcases le_total Z₂ Z₁ with hle | hle
    · nlinarith [mul_le_mul_of_nonneg_left hle hr₂0]
    · have ha : r₂ * (Z₂ - Z₁) ≤ Z₂ * (Z₂ - Z₁) :=
        mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr hle)
      have hb : Z₂ * (Z₂ - Z₁) ≤ Z₂ * c :=
        mul_le_mul_of_nonneg_left (by linarith) hZ₂.le
      nlinarith
  have key2 : 2 * c * Z₂ ≤ ε' * Z₁ * Z₂ := by
    have ha : 2 * c * Z₂ ≤ ε' * z * Z₂ := mul_le_mul_of_nonneg_right h2cz hZ₂.le
    have hb : ε' * Z₂ * z ≤ ε' * Z₂ * Z₁ :=
      mul_le_mul_of_nonneg_left hzZ (mul_nonneg hε'0 hZ₂.le)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h₁ hZ₂.le]

/-- **Lévy–Prokhorov stability of normalized reweighting**: if the priors are LP-close
and the first normalizer is at least `z`, the normalized reweightings are LP-close at
cost `ε + 2 (L + B) ε / z`. -/
private theorem levyProkhorovDist_reweight_le (f : BoundedLipschitzFun Y)
    {ν₁ ν₂ : ProbabilityMeasure Y} (h₁ : PosDensityPair (f, ν₁))
    (h₂ : PosDensityPair (f, ν₂)) {L : ℝ≥0} {B : ℝ}
    (hLip : LipschitzWith L f.toFun) (hB : ∀ y, |f.toFun y| ≤ B) {z ε : ℝ}
    (hz : 0 < z) (hzZ : z ≤ ∫ y, f.toFun y ∂ν₁.toMeasure) (hε : 0 < ε)
    (hd : levyProkhorovDist ν₁.toMeasure ν₂.toMeasure < ε) :
    levyProkhorovDist (reweight ⟨(f, ν₁), h₁⟩).toMeasure
        (reweight ⟨(f, ν₂), h₂⟩).toMeasure
      ≤ ε + 2 * ((L : ℝ) + B) * ε / z := by
  haveI hP1 : IsProbabilityMeasure ν₁.toMeasure := ν₁.prop
  haveI hP2 : IsProbabilityMeasure ν₂.toMeasure := ν₂.prop
  haveI : IsProbabilityMeasure (reweight ⟨(f, ν₁), h₁⟩).toMeasure :=
    (reweight ⟨(f, ν₁), h₁⟩).prop
  haveI : IsProbabilityMeasure (reweight ⟨(f, ν₂), h₂⟩).toMeasure :=
    (reweight ⟨(f, ν₂), h₂⟩).prop
  have hZ₁ : 0 < ∫ y, f.toFun y ∂ν₁.toMeasure := lt_of_lt_of_le hz hzZ
  have hZ₂ : 0 < ∫ y, f.toFun y ∂ν₂.toMeasure := h₂.2
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (nonempty_of_prob ν₁.toMeasure).some)
  have hc0 : (0 : ℝ) ≤ ((L : ℝ) + B) * ε :=
    mul_nonneg (add_nonneg L.coe_nonneg hB0) hε.le
  have hedist : levyProkhorovEDist ν₁.toMeasure ν₂.toMeasure < ENNReal.ofReal ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr hd
  have hedist' : levyProkhorovEDist ν₂.toMeasure ν₁.toMeasure < ENNReal.ofReal ε := by
    rwa [levyProkhorovEDist_comm]
  -- the normalizer transfer to the second prior
  have hZtrans : (∫ y, f.toFun y ∂ν₂.toMeasure)
      ≤ (∫ y, f.toFun y ∂ν₁.toMeasure) + ((L : ℝ) + B) * ε := by
    have hcore := setIntegral_le_thickening_add hLip h₂.1 hB hε hedist'
      MeasurableSet.univ
    have huniv₂ : ∫ y in Set.univ, f.toFun y ∂ν₂.toMeasure
        = ∫ y, f.toFun y ∂ν₂.toMeasure := setIntegral_univ
    have hthick : (∫ y in thickening ε Set.univ, f.toFun y ∂ν₁.toMeasure)
        ≤ ∫ y, f.toFun y ∂ν₁.toMeasure := by
      rw [← setIntegral_univ (f := f.toFun) (μ := ν₁.toMeasure)]
      exact setIntegral_mono_set (integrable_blFun f _).integrableOn
        (Filter.Eventually.of_forall fun y => h₁.1 y)
        (Set.subset_univ _).eventuallyLE
    rw [huniv₂] at hcore
    linarith
  have htail0 : (0 : ℝ) ≤ 2 * ((L : ℝ) + B) * ε / z :=
    div_nonneg (by linarith) hz.le
  have hδ0 : (0 : ℝ) ≤ ε + 2 * ((L : ℝ) + B) * ε / z := by linarith
  refine levyProkhorovDist_le_of_forall_le _ _ hδ0 fun ε' A hε' hA => ?_
  have hεε' : ε < ε' := lt_of_le_of_lt (le_add_of_nonneg_right htail0) hε'
  have hε'0 : 0 < ε' := lt_of_le_of_lt hδ0 hε'
  have hAε' : MeasurableSet (thickening ε' A) := isOpen_thickening.measurableSet
  -- the three set integrals
  have hcore := setIntegral_le_thickening_add hLip h₁.1 hB hε hedist hA
  have hmono : (∫ y in thickening ε A, f.toFun y ∂ν₂.toMeasure)
      ≤ ∫ y in thickening ε' A, f.toFun y ∂ν₂.toMeasure :=
    setIntegral_mono_set (integrable_blFun f _).integrableOn
      (Filter.Eventually.of_forall fun y => h₂.1 y)
      (thickening_mono hεε'.le A).eventuallyLE
  have huniv : (∫ y in thickening ε' A, f.toFun y ∂ν₂.toMeasure)
      ≤ ∫ y, f.toFun y ∂ν₂.toMeasure := by
    rw [← setIntegral_univ (f := f.toFun) (μ := ν₂.toMeasure)]
    exact setIntegral_mono_set (integrable_blFun f _).integrableOn
      (Filter.Eventually.of_forall fun y => h₂.1 y) (Set.subset_univ _).eventuallyLE
  have hr₂0 : 0 ≤ ∫ y in thickening ε' A, f.toFun y ∂ν₂.toMeasure :=
    setIntegral_nonneg hAε' fun y _ => h₂.1 y
  have hkey : (∫ y in A, f.toFun y ∂ν₁.toMeasure) / (∫ y, f.toFun y ∂ν₁.toMeasure)
      ≤ (∫ y in thickening ε' A, f.toFun y ∂ν₂.toMeasure)
          / (∫ y, f.toFun y ∂ν₂.toMeasure) + ε' :=
    div_ratio_le hz hzZ hZ₂ hc0 hr₂0 (by linarith) huniv hZtrans (by
      have hassoc : 2 * (((L : ℝ) + B) * ε) / z = 2 * ((L : ℝ) + B) * ε / z := by
        ring
      rw [hassoc]
      linarith)
  rw [reweight_toMeasure_apply _ hA, reweight_toMeasure_apply _ hAε']
  calc ENNReal.ofReal ((∫ y in A, f.toFun y ∂ν₁.toMeasure)
        / ∫ y, f.toFun y ∂ν₁.toMeasure)
      ≤ ENNReal.ofReal ((∫ y in thickening ε' A, f.toFun y ∂ν₂.toMeasure)
          / (∫ y, f.toFun y ∂ν₂.toMeasure) + ε') := ENNReal.ofReal_le_ofReal hkey
    _ = ENNReal.ofReal ((∫ y in thickening ε' A, f.toFun y ∂ν₂.toMeasure)
          / ∫ y, f.toFun y ∂ν₂.toMeasure) + ENNReal.ofReal ε' :=
        ENNReal.ofReal_add (div_nonneg hr₂0 hZ₂.le) hε'0.le

/-! #### The normalized-weight perturbation -/

omit [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- **Normalized-weight perturbation**: an `ℓ¹` perturbation of nonnegative weight
vectors below the mass lower bound perturbs the normalized weights by at most twice the
relative perturbation. -/
private theorem sum_abs_normalized_le {k : ℕ} (a b : Fin k → ℝ)
    (hb : ∀ i, 0 ≤ b i) {η ζ : ℝ} (hζ : 0 < ζ) (hSuma : ζ ≤ ∑ i, a i)
    (hab : ∑ i, |a i - b i| ≤ η) (hη : η < ζ) :
    ∑ i, |a i / (∑ j, a j) - b i / (∑ j, b j)| ≤ 2 * η / ζ := by
  set Sa := ∑ j, a j with hSa_def
  set Sb := ∑ j, b j with hSb_def
  have hSa : 0 < Sa := lt_of_lt_of_le hζ hSuma
  have hdiff : |Sa - Sb| ≤ η := by
    calc |Sa - Sb| = |∑ i, (a i - b i)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |a i - b i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ η := hab
  have hSb : 0 < Sb := by
    have := (abs_le.mp hdiff).2
    linarith
  have hη0 : 0 ≤ η := le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) hab
  have hpoint : ∀ i, |a i / Sa - b i / Sb|
      ≤ |a i - b i| / Sa + b i / Sb * (|Sb - Sa| / Sa) := by
    intro i
    have hi : a i / Sa - b i / Sb = (a i - b i) / Sa + b i / Sb * ((Sb - Sa) / Sa) := by
      field_simp
      ring
    rw [hi]
    have e1 : |(a i - b i) / Sa| = |a i - b i| / Sa := by
      rw [abs_div, abs_of_pos hSa]
    have e2 : |b i / Sb * ((Sb - Sa) / Sa)| = b i / Sb * (|Sb - Sa| / Sa) := by
      rw [abs_mul, abs_div, abs_div, abs_of_pos hSa, abs_of_pos hSb,
        abs_of_nonneg (hb i)]
    calc |(a i - b i) / Sa + b i / Sb * ((Sb - Sa) / Sa)|
        ≤ |(a i - b i) / Sa| + |b i / Sb * ((Sb - Sa) / Sa)| := abs_add_le _ _
      _ = |a i - b i| / Sa + b i / Sb * (|Sb - Sa| / Sa) := by rw [e1, e2]
  have hbsum : ∑ i, b i / Sb = 1 := by
    rw [← Finset.sum_div, ← hSb_def, div_self hSb.ne']
  calc ∑ i, |a i / Sa - b i / Sb|
      ≤ ∑ i, (|a i - b i| / Sa + b i / Sb * (|Sb - Sa| / Sa)) :=
        Finset.sum_le_sum fun i _ => hpoint i
    _ = (∑ i, |a i - b i|) / Sa + (∑ i, b i / Sb) * (|Sb - Sa| / Sa) := by
        rw [Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_mul]
    _ = (∑ i, |a i - b i|) / Sa + |Sb - Sa| / Sa := by rw [hbsum, one_mul]
    _ ≤ η / Sa + η / Sa := by
        have h1 : (∑ i, |a i - b i|) / Sa ≤ η / Sa := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right hab (inv_nonneg.mpr hSa.le)
        have h2 : |Sb - Sa| / Sa ≤ η / Sa := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_right (by rwa [abs_sub_comm])
            (inv_nonneg.mpr hSa.le)
        linarith
    _ ≤ 2 * η / ζ := by
        have hinv : Sa⁻¹ ≤ ζ⁻¹ := by
          rw [← one_div, ← one_div]
          exact one_div_le_one_div_of_le hζ hSuma
        have h3 : η / Sa ≤ η / ζ := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hinv hη0
        have hsplit : 2 * η / ζ = η / ζ + η / ζ := by ring
        linarith

end ReweightStability

/-! ### Clamped weights: definitionally equal copies of unit 27's private helpers -/

/-- The clamped rational weight of a weight code (definitionally equal to the private
helper inside `atomicOfList`). -/
private def wRaw (c : ℕ) : ℚ := max 0 (min 1 (ratOfCode c))

private theorem wRaw_nonneg (c : ℕ) : 0 ≤ wRaw c := le_max_left _ _

/-- The (rational) total clamped weight of a decoded atom list (definitionally equal to
the private helper inside `atomicOfList`). -/
private def wSumL (l : List (ℕ × ℕ)) : ℚ := (l.map fun pr => wRaw pr.2).sum

private theorem wSumL_nonneg (l : List (ℕ × ℕ)) : 0 ≤ wSumL l :=
  List.sum_nonneg fun x hx => by
    obtain ⟨pr, -, rfl⟩ := List.mem_map.mp hx
    exact wRaw_nonneg _

/-- A mapped list sum as a `Fin` sum over positions. -/
private theorem listSum_map_eq_finSum {β M : Type*} [AddCommMonoid M] (l : List β)
    (g : β → M) : (l.map g).sum = ∑ i : Fin l.length, g l[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

private theorem sum_normWt {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) :
    ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) = 1 := by
  have hcast : ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
      = (((∑ i : Fin l.length, wRaw l[i].2) / wSumL l : ℚ) : ℝ) := by
    push_cast
    rw [Finset.sum_div]
  rw [hcast]
  have hsum : ∑ i : Fin l.length, wRaw l[i].2 = wSumL l :=
    (listSum_map_eq_finSum l fun pr => wRaw pr.2).symm
  rw [hsum, div_self h0]
  norm_num

private theorem normWt_nonneg {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) (i : Fin l.length) :
    (0 : ℝ) ≤ ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) := by
  have hpos : (0 : ℚ) < wSumL l := lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
  exact_mod_cast div_nonneg (wRaw_nonneg _) hpos.le

/-- A zero total clamped weight forces every clamped weight to vanish. -/
private theorem wRaw_all_zero : ∀ l : List (ℕ × ℕ), wSumL l = 0 →
    ∀ pr ∈ l, wRaw pr.2 = 0 := by
  intro l
  induction l with
  | nil => intro _ pr hpr; cases hpr
  | cons a t ih =>
    intro h0 pr hpr
    have hts : 0 ≤ wSumL t := wSumL_nonneg t
    have ha0 : 0 ≤ wRaw a.2 := wRaw_nonneg _
    have hcons : wSumL (a :: t) = wRaw a.2 + wSumL t := rfl
    have hsplit : wRaw a.2 + wSumL t = 0 := by rw [← hcons, h0]
    rcases List.mem_cons.mp hpr with rfl | hpr'
    · linarith
    · exact ih (by linarith) pr hpr'

section AtomicEval

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

omit [BorelSpace X] in
/-- Nonzero total weight: the decoded atomic is the renormalized weighted Dirac sum
(cross-definitional-equality copy of unit 31's branch evaluation). -/
private theorem toMeasure_atomicOfList_of_ne {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) :
    (atomicOfList P l).toMeasure
      = ∑ i : Fin l.length,
          ENNReal.ofReal ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            • Measure.dirac (P.dense l[i].1) := by
  rw [atomicOfList]
  split
  · next h => exact absurd h h0
  · next h => rfl

omit [BorelSpace X] in
/-- Zero total weight: the decoded atomic is the default Dirac at dense point `0`. -/
private theorem toMeasure_atomicOfList_of_eq {l : List (ℕ × ℕ)} (h0 : wSumL l = 0) :
    (atomicOfList P l).toMeasure = Measure.dirac (P.dense 0) := by
  rw [atomicOfList]
  split
  · next h => rfl
  · next h => exact absurd h0 h

omit [BorelSpace X] in
/-- Decoding an encoded atom list. -/
private theorem atomic_encode (l : List (ℕ × ℕ)) :
    atomic P (Encodable.encode l) = atomicOfList P l := by
  rw [atomic, Denumerable.ofNat_encode]

end AtomicEval

/-! ### The second marginal: LP nonexpansiveness and the atomic projection -/

section SndMarginalLP

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [BorelSpace X] in
/-- The second-marginal projection is Lévy–Prokhorov nonexpansive: `Prod.snd` is
`1`-Lipschitz for the max product metric, so thickenings of preimages land in
preimages of thickenings. -/
private theorem levyProkhorovEDist_snd_le (μ ν : Measure (X × Y)) :
    levyProkhorovEDist μ.snd ν.snd ≤ levyProkhorovEDist μ ν := by
  apply sInf_le_sInf
  intro ε hε
  simp only [Set.mem_setOf_eq] at hε ⊢
  intro A hA
  have step : ∀ ρ σ : Measure (X × Y),
      ρ (Prod.snd ⁻¹' A) ≤ σ (thickening ε.toReal (Prod.snd ⁻¹' A)) + ε →
      ρ.snd A ≤ σ.snd (thickening ε.toReal A) + ε := by
    intro ρ σ h
    rw [Measure.snd_apply hA, Measure.snd_apply isOpen_thickening.measurableSet]
    refine h.trans (add_le_add (measure_mono fun z hz => ?_) le_rfl)
    obtain ⟨w, hw, hdist⟩ := Metric.mem_thickening_iff.mp hz
    have hle : dist z.2 w.2 ≤ dist z w := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact Set.mem_preimage.mpr
      (Metric.mem_thickening_iff.mpr ⟨w.2, hw, lt_of_le_of_lt hle hdist⟩)
  obtain ⟨h₁, h₂⟩ := hε (Prod.snd ⁻¹' A) (measurable_snd hA)
  exact ⟨step μ ν h₁, step ν μ h₂⟩

omit [BorelSpace X] in
/-- The metric form of the second-marginal LP nonexpansiveness. -/
private theorem levyProkhorovDist_snd_le (μ ν : Measure (X × Y)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    levyProkhorovDist μ.snd ν.snd ≤ levyProkhorovDist μ ν :=
  ENNReal.toReal_mono (levyProkhorovEDist_ne_top _ _) (levyProkhorovEDist_snd_le μ ν)

/-- The index-projected atom list of the second-marginal projection. -/
private def projList (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.map fun pr => (pr.1.unpair.2, pr.2)

private theorem wSumL_projList (l : List (ℕ × ℕ)) : wSumL (projList l) = wSumL l := by
  unfold wSumL projList
  rw [List.map_map]
  rfl

omit [BorelSpace X] [BorelSpace Y] in
/-- **The second marginal of a decoded atomic on the presented product** is the decoded
atomic of the index-projected list on the second factor. -/
private theorem snd_atomicOfList (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) (l : List (ℕ × ℕ)) :
    (atomicOfList (P.prod Q) l).toMeasure.snd
      = (atomicOfList Q (projList l)).toMeasure := by
  have hlen : (projList l).length = l.length := List.length_map ..
  by_cases h0 : wSumL l = 0
  · rw [toMeasure_atomicOfList_of_eq _ h0,
      toMeasure_atomicOfList_of_eq _ (by rw [wSumL_projList]; exact h0),
      Measure.snd, Measure.map_dirac' measurable_snd]
    have hpt : ((P.prod Q).dense 0).2 = Q.dense 0 := by
      change Q.dense (Nat.unpair 0).2 = Q.dense 0
      norm_num
    rw [hpt]
  · have h0' : wSumL (projList l) ≠ 0 := by rw [wSumL_projList]; exact h0
    rw [toMeasure_atomicOfList_of_ne _ h0, toMeasure_atomicOfList_of_ne _ h0',
      ← listSum_map_eq_finSum l fun pr =>
        ENNReal.ofReal ((wRaw pr.2 / wSumL l : ℚ) : ℝ)
          • Measure.dirac ((P.prod Q).dense pr.1),
      ← listSum_map_eq_finSum (projList l) fun pr =>
        ENNReal.ofReal ((wRaw pr.2 / wSumL (projList l) : ℚ) : ℝ)
          • Measure.dirac (Q.dense pr.1)]
    have hsnd : ∀ ms : List (Measure (X × Y)), ms.sum.snd = (ms.map Measure.snd).sum := by
      intro ms
      induction ms with
      | nil => simp
      | cons m t ih => rw [List.sum_cons, Measure.snd_add, ih, List.map_cons,
          List.sum_cons]
    rw [hsnd, List.map_map]
    unfold projList
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left fun pr _ => ?_)
    change (ENNReal.ofReal ((wRaw pr.2 / wSumL l : ℚ) : ℝ)
        • Measure.dirac ((P.prod Q).dense pr.1)).snd
      = ENNReal.ofReal ((wRaw pr.2 / wSumL (projList l) : ℚ) : ℝ)
          • Measure.dirac (Q.dense pr.1.unpair.2)
    rw [wSumL_projList, Measure.snd, Measure.map_smul, Measure.map_dirac' measurable_snd]
    rfl

/-- The encoded projected list is computable. -/
private theorem computable_projCode :
    Computable fun v => Encodable.encode (projList (ofNat (List (ℕ × ℕ)) v)) := by
  have hmap : Primrec fun v => projList (ofNat (List (ℕ × ℕ)) v) :=
    Primrec.list_map ((Primrec.ofNat (List (ℕ × ℕ))).comp Primrec.id)
      (((primrec_unpairSnd.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact (Primrec.encode.comp hmap).to_comp

/-- **The second marginal is computable** from the weak name of the joint law:
project every decoded atom to its second dense index (coordinatewise on the name);
LP nonexpansiveness of `Prod.snd` preserves the pinned rate. -/
theorem computableMap_sndMarginal (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    ComputableMap
      (haveI : BorelSpace (X × Y) := P.borelSpace_prod
       weakMeasureRep (P.prod Q))
      (weakMeasureRep Q) sndMarginal := by
  haveI : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨gC, hgC⟩ := exists_ofNatFnCode computable_projCode
  refine ⟨.comp gC .query, fun p μ hpμ => ?_⟩
  have hM := (weakMeasureRep_names_iff (P.prod Q)).mp hpμ
  refine ⟨fun n => Encodable.encode (projList (ofNat (List (ℕ × ℕ)) (p n))),
    mem_evalStream.mpr fun n => ?_, ?_⟩
  · rw [eval_comp_some (eval_query p n), hgC]
    exact Part.mem_some _
  · refine (weakMeasureRep_names_iff Q).mpr fun n => ?_
    haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
    haveI : IsProbabilityMeasure (atomic (P.prod Q) (p n)).toMeasure :=
      (atomic (P.prod Q) (p n)).prop
    have hproj : (atomic Q (Encodable.encode (projList (ofNat (List (ℕ × ℕ))
        (p n))))).toMeasure = (atomic (P.prod Q) (p n)).toMeasure.snd := by
      rw [atomic_encode, atomic, snd_atomicOfList P Q]
    rw [sndMarginal_toMeasure, hproj]
    calc levyProkhorovDist μ.toMeasure.snd (atomic (P.prod Q) (p n)).toMeasure.snd
        ≤ levyProkhorovDist μ.toMeasure (atomic (P.prod Q) (p n)).toMeasure :=
          levyProkhorovDist_snd_le _ _
      _ ≤ (2 : ℝ)⁻¹ ^ n := hM n

end SndMarginalLP

/-! ### The density slice is computable

From a product name (bounded-Lipschitz name of `q` on the even track, fast Cauchy name
of `x` on the odd track), a bounded-Lipschitz name of the slice `q (x, ·)` is emitted
coordinatewise through a three-stage adaptive prefix chain: the heads are copied, and
the value stream at dense index `j`, precision `t`, queries the product name at the
pair of the stage-`t + 1 + L` approximant of `x` with `j`, at precision `t + 1` — the
Lipschitz head `L` bounds the slippage `L · 2⁻⁽ᵗ⁺¹⁺ᴸ⁾ ≤ 2⁻⁽ᵗ⁺¹⁾`. -/

section SliceRealizer

/-- Extracting a coordinate from an encoded stream prefix (private re-derivation of
unit 31's helper). -/
private theorem streamTake_getD (p : Baire) {j m : ℕ} (h : j < m) :
    (streamTake p m).getD j 0 = p j := by
  rw [List.getD_eq_getElem _ _ (by rw [length_streamTake]; exact h), getElem_streamTake]

/-- The decoded prefix of a packed chain input. -/
private def prefListS (w : ℕ) : List ℕ := ofNat (List ℕ) w.unpair.2

/-- The copied Lipschitz head. -/
private def headLS (w : ℕ) : ℕ := (prefListS w).getD 0 0

/-- The precision index of an output coordinate `n = 2 + Nat.pair j t`. -/
private def sliceT (w : ℕ) : ℕ := (w.unpair.1 - 2).unpair.2

/-- The dense index of an output coordinate. -/
private def sliceJ (w : ℕ) : ℕ := (w.unpair.1 - 2).unpair.1

/-- The odd-track (Cauchy-name) query position: stage `t + 1 + L`. -/
private def sliceQpos (w : ℕ) : ℕ := 2 * (sliceT w + 1 + headLS w) + 1

/-- The queried approximant index of the observed point. -/
private def sliceA (w : ℕ) : ℕ := (prefListS w).getD (sliceQpos w) 0

/-- The even-track (integrand-name) value position. -/
private def sliceVpos (w : ℕ) : ℕ :=
  2 * (2 + Nat.pair (Nat.pair (sliceA w) (sliceJ w)) (sliceT w + 1))

/-- The oracle-free postprocessor of the slice realizer. -/
private def slicePost (w : ℕ) : ℕ :=
  if w.unpair.1 = 0 then (prefListS w).getD 0 0
  else if w.unpair.1 = 1 then (prefListS w).getD 2 0
  else (prefListS w).getD (sliceVpos w) 0

private theorem primrec_prefListS : Primrec prefListS :=
  (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd

private theorem primrec_headLS : Primrec headLS :=
  (Primrec.list_getD 0).comp primrec_prefListS (Primrec.const 0)

private theorem primrec_sliceT : Primrec sliceT :=
  primrec_unpairSnd.comp (Primrec.nat_sub.comp primrec_unpairFst (Primrec.const 2))

private theorem primrec_sliceJ : Primrec sliceJ :=
  primrec_unpairFst.comp (Primrec.nat_sub.comp primrec_unpairFst (Primrec.const 2))

private theorem primrec_sliceQpos : Primrec sliceQpos :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.succ.comp primrec_sliceT) primrec_headLS))

private theorem primrec_sliceA : Primrec sliceA :=
  (Primrec.list_getD 0).comp primrec_prefListS primrec_sliceQpos

private theorem primrec_sliceVpos : Primrec sliceVpos :=
  Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_add.comp (Primrec.const 2)
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp primrec_sliceA primrec_sliceJ)
      (Primrec.succ.comp primrec_sliceT)))

private theorem primrec_slicePost : Primrec slicePost :=
  Primrec.ite (Primrec.eq.comp primrec_unpairFst (Primrec.const 0))
    ((Primrec.list_getD 0).comp primrec_prefListS (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp primrec_unpairFst (Primrec.const 1))
      ((Primrec.list_getD 0).comp primrec_prefListS (Primrec.const 2))
      ((Primrec.list_getD 0).comp primrec_prefListS primrec_sliceVpos))

/-- Stage-1 → stage-2 bound of the slice chain: cover the odd-track query. -/
private def sliceB₁ (n h : ℕ) : ℕ := sliceQpos (Nat.pair n h) + 1

/-- Stage-2 → stage-3 bound: additionally cover the even-track value position. -/
private def sliceB₂ (n h : ℕ) : ℕ :=
  sliceVpos (Nat.pair n h) + 1 + (sliceQpos (Nat.pair n h) + 1)

private theorem primrec₂_sliceB₁ : Primrec₂ sliceB₁ :=
  (Primrec.succ.comp (primrec_sliceQpos.comp
    (Primrec₂.natPair.comp Primrec.fst Primrec.snd))).to₂

private theorem primrec₂_sliceB₂ : Primrec₂ sliceB₂ := by
  have hpair : Primrec fun p : ℕ × ℕ => Nat.pair p.1 p.2 :=
    Primrec₂.natPair.comp Primrec.fst Primrec.snd
  exact (Primrec.nat_add.comp
    (Primrec.succ.comp (primrec_sliceVpos.comp hpair))
    (Primrec.succ.comp (primrec_sliceQpos.comp hpair))).to₂

/-- The chained slice postprocessor value on any stream, in closed form. -/
private theorem slicePost_value (p : Baire) (n : ℕ) :
    slicePost (Nat.pair n (encode (streamTake p (sliceB₂ n (encode (streamTake p
        (sliceB₁ n (encode (streamTake p 3)))))))))
      = if n = 0 then p 0 else if n = 1 then p 2
        else p (2 * (2 + Nat.pair (Nat.pair
            (p (2 * ((n - 2).unpair.2 + 1 + p 0) + 1)) (n - 2).unpair.1)
          ((n - 2).unpair.2 + 1))) := by
  set t : ℕ := (n - 2).unpair.2 with ht_def
  set j : ℕ := (n - 2).unpair.1 with hj_def
  -- stage 1: the head is read from the length-3 prefix
  have hQ1 : sliceQpos (Nat.pair n (encode (streamTake p 3)))
      = 2 * (t + 1 + p 0) + 1 := by
    simp only [sliceQpos, sliceT, headLS, prefListS, Nat.unpair_pair, ofNat_encode]
    rw [streamTake_getD p (by omega : (0 : ℕ) < 3)]
  have hb1 : sliceB₁ n (encode (streamTake p 3)) = 2 * (t + 1 + p 0) + 2 := by
    rw [sliceB₁, hQ1]
  -- stage 2: the observed-point approximant is read from the stage-2 prefix
  set m₁ : ℕ := 2 * (t + 1 + p 0) + 2 with hm₁_def
  have hQ2 : sliceQpos (Nat.pair n (encode (streamTake p m₁)))
      = 2 * (t + 1 + p 0) + 1 := by
    simp only [sliceQpos, sliceT, headLS, prefListS, Nat.unpair_pair, ofNat_encode]
    rw [streamTake_getD p (by omega : (0 : ℕ) < m₁)]
  have hA2 : sliceA (Nat.pair n (encode (streamTake p m₁)))
      = p (2 * (t + 1 + p 0) + 1) := by
    rw [sliceA, hQ2]
    simp only [prefListS, Nat.unpair_pair, ofNat_encode]
    rw [streamTake_getD p (by omega : 2 * (t + 1 + p 0) + 1 < m₁)]
  have hV2 : sliceVpos (Nat.pair n (encode (streamTake p m₁)))
      = 2 * (2 + Nat.pair (Nat.pair (p (2 * (t + 1 + p 0) + 1)) j) (t + 1)) := by
    simp only [sliceVpos, sliceT, sliceJ, Nat.unpair_pair, hA2, ht_def, hj_def]
  have hb2 : sliceB₂ n (encode (streamTake p m₁))
      = 2 * (2 + Nat.pair (Nat.pair (p (2 * (t + 1 + p 0) + 1)) j) (t + 1)) + 1
        + (2 * (t + 1 + p 0) + 2) := by
    rw [sliceB₂, hV2, hQ2]
  -- stage 3: all needed coordinates lie inside the final prefix
  set V : ℕ := 2 * (2 + Nat.pair (Nat.pair (p (2 * (t + 1 + p 0) + 1)) j) (t + 1))
    with hV_def
  set m₂ : ℕ := V + 1 + (2 * (t + 1 + p 0) + 2) with hm₂_def
  rw [hb1, hb2]
  have hVpos3 : sliceVpos (Nat.pair n (encode (streamTake p m₂))) = V := by
    have hQ3 : sliceQpos (Nat.pair n (encode (streamTake p m₂)))
        = 2 * (t + 1 + p 0) + 1 := by
      simp only [sliceQpos, sliceT, headLS, prefListS, Nat.unpair_pair, ofNat_encode]
      rw [streamTake_getD p (by omega : (0 : ℕ) < m₂)]
    have hA3 : sliceA (Nat.pair n (encode (streamTake p m₂)))
        = p (2 * (t + 1 + p 0) + 1) := by
      rw [sliceA, hQ3]
      simp only [prefListS, Nat.unpair_pair, ofNat_encode]
      rw [streamTake_getD p (by omega : 2 * (t + 1 + p 0) + 1 < m₂)]
    simp only [sliceVpos, sliceT, sliceJ, Nat.unpair_pair, hA3, hV_def, ht_def, hj_def]
  simp only [slicePost, prefListS, Nat.unpair_pair, ofNat_encode, hVpos3]
  by_cases h0 : n = 0
  · rw [if_pos h0, if_pos h0, streamTake_getD p (by omega : (0 : ℕ) < m₂)]
  · rw [if_neg h0, if_neg h0]
    by_cases h1 : n = 1
    · rw [if_pos h1, if_pos h1, streamTake_getD p (by omega : (2 : ℕ) < m₂)]
    · rw [if_neg h1, if_neg h1, streamTake_getD p (by omega : V < m₂), hV_def]

variable {X Y : Type} [MetricSpace X] [MetricSpace Y]

/-- `L · 2⁻ᴸ ≤ 1` for natural `L`. -/
private theorem nat_mul_inv_pow_le_one (L : ℕ) : (L : ℝ) * (2 : ℝ)⁻¹ ^ L ≤ 1 := by
  rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
  exact_mod_cast Nat.lt_two_pow_self.le

/-- **The density slice is a computable map**
`blRep (P.prod Q) × cauchyRep P ⟶ blRep Q`, `(q, x) ↦ q (x, ·)`: the three-stage
adaptive prefix chain copies the heads and requeries the value stream through the
observed point's approximants. -/
theorem computableMap_blSlice (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    ComputableMap ((blRep (P.prod Q)).prod P.cauchyRep) (blRep Q)
      (fun w => w.1.slice w.2) := by
  obtain ⟨c, hc⟩ := exists_prefixChainCode (b₀ := fun _ => 3) (b₁ := sliceB₁)
    (b₂ := sliceB₂) (g := slicePost) (Primrec.const 3) primrec₂_sliceB₁
    primrec₂_sliceB₂ primrec_slicePost
  refine ⟨c, fun p w hpw => ?_⟩
  obtain ⟨hq, hx⟩ := Representation.prod_names_iff.mp hpw
  have hname : IntegrandName (P.prod Q) p.evenPart (p.evenPart 0) (p.evenPart 1)
      w.1.toFun := (blRep_names_iff (P.prod Q)).mp hq
  have hxp : P.NamesPoint p.oddPart w.2 := (P.cauchyRep_names_iff).mp hx
  set r : Baire := fun n => slicePost (Nat.pair n (encode (streamTake p (sliceB₂ n
    (encode (streamTake p (sliceB₁ n (encode (streamTake p 3))))))))) with hr_def
  have hrval : ∀ n, r n = if n = 0 then p 0 else if n = 1 then p 2
      else p (2 * (2 + Nat.pair (Nat.pair
          (p (2 * ((n - 2).unpair.2 + 1 + p 0) + 1)) (n - 2).unpair.1)
        ((n - 2).unpair.2 + 1))) := fun n => slicePost_value p n
  refine ⟨r, mem_evalStream.mpr fun n => ?_, ?_⟩
  · rw [hc p n]
    exact Part.mem_some _
  -- the emitted stream is a bounded-Lipschitz name of the slice
  refine (blRep_names_iff Q).mpr ?_
  have hr0 : r 0 = p.evenPart 0 := by rw [hrval 0]; rfl
  have hr1 : r 1 = p.evenPart 1 := by rw [hrval 1]; rfl
  have hLip : LipschitzWith ((p.evenPart 0 : ℕ) : ℝ≥0) fun y => w.1.toFun (w.2, y) := by
    simpa [Function.comp_def] using hname.lip.comp (LipschitzWith.prodMk_left w.2)
  refine ⟨rfl, rfl, by rw [hr0]; exact hLip, fun y => by rw [hr1]; exact hname.bound _,
    fun j t => ?_⟩
  -- the value-stream estimate
  have hidx : (2 + Nat.pair j t) - 2 = Nat.pair j t := by omega
  have hne0 : ¬(2 + Nat.pair j t = 0) := by omega
  have hne1 : ¬(2 + Nat.pair j t = 1) := by omega
  have hrv : r (2 + Nat.pair j t)
      = p.evenPart (2 + Nat.pair (Nat.pair (p.oddPart (t + 1 + p 0)) j) (t + 1)) := by
    rw [hrval, if_neg hne0, if_neg hne1, hidx, Nat.unpair_pair]
    rfl
  set k : ℕ := t + 1 + p 0 with hk_def
  set m' : ℕ := Nat.pair (p.oddPart k) j with hm'_def
  have happrox := hname.approx m' (t + 1)
  have hdense : (P.prod Q).dense m' = (P.dense (p.oddPart k), Q.dense j) := by
    change ((P.dense (Nat.unpair m').1, Q.dense (Nat.unpair m').2) : X × Y) = _
    rw [hm'_def, Nat.unpair_pair]
  have hL0 : p 0 = p.evenPart 0 := rfl
  have hslip : |w.1.toFun (P.dense (p.oddPart k), Q.dense j)
      - w.1.toFun (w.2, Q.dense j)| ≤ (2 : ℝ)⁻¹ ^ (t + 1) := by
    have hd := hname.lip.dist_le_mul (P.dense (p.oddPart k), Q.dense j)
      (w.2, Q.dense j)
    rw [Real.dist_eq] at hd
    have hdp : dist ((P.dense (p.oddPart k), Q.dense j) : X × Y) (w.2, Q.dense j)
        = dist (P.dense (p.oddPart k)) w.2 := by
      rw [Prod.dist_eq, dist_self]
      exact max_eq_left dist_nonneg
    have hxk : dist (P.dense (p.oddPart k)) w.2 ≤ (2 : ℝ)⁻¹ ^ k := hxp k
    have hLpow : ((p.evenPart 0 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ (2 : ℝ)⁻¹ ^ (t + 1) := by
      have hkeq : (2 : ℝ)⁻¹ ^ k = (2 : ℝ)⁻¹ ^ (t + 1) * (2 : ℝ)⁻¹ ^ (p 0) := by
        rw [← pow_add]
      rw [hkeq, ← mul_assoc, mul_comm ((p.evenPart 0 : ℕ) : ℝ), mul_assoc]
      calc (2 : ℝ)⁻¹ ^ (t + 1) * (((p.evenPart 0 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (p 0))
          ≤ (2 : ℝ)⁻¹ ^ (t + 1) * 1 :=
            mul_le_mul_of_nonneg_left (nat_mul_inv_pow_le_one _) (by positivity)
        _ = (2 : ℝ)⁻¹ ^ (t + 1) := mul_one _
    calc |w.1.toFun (P.dense (p.oddPart k), Q.dense j) - w.1.toFun (w.2, Q.dense j)|
        ≤ ((p.evenPart 0 : ℕ) : ℝ)
            * dist ((P.dense (p.oddPart k), Q.dense j) : X × Y) (w.2, Q.dense j) := hd
      _ = ((p.evenPart 0 : ℕ) : ℝ) * dist (P.dense (p.oddPart k)) w.2 := by rw [hdp]
      _ ≤ ((p.evenPart 0 : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ k :=
          mul_le_mul_of_nonneg_left hxk (by positivity)
      _ ≤ (2 : ℝ)⁻¹ ^ (t + 1) := hLpow
  calc |((ratOfCode (r (2 + Nat.pair j t)) : ℚ) : ℝ) - (w.1.slice w.2).toFun (Q.dense j)|
      ≤ |((ratOfCode (r (2 + Nat.pair j t)) : ℚ) : ℝ)
            - w.1.toFun ((P.prod Q).dense m')|
          + |w.1.toFun ((P.prod Q).dense m') - w.1.toFun (w.2, Q.dense j)| :=
        abs_sub_le _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (t + 1) + (2 : ℝ)⁻¹ ^ (t + 1) := by
        refine add_le_add ?_ ?_
        · rw [hrv]
          exact happrox
        · rw [hdense]
          exact hslip
    _ = (2 : ℝ)⁻¹ ^ t := by
        rw [pow_succ]
        ring

end SliceRealizer

/-! ### Coded rational riders for the candidate weights (private engine)

The shared combinators live in `Metric/RatCodeArith.lean`; local here are the
positive-part, inverse-successor and fusion codes this unit needs on top of them. -/

section CodedArithmetic

/-- The clamped weight is the decoded clamp code. -/
private theorem wRaw_eq_ratOfCode_clampCode (c : ℕ) : wRaw c = ratOfCode (clampCode c) :=
  (ratOfCode_clampCode c).symm

/-- The nonnegative part of a rational code: `zeroCode` on nonpositive values. -/
private def posPartCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 then zeroCode else m

private theorem ratOfCode_posPartCode (m : ℕ) :
    ratOfCode (posPartCode m) = max 0 (ratOfCode m) := by
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  rw [posPartCode]
  split_ifs with h
  · have hab : (m.unpair.1.unpair.1 : ℚ) ≤ (m.unpair.1.unpair.2 : ℚ) := by
      exact_mod_cast h
    rw [ratOfCode_zeroCode, eq_comm, max_eq_left]
    unfold ratOfCode
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  · have hba : (m.unpair.1.unpair.2 : ℚ) ≤ (m.unpair.1.unpair.1 : ℚ) := by
      exact_mod_cast (Nat.lt_of_not_le h).le
    rw [eq_comm, max_eq_right]
    unfold ratOfCode
    exact div_nonneg (by linarith) hden.le

/-- The code of `1 / (b + 1)`. -/
private theorem ratOfCode_invSucc (b : ℕ) :
    ratOfCode (Nat.pair (Nat.pair 1 0) b) = 1 / ((b : ℚ) + 1) := by
  simp [ratOfCode]

/-- **The fused candidate-weight code**: `wRaw w · (max 0 (ratOfCode c)) / (b + 1)`. -/
private def fuseCode (w c b : ℕ) : ℕ :=
  mulCode (clampCode w) (mulCode (posPartCode c) (Nat.pair (Nat.pair 1 0) b))

private theorem ratOfCode_fuseCode (w c b : ℕ) :
    ratOfCode (fuseCode w c b)
      = wRaw w * (max 0 (ratOfCode c) * (1 / ((b : ℚ) + 1))) := by
  rw [fuseCode, ratOfCode_mulCode, ratOfCode_mulCode, ratOfCode_clampCode,
    ratOfCode_posPartCode, ratOfCode_invSucc]
  rfl

/-- On values in `[0,1]`, the clamp is the identity. -/
private theorem wRaw_eq_of_mem {m : ℕ} (h0 : 0 ≤ ratOfCode m) (h1 : ratOfCode m ≤ 1) :
    wRaw m = ratOfCode m := by
  unfold wRaw
  rw [min_eq_right h1, max_eq_right h0]

section PrimrecArithmetic

open Primrec

private theorem primrec_posPartCode : Primrec posPartCode :=
  Primrec.ite
    (Primrec.nat_le.comp (primrec_unpairFst.comp primrec_unpairFst)
      (primrec_unpairSnd.comp primrec_unpairFst))
    (const zeroCode) Primrec.id

private theorem primrec₂_fuseWithBound :
    Primrec₂ fun (cb : ℕ × ℕ) (w : ℕ) => fuseCode w cb.1 cb.2 :=
  (primrec₂_mulCode.comp (primrec_clampCode.comp snd)
    (primrec₂_mulCode.comp (primrec_posPartCode.comp (fst.comp fst))
      (Primrec₂.natPair.comp (const (Nat.pair 1 0)) (snd.comp fst)))).to₂

/-- Powering is primitive recursive (bridge from `Nat.Primrec.pow`). -/
private theorem primrec₂_pow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

end PrimrecArithmetic

/-- The stage-`k` search test on a rational code `m`: `0` exactly when the coded value
exceeds the threshold `2 · (2⁻¹)ᵏ` (private re-derivation of unit 33's search test). -/
private def searchVal (m k : ℕ) : ℕ :=
  if 2 * (m.unpair.2 + 1) + m.unpair.1.unpair.2 * 2 ^ k < m.unpair.1.unpair.1 * 2 ^ k
  then 0 else 1

/-- The search test hits zero exactly at the rational threshold comparison. -/
private theorem searchVal_eq_zero_iff {m k : ℕ} :
    searchVal m k = 0 ↔ 2 * ((2 : ℚ)⁻¹) ^ k < ratOfCode m := by
  have hpk : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  have hq : (2 * (m.unpair.2 + 1) + m.unpair.1.unpair.2 * 2 ^ k
        < m.unpair.1.unpair.1 * 2 ^ k)
      ↔ 2 * ((2 : ℚ)⁻¹) ^ k < ratOfCode m := by
    rw [ratOfCode, inv_pow, ← div_eq_mul_inv, div_lt_div_iff₀ hpk hden, sub_mul,
      lt_sub_iff_add_lt]
    exact_mod_cast Iff.rfl
  rw [searchVal]
  split_ifs with h
  · exact iff_of_true rfl (hq.mp h)
  · exact iff_of_false (by simp) fun hlt => h (hq.mpr hlt)

/-- The packed form of the search test is primitive recursive. -/
private theorem primrec_searchValPost :
    Primrec fun v : ℕ => searchVal v.unpair.1 v.unpair.2 := by
  have ha : Primrec fun v : ℕ => v.unpair.1.unpair.1.unpair.1 :=
    primrec_unpairFst.comp (primrec_unpairFst.comp primrec_unpairFst)
  have hb : Primrec fun v : ℕ => v.unpair.1.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp (primrec_unpairFst.comp primrec_unpairFst)
  have hc : Primrec fun v : ℕ => 2 * (v.unpair.1.unpair.2 + 1) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (primrec_unpairSnd.comp primrec_unpairFst))
  have hpow : Primrec fun v : ℕ => 2 ^ v.unpair.2 :=
    primrec₂_pow.comp (Primrec.const 2) primrec_unpairSnd
  exact (Primrec.ite
    (Primrec.nat_lt.comp
      (Primrec.nat_add.comp hc (Primrec.nat_mul.comp hb hpow))
      (Primrec.nat_mul.comp ha hpow))
    (Primrec.const 0) (Primrec.const 1)).of_eq fun v => rfl

/-- Names of `realRep` are the fast rational approximation streams (private
re-derivation of the unit 33 names bridge). -/
private theorem realRep_names_iff {p : Baire} {x : ℝ} :
    realRep.Names p x ↔
      ∀ n : ℕ, |((ratOfCode (p n) : ℚ) : ℝ) - x| ≤ (2 : ℝ)⁻¹ ^ n := by
  refine Iff.trans realPresentation.cauchyRep_names_iff ?_
  constructor
  · intro h n
    have hn := h n
    rw [Real.dist_eq] at hn
    exact hn
  · intro h n
    rw [Real.dist_eq]
    exact h n

end CodedArithmetic

/-! ### Reweighting decoded atomics: the Dirac-sum representation -/

section AtomicReweight

variable {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable (Q : ComputableMetricPresentation Y)

omit [MetricSpace Y] [BorelSpace Y] in
/-- Bounded measurable functions are integrable against finite measures (private
re-derivation). -/
private theorem integrable_of_abs_le {f : Y → ℝ} {B : ℝ} (hfm : StronglyMeasurable f)
    (hB : ∀ y, |f y| ≤ B) (ν : Measure Y) [IsFiniteMeasure ν] : Integrable f ν :=
  ⟨hfm.aestronglyMeasurable, .of_bounded (C := B)
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hB y)⟩

omit [MetricSpace Y] [BorelSpace Y] in
/-- Restriction distributes over finite sums of measures. -/
private theorem restrict_finsetSum {k : ℕ} (m : Fin k → Measure Y) (A : Set Y) :
    (∑ i, m i).restrict A = ∑ i, (m i).restrict A := by
  ext S hS
  rw [Measure.restrict_apply hS, Measure.finsetSum_apply, Measure.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => (Measure.restrict_apply hS).symm

omit [BorelSpace Y] in
/-- Set integrals against a decoded atomic with nonzero total weight: weighted
indicator sums. -/
private theorem setIntegral_atomicOfList_ne {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0)
    {f : Y → ℝ} {B : ℝ} (hfm : StronglyMeasurable f) (hB : ∀ y, |f y| ≤ B)
    {A : Set Y} (hA : MeasurableSet A) :
    ∫ y in A, f y ∂(atomicOfList Q l).toMeasure
      = ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
          * A.indicator f (Q.dense l[i].1) := by
  classical
  rw [toMeasure_atomicOfList_of_ne _ h0, restrict_finsetSum]
  rw [integral_finsetSum_measure fun i _ => by
    rw [Measure.restrict_smul]
    exact ((integrable_of_abs_le hfm hB _).restrict).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (normWt_nonneg h0 i), setIntegral_dirac' hfm _ hA,
    smul_eq_mul, Set.indicator_apply]

omit [BorelSpace Y] in
/-- Integrals against a decoded atomic with nonzero total weight: weighted value
sums. -/
private theorem integral_atomicOfList_ne {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0)
    {f : Y → ℝ} {B : ℝ} (hfm : StronglyMeasurable f) (hB : ∀ y, |f y| ≤ B) :
    ∫ y, f y ∂(atomicOfList Q l).toMeasure
      = ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) * f (Q.dense l[i].1) := by
  rw [← setIntegral_univ (f := f) (μ := (atomicOfList Q l).toMeasure),
    setIntegral_atomicOfList_ne Q h0 hfm hB MeasurableSet.univ]
  simp

/-- **The Dirac-sum representation of a reweighted atomic** (nonzero total weight):
the normalized reweighting of a decoded atomic is the same Dirac sum with weights
`aᵢ f(yᵢ) / Z`. -/
private theorem reweight_atomicOfList_toMeasure {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0)
    (f : BoundedLipschitzFun Y) (h₂ : PosDensityPair (f, atomicOfList Q l)) :
    (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
      = ∑ i : Fin l.length,
          ENNReal.ofReal (((wRaw l[i].2 / wSumL l : ℚ) : ℝ) * f.toFun (Q.dense l[i].1)
              / ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure)
            • Measure.dirac (Q.dense l[i].1) := by
  obtain ⟨L, B, hL, hB⟩ := f.exists_bounds
  have hfm : StronglyMeasurable f.toFun := hL.continuous.stronglyMeasurable
  have hZpos : 0 < ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure := h₂.2
  ext A hA
  rw [reweight_toMeasure_apply _ hA, sum_smul_dirac_apply _ _ hA]
  change ENNReal.ofReal ((∫ y in A, f.toFun y ∂(atomicOfList Q l).toMeasure)
      / ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure) = _
  rw [setIntegral_atomicOfList_ne Q h0 hfm hB hA, Finset.sum_div,
    ENNReal.ofReal_sum_of_nonneg fun i _ => by
      have hnn := h₂.1
      have hind : 0 ≤ A.indicator f.toFun (Q.dense l[i].1) :=
        Set.indicator_apply_nonneg fun _ => hnn _
      have := normWt_nonneg h0 i
      positivity]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : Q.dense l[i].1 ∈ A
  · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi]
  · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem hi, mul_zero, zero_div,
      ENNReal.ofReal_zero]

/-- The normalized reweighting of a point mass is the point mass. -/
private theorem reweight_toMeasure_of_dirac {f : BoundedLipschitzFun Y}
    {ν : ProbabilityMeasure Y} {y : Y} (hν : ν.toMeasure = Measure.dirac y)
    (h : PosDensityPair (f, ν)) :
    (reweight ⟨(f, ν), h⟩).toMeasure = Measure.dirac y := by
  classical
  obtain ⟨L, B, hL, hB⟩ := f.exists_bounds
  have hfm : StronglyMeasurable f.toFun := hL.continuous.stronglyMeasurable
  have hZ : ∫ y', f.toFun y' ∂ν.toMeasure = f.toFun y := by
    rw [hν]
    exact integral_dirac' _ _ hfm
  have hfy : 0 < f.toFun y := by
    rw [← hZ]
    exact h.2
  ext A hA
  rw [reweight_toMeasure_apply _ hA, Measure.dirac_apply' _ hA]
  change ENNReal.ofReal ((∫ y' in A, f.toFun y' ∂ν.toMeasure)
      / ∫ y', f.toFun y' ∂ν.toMeasure) = _
  have hset : ∫ y' in A, f.toFun y' ∂ν.toMeasure = if y ∈ A then f.toFun y else 0 := by
    rw [hν]
    exact setIntegral_dirac' hfm _ hA
  rw [hset, hZ]
  by_cases hy : y ∈ A
  · rw [if_pos hy, div_self hfy.ne', ENNReal.ofReal_one, Set.indicator_of_mem hy]
    rfl
  · rw [if_neg hy, zero_div, ENNReal.ofReal_zero, Set.indicator_of_notMem hy]

omit [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
/-- Monotonicity of the pinned rate. -/
private theorem inv_pow_le_inv_pow {a b : ℕ} (h : b ≤ a) :
    (2 : ℝ)⁻¹ ^ a ≤ (2 : ℝ)⁻¹ ^ b :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

omit [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
private theorem nat_cast_le_two_pow (m : ℕ) : (m : ℝ) ≤ 2 ^ m := by
  exact_mod_cast Nat.lt_two_pow_self.le

omit [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] in
private theorem two_pow_mul_inv_pow (m : ℕ) : (2 : ℝ) ^ m * (2 : ℝ)⁻¹ ^ m = 1 := by
  rw [← mul_pow]
  norm_num

private theorem integ_le_integ_add (f : BoundedLipschitzFun Y) (ν : ProbabilityMeasure Y)
    (l : List (ℕ × ℕ)) {Ψ : Baire} {L B : ℕ} (hname : IntegrandName Q Ψ L B f.toFun)
    (hnn : ∀ y, 0 ≤ f.toFun y) {ε : ℝ} (hε0 : 0 < ε)
    (hedist : levyProkhorovEDist ν.toMeasure (atomicOfList Q l).toMeasure
      < ENNReal.ofReal ε) :
    (∫ y, f.toFun y ∂ν.toMeasure)
      ≤ (∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure) + ((L : ℝ) + B) * ε := by
  haveI : IsProbabilityMeasure ν.toMeasure := ν.prop
  haveI : IsProbabilityMeasure (atomicOfList Q l).toMeasure := (atomicOfList Q l).prop
  have hcore := setIntegral_le_thickening_add hname.lip hnn hname.bound hε0 hedist
    MeasurableSet.univ
  push_cast at hcore
  have huniv : ∫ y in Set.univ, f.toFun y ∂ν.toMeasure = ∫ y, f.toFun y ∂ν.toMeasure :=
    setIntegral_univ
  have hthick : (∫ y in thickening ε Set.univ, f.toFun y ∂(atomicOfList Q l).toMeasure)
      ≤ ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure := by
    rw [← setIntegral_univ (f := f.toFun) (μ := (atomicOfList Q l).toMeasure)]
    exact setIntegral_mono_set (integrable_blFun f _).integrableOn
      (Filter.Eventually.of_forall fun y => hnn y) (Set.subset_univ _).eventuallyLE
  rw [huniv] at hcore
  linarith

/-- The `(L + B) · ε` slack, with `ε = 2 · (2⁻¹)ˢ` and `s = n + 4 + (L + B) + k`, is at
most `(2⁻¹)^(n+3+k)` — the pure pinned-rate arithmetic. -/
private theorem LBε_le {L B n k s : ℕ} (hs : s = n + 4 + (L + B) + k) :
    ((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s) ≤ (2 : ℝ)⁻¹ ^ (n + 3 + k) := by
  have h1 : ((L : ℝ) + B) ≤ 2 ^ (L + B) := by
    have h := nat_cast_le_two_pow (L + B)
    push_cast at h
    linarith
  have h2 : (2 : ℝ)⁻¹ ^ s
      = (2 : ℝ)⁻¹ ^ (n + 3 + k) * ((2 : ℝ)⁻¹ ^ (L + B) * (2 : ℝ)⁻¹) := by
    have hsum : s = (n + 3 + k) + ((L + B) + 1) := by omega
    rw [hsum, pow_add, pow_add (2 : ℝ)⁻¹ (L + B) 1, pow_one]
  calc ((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s) = ((L : ℝ) + B) * 2 * (2 : ℝ)⁻¹ ^ s := by ring
    _ ≤ 2 ^ (L + B) * 2 * (2 : ℝ)⁻¹ ^ s := by
        have hp : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ s := by positivity
        nlinarith
    _ = (2 : ℝ)⁻¹ ^ (n + 3 + k) * ((2 : ℝ) ^ (L + B) * (2 : ℝ)⁻¹ ^ (L + B))
          * (2 * (2 : ℝ)⁻¹) := by rw [h2]; ring
    _ = (2 : ℝ)⁻¹ ^ (n + 3 + k) := by rw [two_pow_mul_inv_pow]; norm_num

/-- The certified lower bound transfers to the atomic normalizer: `(2⁻¹)^(k+1) ≤ Zs`. -/
private theorem Zs_lb_of {Z Zs t : ℝ} {n k : ℕ} (hZZs : Z ≤ Zs + t)
    (hLBε : t ≤ (2 : ℝ)⁻¹ ^ (n + 3 + k)) (hlow : (2 : ℝ)⁻¹ ^ k < Z) :
    (2 : ℝ)⁻¹ ^ (k + 1) ≤ Zs := by
  have hks : (2 : ℝ)⁻¹ ^ (n + 3 + k) ≤ (2 : ℝ)⁻¹ ^ (k + 1) := inv_pow_le_inv_pow (by omega)
  have hkk : (2 : ℝ)⁻¹ ^ k = 2 * (2 : ℝ)⁻¹ ^ (k + 1) := by rw [pow_succ]; ring
  linarith

/-- Stability of the normalized reweighting from `ν` to its stage-`s` atomic approximant,
at the certified normalizer floor `(2⁻¹)ᵏ`; the `ε + 2(L+B)ε/z` estimate collapses to the
pinned budget `(2⁻¹)^(n+1)`. -/
private theorem reweight_stab_le (f : BoundedLipschitzFun Y) (ν : ProbabilityMeasure Y)
    (l : List (ℕ × ℕ)) (hw : PosDensityPair (f, ν))
    (h₂ : PosDensityPair (f, atomicOfList Q l)) {Ψ : Baire} {L B : ℕ}
    (hname : IntegrandName Q Ψ L B f.toFun) {n k s : ℕ} (hs : s = n + 4 + (L + B) + k)
    (hlow : (2 : ℝ)⁻¹ ^ k < ∫ y, f.toFun y ∂ν.toMeasure)
    (hdε : levyProkhorovDist ν.toMeasure (atomicOfList Q l).toMeasure
      < 2 * (2 : ℝ)⁻¹ ^ s) :
    levyProkhorovDist (reweight ⟨(f, ν), hw⟩).toMeasure
        (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  have hε0 : (0 : ℝ) < 2 * (2 : ℝ)⁻¹ ^ s := by positivity
  have h := levyProkhorovDist_reweight_le f hw h₂ hname.lip hname.bound
    (z := (2 : ℝ)⁻¹ ^ k) (by positivity) hlow.le hε0 hdε
  push_cast at h
  refine h.trans ?_
  have hεsmall : 2 * (2 : ℝ)⁻¹ ^ s ≤ (2 : ℝ)⁻¹ ^ (n + 2) := by
    have h1 : (2 : ℝ)⁻¹ ^ s ≤ (2 : ℝ)⁻¹ ^ (n + 3) := inv_pow_le_inv_pow (by omega)
    have h2 : 2 * (2 : ℝ)⁻¹ ^ (n + 3) = (2 : ℝ)⁻¹ ^ (n + 2) := by rw [pow_succ]; ring
    linarith
  have htail : 2 * ((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s) / (2 : ℝ)⁻¹ ^ k
      ≤ (2 : ℝ)⁻¹ ^ (n + 2) := by
    rw [div_le_iff₀ (by positivity)]
    have hr : (2 : ℝ)⁻¹ ^ (n + 2) * (2 : ℝ)⁻¹ ^ k = 2 * (2 : ℝ)⁻¹ ^ (n + 3 + k) := by
      rw [← pow_add, show n + 3 + k = (n + 2 + k) + 1 by omega, pow_succ]; ring
    have hLBε := LBε_le (L := L) (B := B) (n := n) (k := k) (s := s) hs
    calc 2 * ((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s)
          = 2 * (((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s)) := by ring
      _ ≤ 2 * (2 : ℝ)⁻¹ ^ (n + 3 + k) := by linarith
      _ = (2 : ℝ)⁻¹ ^ (n + 2) * (2 : ℝ)⁻¹ ^ k := hr.symm
  have hsum : (2 : ℝ)⁻¹ ^ (n + 2) + (2 : ℝ)⁻¹ ^ (n + 2) = (2 : ℝ)⁻¹ ^ (n + 1) := by
    rw [pow_succ]; ring
  linarith

-- Seal the coded-rational layer as irreducible: the fused-weight equalities are proved
-- through the `ratOfCode_*` rewrite lemmas, and unfolding `ratOfCode`/`wRaw` into their
-- `Nat.pair`/`Nat.unpair` numeral bodies triggers `whnf` storms.
-- Seal the fused-weight code as irreducible: the fused weights are manipulated only
-- through `ratOfCode_fuseCode`, and letting `isDefEq`/`kabstract` unfold `fuseCode` into
-- its nested `Nat.pair` body (then `ratOfCode`'s `Nat.unpair`) triggers `whnf` storms.
attribute [local irreducible] fuseCode

/-- Degenerate branch of the candidate estimate: when the stage-`s` atom list has zero
total weight, both the reweighted atomic and the fused candidate collapse to the default
point mass `dirac (Q.dense 0)`, so the Lévy–Prokhorov distance is `0`. -/
private theorem reweight_atomic_candidate_le_zero (f : BoundedLipschitzFun Y)
    (l : List (ℕ × ℕ)) (h₂ : PosDensityPair (f, atomicOfList Q l)) {Ψ : Baire} {B n s : ℕ}
    (h0 : wSumL l = 0) :
    levyProkhorovDist (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
        (atomicOfList Q (l.map fun pr =>
          (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure
      ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  set l' : List (ℕ × ℕ) := l.map fun pr =>
    (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B) with hl'_def
  have hνdirac : (atomicOfList Q l).toMeasure = Measure.dirac (Q.dense 0) :=
    toMeasure_atomicOfList_of_eq _ h0
  have hall := wRaw_all_zero l h0
  have h0' : wSumL l' = 0 := by
    rw [wSumL, hl'_def, List.map_map]
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp hx
    change wRaw (fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B) = 0
    have hz : ratOfCode (fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B) = 0 := by
      rw [ratOfCode_fuseCode, hall pr hpr, zero_mul]
    rw [wRaw_eq_of_mem (le_of_eq hz.symm)
      (by rw [hz]; norm_num : ratOfCode (fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B) ≤ 1),
      hz]
  rw [reweight_toMeasure_of_dirac hνdirac h₂, toMeasure_atomicOfList_of_eq _ h0',
    levyProkhorovDist_self]
  positivity

/-- The clamped fused candidate weight in normalized-perturbation form: with the per-atom
threshold `max 0 (ratOfCode e) ≤ B + 1`, the `[0,1]` clamp is inactive and the fused
weight is the raw weight scaled by the normalized coefficient `max 0 (ratOfCode e)/(B+1)`.
Extracted so the main-branch estimate below stays within the default heartbeat budget. -/
private theorem wRaw_fuseCode_eq (w e B : ℕ)
    (hc_le : max 0 (ratOfCode e) ≤ (B : ℚ) + 1) :
    wRaw (fuseCode w e B) = wRaw w * (max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1))) := by
  have hval : ratOfCode (fuseCode w e B)
      = wRaw w * (max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1))) := ratOfCode_fuseCode w e B
  have hcnn : (0 : ℚ) ≤ max 0 (ratOfCode e) := le_max_left _ _
  have h0v : 0 ≤ wRaw w * (max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1))) :=
    mul_nonneg (wRaw_nonneg _) (mul_nonneg hcnn (by positivity))
  have h1v : wRaw w * (max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1))) ≤ 1 := by
    have hw1 : wRaw w ≤ 1 := max_le zero_le_one (min_le_left _ _)
    have hcB0 : 0 ≤ max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1)) :=
      mul_nonneg hcnn (by positivity)
    have hcB : max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      exact hc_le
    calc wRaw w * (max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1)))
        ≤ 1 * (max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1))) :=
          mul_le_mul_of_nonneg_right hw1 hcB0
      _ = max 0 (ratOfCode e) * (1 / ((B : ℚ) + 1)) := one_mul _
      _ ≤ 1 := hcB
  rw [wRaw_eq_of_mem (by rw [hval]; exact h0v) (by rw [hval]; exact h1v), hval]

/-- Pure real-cast identity: a shared rational denominator cancels under the cast. -/
private theorem cast_ratio_of_common_denom (Ni D S : ℚ) (hS : S ≠ 0) :
    ((Ni / S : ℚ) : ℝ) / ((D / S : ℚ) : ℝ) = ((Ni / D : ℚ) : ℝ) := by
  have hkey : Ni / S / (D / S) = Ni / D := by
    rw [div_div_div_cancel_right₀]
    exact hS
  rw [← Rat.cast_div, hkey]

/-- Positivity of a rational sum transfers from the positivity of its real-cast
normalization by a positive rational denominator. -/
private theorem sum_num_pos_of_cast_pos {m : ℕ} (N : Fin m → ℚ) {S : ℚ} (hS : 0 < S)
    (hpos : 0 < ∑ i : Fin m, ((N i / S : ℚ) : ℝ)) : 0 < ∑ i : Fin m, N i := by
  have hcast : ((∑ i : Fin m, N i / S : ℚ) : ℝ) = ∑ i : Fin m, ((N i / S : ℚ) : ℝ) := by
    push_cast
    ring
  have hq : (0 : ℚ) < ∑ i : Fin m, N i / S := by
    have hr : (0 : ℝ) < ((∑ i : Fin m, N i / S : ℚ) : ℝ) := by rw [hcast]; exact hpos
    exact_mod_cast hr
  rw [← Finset.sum_div] at hq
  exact (div_pos_iff.mp hq).resolve_right (fun h => absurd h.2 (not_lt.mpr hS.le)) |>.1

/-- The total weight of the fused candidate list factors through the shared `1/(B+1)`. -/
private theorem wSumL_map_fuse (l : List (ℕ × ℕ)) (Ψ : Baire) (s B : ℕ)
    (c : Fin l.length → ℚ)
    (hc : ∀ i, c i = max 0 (ratOfCode (Ψ (2 + Nat.pair l[i].1 s))))
    (hbd : ∀ i, c i ≤ (B : ℚ) + 1) :
    wSumL (l.map fun pr => (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))
      = (∑ i : Fin l.length, wRaw l[i].2 * c i) * (1 / ((B : ℚ) + 1)) := by
  rw [Finset.sum_mul, wSumL, List.map_map,
    listSum_map_eq_finSum l ((fun pr : ℕ × ℕ => wRaw pr.2) ∘ fun pr : ℕ × ℕ =>
      (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))]
  refine Finset.sum_congr rfl fun i _ => ?_
  change wRaw (fuseCode l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B)
    = wRaw l[i].2 * c i * (1 / ((B : ℚ) + 1))
  rw [hc i, wRaw_fuseCode_eq l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B (hc i ▸ hbd i), mul_assoc]

/-- The candidate weight normalized by the fused total equals the perturbed normalized
weight `bv i / ∑ bv` in the real cast (`bv j = (wRaw l[j].2 / wSumL l) · c j`). -/
private theorem cand_wt_cast (l : List (ℕ × ℕ)) (Ψ : Baire) (s B : ℕ)
    (c : Fin l.length → ℚ)
    (hc : ∀ i, c i = max 0 (ratOfCode (Ψ (2 + Nat.pair l[i].1 s))))
    (hbd : ∀ i, c i ≤ (B : ℚ) + 1) (hW : (0 : ℚ) < wSumL l)
    (i : Fin l.length) :
    ((wRaw (fuseCode l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B)
        / wSumL (l.map fun pr => (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B)) : ℚ) : ℝ)
      = ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) * ((c i : ℚ) : ℝ)
        / ∑ j : Fin l.length, ((wRaw l[j].2 / wSumL l : ℚ) : ℝ) * ((c j : ℚ) : ℝ) := by
  have hQrat : wRaw (fuseCode l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B)
        / wSumL (l.map fun pr => (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))
      = (wRaw l[i].2 * c i) / ∑ j : Fin l.length, wRaw l[j].2 * c j := by
    rw [wRaw_fuseCode_eq l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B (hc i ▸ hbd i), ← hc i,
      wSumL_map_fuse l Ψ s B c hc hbd, ← mul_assoc,
      mul_div_mul_right _ _ (by positivity : (1 : ℚ) / ((B : ℚ) + 1) ≠ 0)]
  rw [hQrat]
  have hbv_cast : ∀ j : Fin l.length,
      ((wRaw l[j].2 / wSumL l : ℚ) : ℝ) * ((c j : ℚ) : ℝ)
        = ((wRaw l[j].2 * c j / wSumL l : ℚ) : ℝ) := by
    intro j
    push_cast
    ring
  have hSbv_cast : (∑ j : Fin l.length, ((wRaw l[j].2 / wSumL l : ℚ) : ℝ) * ((c j : ℚ) : ℝ))
      = (((∑ j : Fin l.length, wRaw l[j].2 * c j) / wSumL l : ℚ) : ℝ) := by
    rw [Finset.sum_congr rfl fun j _ => hbv_cast j]
    push_cast
    rw [Finset.sum_div]
  rw [hbv_cast i, hSbv_cast,
    cast_ratio_of_common_denom (wRaw l[i].2 * c i)
      (∑ j : Fin l.length, wRaw l[j].2 * c j) (wSumL l) hW.ne']

/-- Main branch of the candidate estimate: with nonzero total weight both measures are
the same finite Dirac sum with perturbed normalized weights, and the certified normalizer
floor `(2⁻¹)^(k+1) ≤ Zs` bounds the normalized-weight perturbation by `(2⁻¹)^(n+1)`. -/
private theorem reweight_atomic_candidate_le_pos (f : BoundedLipschitzFun Y)
    (l : List (ℕ × ℕ)) (h₂ : PosDensityPair (f, atomicOfList Q l)) {Ψ : Baire} {L B : ℕ}
    (hname : IntegrandName Q Ψ L B f.toFun) (hnn : ∀ y, 0 ≤ f.toFun y) {n k s : ℕ}
    (hs : s = n + 4 + (L + B) + k)
    (hZs_lb : (2 : ℝ)⁻¹ ^ (k + 1) ≤ ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure)
    (h0 : ¬wSumL l = 0) :
    levyProkhorovDist (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
        (atomicOfList Q (l.map fun pr =>
          (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure
      ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  haveI : IsProbabilityMeasure (atomicOfList Q l).toMeasure := (atomicOfList Q l).prop
  have hBnd := hname.bound
  have hfm : StronglyMeasurable f.toFun := hname.lip.continuous.stronglyMeasurable
  set l' : List (ℕ × ℕ) := l.map fun pr =>
    (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B) with hl'_def
  set Zs : ℝ := ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure with hZs_def
  set c : Fin l.length → ℚ :=
    fun i => max 0 (ratOfCode (Ψ (2 + Nat.pair l[i].1 s))) with hc_def
  have hc0 : ∀ i, (0 : ℚ) ≤ c i := fun i => le_max_left _ _
  set aw : Fin l.length → ℝ := fun i => ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
    with haw_def
  have haw0 : ∀ i, 0 ≤ aw i := fun i => normWt_nonneg h0 i
  set av : Fin l.length → ℝ := fun i => aw i * f.toFun (Q.dense l[i].1) with hav_def
  set bv : Fin l.length → ℝ := fun i => aw i * ((c i : ℚ) : ℝ) with hbv_def
  -- per-atom value estimates
  have hci : ∀ i : Fin l.length,
      |((c i : ℚ) : ℝ) - f.toFun (Q.dense l[i].1)| ≤ (2 : ℝ)⁻¹ ^ s := by
    intro i
    have happ := hname.approx l[i].1 s
    have hcast : ((c i : ℚ) : ℝ)
        = max ((ratOfCode (Ψ (2 + Nat.pair l[i].1 s)) : ℚ) : ℝ) 0 := by
      rw [hc_def]
      push_cast [Rat.cast_max]
      rw [max_comm]
    have hfmax : f.toFun (Q.dense l[i].1) = max (f.toFun (Q.dense l[i].1)) 0 :=
      (max_eq_left (hnn _)).symm
    calc |((c i : ℚ) : ℝ) - f.toFun (Q.dense l[i].1)|
        = |max ((ratOfCode (Ψ (2 + Nat.pair l[i].1 s)) : ℚ) : ℝ) 0
            - max (f.toFun (Q.dense l[i].1)) 0| := by rw [hcast, ← hfmax]
      _ ≤ |((ratOfCode (Ψ (2 + Nat.pair l[i].1 s)) : ℚ) : ℝ)
            - f.toFun (Q.dense l[i].1)| := abs_max_sub_max_le_abs _ _ _
      _ ≤ (2 : ℝ)⁻¹ ^ s := happ
  have hsumab : ∑ i, |av i - bv i| ≤ (2 : ℝ)⁻¹ ^ s := by
    calc ∑ i, |av i - bv i|
        = ∑ i, aw i * |f.toFun (Q.dense l[i].1) - ((c i : ℚ) : ℝ)| := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hav_def, hbv_def, ← mul_sub, abs_mul, abs_of_nonneg (haw0 i)]
      _ ≤ ∑ i, aw i * (2 : ℝ)⁻¹ ^ s := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (haw0 i)
          rw [abs_sub_comm]
          exact hci i
      _ = (∑ i, aw i) * (2 : ℝ)⁻¹ ^ s := (Finset.sum_mul _ _ _).symm
      _ = (2 : ℝ)⁻¹ ^ s := by rw [sum_normWt h0, one_mul]
  have hZs_eq : Zs = ∑ i, av i := by
    rw [hZs_def, integral_atomicOfList_ne Q h0 hfm hBnd]
  have hη : (2 : ℝ)⁻¹ ^ s < (2 : ℝ)⁻¹ ^ (k + 1) :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  -- normalized-weight perturbation
  have hpert := sum_abs_normalized_le av bv
    (fun i => mul_nonneg (haw0 i) (by exact_mod_cast hc0 i))
    (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (k + 1))
    (by rw [← hZs_eq]; exact hZs_lb) hsumab hη
  have hbudget : 2 * (2 : ℝ)⁻¹ ^ s / (2 : ℝ)⁻¹ ^ (k + 1) ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (2 : ℝ)⁻¹ ^ s ≤ (2 : ℝ)⁻¹ ^ (n + k + 3) := inv_pow_le_inv_pow (by omega)
    have h2 : (2 : ℝ)⁻¹ ^ (n + 1) * (2 : ℝ)⁻¹ ^ (k + 1)
        = 2 * (2 : ℝ)⁻¹ ^ (n + k + 3) := by
      rw [← pow_add, show n + k + 3 = (n + 1 + (k + 1)) + 1 by omega, pow_succ]
      ring
    rw [h2]
    linarith
  -- the Σb mass is positive
  have hSab : |(∑ i, av i) - ∑ i, bv i| ≤ (2 : ℝ)⁻¹ ^ s := by
    calc |(∑ i, av i) - ∑ i, bv i| = |∑ i, (av i - bv i)| := by
          rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i, |av i - bv i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ (2 : ℝ)⁻¹ ^ s := hsumab
  have hSbv_pos : 0 < ∑ i, bv i := by
    have h1 := (abs_le.mp hSab).2
    have h2 : (2 : ℝ)⁻¹ ^ (k + 1) ≤ ∑ i, av i := by
      rw [← hZs_eq]
      exact hZs_lb
    linarith
  -- the candidate's total weight is nonzero
  have hW : (0 : ℚ) < wSumL l := lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
  have hbd : ∀ i : Fin l.length, c i ≤ (B : ℚ) + 1 := by
    intro i
    have h2 := hBnd (Q.dense l[i].1)
    have h3 : (2 : ℝ)⁻¹ ^ s ≤ 1 := by
      calc (2 : ℝ)⁻¹ ^ s ≤ (2 : ℝ)⁻¹ ^ 0 := inv_pow_le_inv_pow (Nat.zero_le _)
        _ = 1 := pow_zero _
    have h4 : ((c i : ℚ) : ℝ) ≤ (B : ℝ) + 1 := by
      have h1 := (abs_le.mp (hci i)).2
      have := (abs_le.mp h2).2
      linarith
    exact_mod_cast h4
  have hl'sum : wSumL l'
      = (∑ i : Fin l.length, wRaw l[i].2 * c i) * (1 / ((B : ℚ) + 1)) :=
    wSumL_map_fuse l Ψ s B c (fun i => congrFun hc_def i) hbd
  -- the rational total of the fused weights is positive
  have hSQ : (0 : ℚ) < ∑ i : Fin l.length, wRaw l[i].2 * c i :=
    sum_num_pos_of_cast_pos (fun i => wRaw l[i].2 * c i) hW (by
      have hcast : (∑ i : Fin l.length, ((wRaw l[i].2 * c i / wSumL l : ℚ) : ℝ))
          = ∑ i, bv i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hbv_def, haw_def]
        push_cast
        ring
      rw [hcast]
      exact hSbv_pos)
  have h0' : wSumL l' ≠ 0 := by
    rw [hl'sum]
    positivity
  -- the candidate weight is the normalized perturbed weight
  have hcand_wt : ∀ i : Fin l.length,
      ((wRaw (fuseCode l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B) / wSumL l' : ℚ) : ℝ)
        = bv i / ∑ j, bv j := fun i =>
    cand_wt_cast l Ψ s B c (fun i => congrFun hc_def i) hbd hW i
  -- the two Dirac-sum representations
  have hPrep : (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
      = ∑ i : Fin l.length, ENNReal.ofReal (av i / ∑ j, av j)
          • Measure.dirac (Q.dense l[i].1) := by
    rw [reweight_atomicOfList_toMeasure Q h0 f h₂]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hZs_def, hZs_eq, hav_def, haw_def]
  have hQrep : (atomicOfList Q l').toMeasure
      = ∑ i : Fin l.length, ENNReal.ofReal (bv i / ∑ j, bv j)
          • Measure.dirac (Q.dense l[i].1) := by
    rw [toMeasure_atomicOfList_of_ne _ h0',
      ← listSum_map_eq_finSum l' fun pr =>
        ENNReal.ofReal ((wRaw pr.2 / wSumL l' : ℚ) : ℝ)
          • Measure.dirac (Q.dense pr.1)]
    rw [hl'_def, List.map_map, listSum_map_eq_finSum l _]
    refine Finset.sum_congr rfl fun i _ => ?_
    change ENNReal.ofReal
        ((wRaw (fuseCode l[i].2 (Ψ (2 + Nat.pair l[i].1 s)) B) / wSumL l' : ℚ) : ℝ)
        • Measure.dirac (Q.dense l[i].1) = _
    rw [hcand_wt i]
  have hM4 := levyProkhorovDist_le_sum_abs (fun i : Fin l.length => Q.dense l[i].1)
    (fun i => av i / ∑ j, av j) (fun i => bv i / ∑ j, bv j)
    (fun i => div_nonneg (mul_nonneg (haw0 i) (by exact_mod_cast hc0 i))
      hSbv_pos.le)
    (reweight ⟨(f, atomicOfList Q l), h₂⟩) (atomicOfList Q l') hPrep hQrep
  exact hM4.trans (hpert.trans hbudget)

/-- **The candidate is close to the reweighted atomic**: with the certified normalizer
floor `(2⁻¹)^(k+1) ≤ Zs`, the fused candidate atomic is within `(2⁻¹)^(n+1)` of the
reweighted stage-`s` atomic — dispatched on whether the atom list carries any weight. -/
private theorem reweight_atomic_candidate_le (f : BoundedLipschitzFun Y)
    (l : List (ℕ × ℕ)) (h₂ : PosDensityPair (f, atomicOfList Q l)) {Ψ : Baire} {L B : ℕ}
    (hname : IntegrandName Q Ψ L B f.toFun) (hnn : ∀ y, 0 ≤ f.toFun y) {n k s : ℕ}
    (hs : s = n + 4 + (L + B) + k)
    (hZs_lb : (2 : ℝ)⁻¹ ^ (k + 1) ≤ ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure) :
    levyProkhorovDist (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
        (atomicOfList Q (l.map fun pr =>
          (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure
      ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  by_cases h0 : wSumL l = 0
  · exact reweight_atomic_candidate_le_zero Q f l h₂ h0
  · exact reweight_atomic_candidate_le_pos Q f l h₂ hname hnn hs hZs_lb h0


/-- **The per-coordinate Lévy–Prokhorov budget of the reweighting realizer**: with a
certified normalizer lower bound `(2⁻¹)ᵏ < ∫ f dν` and the prior's stage-`s` atomic
approximant, the fused candidate atomic is within `(2⁻¹)ⁿ` of the true normalized
reweighting, for `s = n + 4 + (L + B) + k`. -/
private theorem levyProkhorovDist_reweight_candidate_le
    (f : BoundedLipschitzFun Y) (ν : ProbabilityMeasure Y) (hw : PosDensityPair (f, ν))
    {Ψ : Baire} {L B : ℕ} (hname : IntegrandName Q Ψ L B f.toFun)
    (l : List (ℕ × ℕ)) {n k s : ℕ} (hs : s = n + 4 + (L + B) + k)
    (hd : levyProkhorovDist ν.toMeasure (atomicOfList Q l).toMeasure ≤ (2 : ℝ)⁻¹ ^ s)
    (hlow : (2 : ℝ)⁻¹ ^ k < ∫ y, f.toFun y ∂ν.toMeasure) :
    levyProkhorovDist (reweight ⟨(f, ν), hw⟩).toMeasure
        (atomicOfList Q (l.map fun pr =>
          (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure
      ≤ (2 : ℝ)⁻¹ ^ n := by
  have hnn := hw.1
  haveI : IsProbabilityMeasure ν.toMeasure := ν.prop
  haveI : IsProbabilityMeasure (atomicOfList Q l).toMeasure := (atomicOfList Q l).prop
  have hε0 : (0 : ℝ) < 2 * (2 : ℝ)⁻¹ ^ s := by positivity
  have hdε : levyProkhorovDist ν.toMeasure (atomicOfList Q l).toMeasure
      < 2 * (2 : ℝ)⁻¹ ^ s := by
    refine lt_of_le_of_lt hd ?_
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ s := by positivity
    linarith
  have hedist : levyProkhorovEDist ν.toMeasure (atomicOfList Q l).toMeasure
      < ENNReal.ofReal (2 * (2 : ℝ)⁻¹ ^ s) :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr hdε
  have hZZs : (∫ y, f.toFun y ∂ν.toMeasure)
      ≤ (∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure) + ((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s) :=
    integ_le_integ_add Q f ν l hname hnn hε0 hedist
  have hLBε : ((L : ℝ) + B) * (2 * (2 : ℝ)⁻¹ ^ s) ≤ (2 : ℝ)⁻¹ ^ (n + 3 + k) := LBε_le hs
  have hZs_lb : (2 : ℝ)⁻¹ ^ (k + 1) ≤ ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure :=
    Zs_lb_of hZZs hLBε hlow
  have hZs_pos : 0 < ∫ y, f.toFun y ∂(atomicOfList Q l).toMeasure :=
    lt_of_lt_of_le (by positivity) hZs_lb
  have h₂ : PosDensityPair (f, atomicOfList Q l) := ⟨hnn, hZs_pos⟩
  have hLP₁ : levyProkhorovDist (reweight ⟨(f, ν), hw⟩).toMeasure
      (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    reweight_stab_le Q f ν l hw h₂ hname hs hlow hdε
  have hLP₂ : levyProkhorovDist (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
      (atomicOfList Q (l.map fun pr =>
        (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    reweight_atomic_candidate_le Q f l h₂ hname hnn hs hZs_lb
  haveI : IsProbabilityMeasure (reweight ⟨(f, ν), hw⟩).toMeasure :=
    (reweight ⟨(f, ν), hw⟩).prop
  haveI : IsProbabilityMeasure (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure :=
    (reweight ⟨(f, atomicOfList Q l), h₂⟩).prop
  haveI : IsProbabilityMeasure (atomicOfList Q (l.map fun pr =>
      (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure :=
    (atomicOfList Q _).prop
  calc levyProkhorovDist (reweight ⟨(f, ν), hw⟩).toMeasure
        (atomicOfList Q (l.map fun pr =>
          (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure
      ≤ levyProkhorovDist (reweight ⟨(f, ν), hw⟩).toMeasure
          (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
        + levyProkhorovDist (reweight ⟨(f, atomicOfList Q l), h₂⟩).toMeasure
            (atomicOfList Q (l.map fun pr =>
              (pr.1, fuseCode pr.2 (Ψ (2 + Nat.pair pr.1 s)) B))).toMeasure :=
        levyProkhorovDist_triangle _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (n + 1) + (2 : ℝ)⁻¹ ^ (n + 1) := add_le_add hLP₁ hLP₂
    _ = (2 : ℝ)⁻¹ ^ n := by rw [pow_succ]; ring

end AtomicReweight

/-! ### The reweighting realizer: normalizer search and fused-atomic emission -/

section ReweightRealizer

variable {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

-- Seal the fused-weight code as irreducible here too, for the same `whnf`-storm reason as
-- in the candidate estimate: `fuseCode` is manipulated only through `ratOfCode_fuseCode`.
attribute [local irreducible] fuseCode

/-- The maximal dense index of an atom list (private re-derivation of unit 31's helper). -/
private def rwMaxIdx (l : List (ℕ × ℕ)) : ℕ := l.foldr (fun pr acc => max pr.1 acc) 0

private theorem rwFst_le_maxIdx : ∀ {l : List (ℕ × ℕ)} {pr : ℕ × ℕ}, pr ∈ l →
    pr.1 ≤ rwMaxIdx l := by
  intro l
  induction l with
  | nil => intro pr h; cases h
  | cons a t ih =>
    intro pr h
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem primrec_rwMaxIdx : Primrec rwMaxIdx :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun _ => rfl

private theorem rwPair_le_pair_left {a b : ℕ} (h : a ≤ b) (c : ℕ) :
    Nat.pair a c ≤ Nat.pair b c := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (Nat.pair_lt_pair_left c h).le
  · exact le_rfl

/-- The stage `s = n + 4 + (L + B) + k` recomputed from the coordinate `m = ⟨n, k⟩` and a
prefix `h` carrying `L = p 0` at index `0` and `B = p 2` at index `2`. -/
private def rwStage (m h : ℕ) : ℕ :=
  m.unpair.1 + 4 + ((ofNat (List ℕ) h).getD 0 0 + (ofNat (List ℕ) h).getD 2 0) + m.unpair.2

/-- Stage-1 → stage-2 bound: cover the atom-list coordinate `2 · s + 1` on the odd track. -/
private def rwB₁ (m h : ℕ) : ℕ := 2 * rwStage m h + 2

/-- Stage-2 → stage-3 bound: additionally cover every fused-value coordinate
`2 · (2 + ⟨idx, s⟩)` of the decoded atom list on the even track (through `rwMaxIdx`). -/
private def rwB₂ (m h : ℕ) : ℕ :=
  2 * (2 + Nat.pair (rwMaxIdx (ofNat (List (ℕ × ℕ))
        ((ofNat (List ℕ) h).getD (2 * rwStage m h + 1) 0))) (rwStage m h)) + 1
    + (2 * rwStage m h + 2)

private theorem primrec_rwStage : Primrec₂ rwStage := by
  have hn : Primrec fun p : ℕ × ℕ => p.1.unpair.1 := primrec_unpairFst.comp Primrec.fst
  have hk : Primrec fun p : ℕ × ℕ => p.1.unpair.2 := primrec_unpairSnd.comp Primrec.fst
  have hu : Primrec fun p : ℕ × ℕ => ofNat (List ℕ) p.2 :=
    (Primrec.ofNat (List ℕ)).comp Primrec.snd
  have hL : Primrec fun p : ℕ × ℕ => (ofNat (List ℕ) p.2).getD 0 0 :=
    (Primrec.list_getD 0).comp hu (Primrec.const 0)
  have hB : Primrec fun p : ℕ × ℕ => (ofNat (List ℕ) p.2).getD 2 0 :=
    (Primrec.list_getD 0).comp hu (Primrec.const 2)
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp hn (Primrec.const 4))
      (Primrec.nat_add.comp hL hB)) hk).to₂

private theorem primrec₂_rwB₁ : Primrec₂ rwB₁ :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (primrec_rwStage.comp Primrec.fst Primrec.snd)) (Primrec.const 2)).to₂

private theorem primrec₂_rwB₂ : Primrec₂ rwB₂ := by
  have hs : Primrec fun p : ℕ × ℕ => rwStage p.1 p.2 :=
    primrec_rwStage.comp Primrec.fst Primrec.snd
  have hlist : Primrec fun p : ℕ × ℕ => rwMaxIdx (ofNat (List (ℕ × ℕ))
      ((ofNat (List ℕ) p.2).getD (2 * rwStage p.1 p.2 + 1) 0)) :=
    primrec_rwMaxIdx.comp ((Primrec.ofNat (List (ℕ × ℕ))).comp
      ((Primrec.list_getD 0).comp ((Primrec.ofNat (List ℕ)).comp Primrec.snd)
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hs)
          (Primrec.const 1))))
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.const 2) (Primrec₂.natPair.comp hlist hs)))
      (Primrec.const 1))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hs)
      (Primrec.const 2))).to₂

/-! #### The oracle-free postprocessor of the reweight emitter -/

/-- The decoded stage-3 prefix of the packed input `w = ⟨⟨n, k⟩, encode prefix⟩`. -/
private def rwPref (w : ℕ) : List ℕ := ofNat (List ℕ) w.unpair.2

/-- The stage recomputed from the coordinate and prefix heads. -/
private def rwStageIdx (w : ℕ) : ℕ :=
  w.unpair.1.unpair.1 + 4 + ((rwPref w).getD 0 0 + (rwPref w).getD 2 0) + w.unpair.1.unpair.2

/-- The decoded atom list, read at coordinate `2 · s + 1` of the prefix (odd track). -/
private def rwAtomList (w : ℕ) : List (ℕ × ℕ) :=
  ofNat (List (ℕ × ℕ)) ((rwPref w).getD (2 * rwStageIdx w + 1) 0)

/-- The oracle-free postprocessor: the encoded fused-atomic list. -/
private def rwPost (w : ℕ) : ℕ :=
  encode ((rwAtomList w).map fun pr =>
    (pr.1, fuseCode pr.2 ((rwPref w).getD (2 * (2 + Nat.pair pr.1 (rwStageIdx w))) 0)
      ((rwPref w).getD 2 0)))

private theorem primrec_rwPref : Primrec rwPref :=
  (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd

private theorem primrec_rwStageIdx : Primrec rwStageIdx :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (primrec_unpairFst.comp primrec_unpairFst) (Primrec.const 4))
      (Primrec.nat_add.comp ((Primrec.list_getD 0).comp primrec_rwPref (Primrec.const 0))
        ((Primrec.list_getD 0).comp primrec_rwPref (Primrec.const 2))))
    (primrec_unpairSnd.comp primrec_unpairFst)

private theorem primrec_rwAtomList : Primrec rwAtomList :=
  (Primrec.ofNat (List (ℕ × ℕ))).comp ((Primrec.list_getD 0).comp primrec_rwPref
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_rwStageIdx)
      (Primrec.const 1)))

private theorem primrec_rwPost : Primrec rwPost := by
  have hB : Primrec fun w : ℕ => (rwPref w).getD 2 0 :=
    (Primrec.list_getD 0).comp primrec_rwPref (Primrec.const 2)
  have hΨpos : Primrec fun p : ℕ × (ℕ × ℕ) =>
      (rwPref p.1).getD (2 * (2 + Nat.pair p.2.1 (rwStageIdx p.1))) 0 :=
    (Primrec.list_getD 0).comp (primrec_rwPref.comp Primrec.fst)
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.const 2)
          (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
            (primrec_rwStageIdx.comp Primrec.fst))))
  have hmap : Primrec fun w : ℕ => (rwAtomList w).map fun pr =>
      (pr.1, fuseCode pr.2 ((rwPref w).getD (2 * (2 + Nat.pair pr.1 (rwStageIdx w))) 0)
        ((rwPref w).getD 2 0)) :=
    Primrec.list_map primrec_rwAtomList
      (((Primrec.fst.comp Primrec.snd).pair
        (primrec₂_fuseWithBound.comp
          (hΨpos.pair (hB.comp Primrec.fst))
          (Primrec.snd.comp Primrec.snd))).to₂)
  exact Primrec.encode.comp hmap

/-! #### Correctness of the postprocessor on the raw name -/

/-- The chained postprocessor value on a name `p` is exactly the encoded fused-atomic
list at stage `s = n + 4 + (p 0 + p 2) + k`, reading the density heads from the even
track and the stage-`s` atom list from the odd track. -/
private theorem rwPost_value (p : Baire) (n k : ℕ) :
    rwPost (Nat.pair (Nat.pair n k) (encode (streamTake p (rwB₂ (Nat.pair n k)
        (encode (streamTake p (rwB₁ (Nat.pair n k) (encode (streamTake p 3)))))))))
      = encode ((ofNat (List (ℕ × ℕ)) (p (2 * (n + 4 + (p 0 + p 2) + k) + 1))).map
          fun pr => (pr.1, fuseCode pr.2
            (p (2 * (2 + Nat.pair pr.1 (n + 4 + (p 0 + p 2) + k)))) (p 2))) := by
  set s : ℕ := n + 4 + (p 0 + p 2) + k with hs_def
  have hst1 : rwStage (Nat.pair n k) (encode (streamTake p 3)) = s := by
    simp only [rwStage, ofNat_encode, Nat.unpair_pair]
    rw [streamTake_getD p (by omega : (0 : ℕ) < 3),
      streamTake_getD p (by omega : (2 : ℕ) < 3)]
  have hb1 : rwB₁ (Nat.pair n k) (encode (streamTake p 3)) = 2 * s + 2 := by
    rw [rwB₁, hst1]
  set l : List (ℕ × ℕ) := ofNat (List (ℕ × ℕ)) (p (2 * s + 1)) with hl_def
  have hst2 : rwStage (Nat.pair n k) (encode (streamTake p (2 * s + 2))) = s := by
    simp only [rwStage, ofNat_encode, Nat.unpair_pair]
    rw [streamTake_getD p (by omega : (0 : ℕ) < 2 * s + 2),
      streamTake_getD p (by omega : (2 : ℕ) < 2 * s + 2)]
  have hb2 : rwB₂ (Nat.pair n k) (encode (streamTake p (2 * s + 2)))
      = 2 * (2 + Nat.pair (rwMaxIdx l) s) + 1 + (2 * s + 2) := by
    simp only [rwB₂, ofNat_encode]
    rw [hst2, streamTake_getD p (by omega : 2 * s + 1 < 2 * s + 2)]
  rw [hb1, hb2]
  set m₂ : ℕ := 2 * (2 + Nat.pair (rwMaxIdx l) s) + 1 + (2 * s + 2) with hm₂_def
  set w : ℕ := Nat.pair (Nat.pair n k) (encode (streamTake p m₂)) with hw_def
  have hpref : rwPref w = streamTake p m₂ := by simp [rwPref, hw_def]
  have hn1 : w.unpair.1 = Nat.pair n k := by simp [hw_def]
  have hsi : rwStageIdx w = s := by
    simp only [rwStageIdx, hpref, hn1, Nat.unpair_pair]
    rw [streamTake_getD p (by omega : (0 : ℕ) < m₂),
      streamTake_getD p (by omega : (2 : ℕ) < m₂)]
  have hal : rwAtomList w = l := by
    simp only [rwAtomList, hsi, hpref, hl_def]
    rw [streamTake_getD p (by omega : 2 * s + 1 < m₂)]
  have hB2 : (rwPref w).getD 2 0 = p 2 := by
    rw [hpref, streamTake_getD p (by omega : (2 : ℕ) < m₂)]
  have hval : ∀ pr : ℕ × ℕ, pr ∈ l →
      (rwPref w).getD (2 * (2 + Nat.pair pr.1 s)) 0 = p (2 * (2 + Nat.pair pr.1 s)) := by
    intro pr hpr
    have hle : Nat.pair pr.1 s ≤ Nat.pair (rwMaxIdx l) s :=
      rwPair_le_pair_left (rwFst_le_maxIdx hpr) _
    rw [hpref, streamTake_getD p (by omega : 2 * (2 + Nat.pair pr.1 s) < m₂)]
  simp only [rwPost, hal, hsi, hB2]
  refine congrArg encode (List.map_congr_left fun pr hpr => ?_)
  rw [hval pr hpr]

/-- **The normalized reweighting is a computable map** `blRep Q × weakMeasureRep Q ⟶
weakMeasureRep Q` on the positive-density subtype.  The normalizer's positivity is Σ₁: an
`rfind` search certifies a rational lower bound `(2⁻¹)ᵏ < ∫ f dν` from the integration
operation on the name alone (no modulus datum), and the division is exact coded-rational
arithmetic inside the emitted atomic weights (the same search pattern as
`computableMap_realInv_pos`). -/
theorem computableMap_reweight (Q : ComputableMetricPresentation Y) :
    ComputableMap (((blRep Q).prod (weakMeasureRep Q)).subtype fun w => PosDensityPair w)
      (weakMeasureRep Q) reweight := by
  obtain ⟨cInt, hcInt⟩ := computableMap_integrateBL Q
  obtain ⟨svC, hsv⟩ := exists_ofNatFnCode (g := fun v => searchVal v.unpair.1 v.unpair.2)
    primrec_searchValPost.to_comp
  obtain ⟨emitC, hemit⟩ := exists_prefixChainCode (b₀ := fun _ => 3) (b₁ := rwB₁)
    (b₂ := rwB₂) (g := rwPost) (Primrec.const 3) primrec₂_rwB₁ primrec₂_rwB₂ primrec_rwPost
  refine ⟨.comp emitC (.pair OracleCode.id (OracleCode.rfind
    (.comp svC (.pair (.comp cInt .right) .right)))), fun p w hpw => ?_⟩
  have hprod : ((blRep Q).prod (weakMeasureRep Q)).Names p w.val :=
    Representation.subtype_names_iff.mp hpw
  obtain ⟨hfn, hνn⟩ := Representation.prod_names_iff.mp hprod
  have hname : IntegrandName Q p.evenPart (p.evenPart 0) (p.evenPart 1) w.val.1.toFun :=
    (blRep_names_iff Q).mp hfn
  have hνnames : WeakMeasureNames Q p.oddPart w.val.2 := (weakMeasureRep_names_iff Q).mp hνn
  obtain ⟨I, hI_mem, hI_names⟩ := hcInt p w.val hprod
  have hI_eval : ∀ j, cInt.eval p j = Part.some (I j) :=
    fun j => Part.eq_some_iff.mpr (mem_evalStream.mp hI_mem j)
  have hI_ap : ∀ j, |((ratOfCode (I j) : ℚ) : ℝ)
      - ∫ y, w.val.1.toFun y ∂w.val.2.toMeasure| ≤ (2 : ℝ)⁻¹ ^ j :=
    realRep_names_iff.mp hI_names
  have hSC : ∀ a k : ℕ,
      (OracleCode.comp svC (.pair (.comp cInt .right) .right)).eval p (Nat.pair a k)
        = Part.some (searchVal (I k) k) := by
    intro a k
    have hr : OracleCode.right.eval p (Nat.pair a k) = Part.some k := by
      rw [eval_right, Nat.unpair_pair]
    have h1 : (OracleCode.comp cInt .right).eval p (Nat.pair a k) = Part.some (I k) := by
      rw [eval_comp_some hr, hI_eval]
    rw [eval_comp_some (eval_pair_some h1 hr), hsv]
    simp only [Nat.unpair_pair]
  let pred : ℕ → Bool := fun k => decide (searchVal (I k) k = 0)
  have hpreddef : pred = fun k => decide (searchVal (I k) k = 0) := rfl
  have hrfeq : ∀ a : ℕ,
      (OracleCode.rfind (.comp svC (.pair (.comp cInt .right) .right))).eval p a
        = Nat.rfind (pred : ℕ →. Bool) := by
    intro a
    rw [eval_rfind]
    congr 1
    funext k
    rw [hSC a k, PFun.coe_val]
    simp [hpreddef]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (div_pos w.property.2 (by norm_num : (0 : ℝ) < 3) :
      (0 : ℝ) < (∫ y, w.val.1.toFun y ∂w.val.2.toMeasure) / 3)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hpk : pred k = true := by
    simp only [hpreddef, decide_eq_true_eq]
    rw [searchVal_eq_zero_iff]
    have habs := abs_le.mp (hI_ap k)
    have hr : ((2 * (2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) < ((ratOfCode (I k) : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hr
  obtain ⟨k₀, hk₀, -⟩ := Nat.rfind_min' hpk
  have hrf : ∀ a : ℕ,
      (OracleCode.rfind (.comp svC (.pair (.comp cInt .right) .right))).eval p a
        = Part.some k₀ := fun a =>
    Part.eq_some_iff.mpr (by rw [hrfeq a]; exact hk₀)
  have hlow : (2 : ℝ)⁻¹ ^ k₀ < ∫ y, w.val.1.toFun y ∂w.val.2.toMeasure := by
    have hspec0 := Nat.rfind_spec hk₀
    rw [PFun.coe_val, Part.mem_some_iff] at hspec0
    have hzero : searchVal (I k₀) k₀ = 0 := by
      have h' := hspec0.symm
      simp only [hpreddef, decide_eq_true_eq] at h'
      exact h'
    have hs2 : 2 * (2 : ℚ)⁻¹ ^ k₀ < ratOfCode (I k₀) := searchVal_eq_zero_iff.mp hzero
    have hsr : ((2 * (2 : ℚ)⁻¹ ^ k₀ : ℚ) : ℝ) < ((ratOfCode (I k₀) : ℚ) : ℝ) := by
      exact_mod_cast hs2
    push_cast at hsr
    have habs := abs_le.mp (hI_ap k₀)
    linarith
  refine ⟨fun a => rwPost (Nat.pair (Nat.pair a k₀) (encode (streamTake p
      (rwB₂ (Nat.pair a k₀) (encode (streamTake p
        (rwB₁ (Nat.pair a k₀) (encode (streamTake p 3))))))))),
    mem_evalStream.mpr fun a => ?_, ?_⟩
  · have hpair : (OracleCode.pair OracleCode.id (OracleCode.rfind
        (.comp svC (.pair (.comp cInt .right) .right)))).eval p a
        = Part.some (Nat.pair a k₀) := eval_pair_some (eval_id p a) (hrf a)
    rw [eval_comp_some hpair, hemit p (Nat.pair a k₀)]
    exact Part.mem_some _
  · refine (weakMeasureRep_names_iff Q).mpr fun a => ?_
    rw [rwPost_value p a k₀, atomic_encode]
    have hd : levyProkhorovDist w.val.2.toMeasure
        (atomicOfList Q (ofNat (List (ℕ × ℕ))
          (p.oddPart (a + 4 + (p.evenPart 0 + p.evenPart 1) + k₀)))).toMeasure
        ≤ (2 : ℝ)⁻¹ ^ (a + 4 + (p.evenPart 0 + p.evenPart 1) + k₀) := by
      have h := hνnames (a + 4 + (p.evenPart 0 + p.evenPart 1) + k₀)
      rwa [atomic] at h
    exact levyProkhorovDist_reweight_candidate_le Q w.val.1 w.val.2 w.property hname
      (ofNat (List (ℕ × ℕ)) (p.oddPart (a + 4 + (p.evenPart 0 + p.evenPart 1) + k₀)))
      (n := a) (k := k₀) rfl hd hlow

end ReweightRealizer

/-! ### The uncurried and curried positive conditioning theorems -/

section BayesCond

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Lift a computable map into a subtype whose predicate the image always satisfies. -/
private theorem computableMap_subtypeMk {α β : Type*} {RA : Representation α}
    {RB : Representation β} {P : β → Prop} {f : α → β} (hf : ComputableMap RA RB f)
    (hP : ∀ a, P (f a)) : ComputableMap RA (RB.subtype P) fun a => ⟨f a, hP a⟩ := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨c, fun p a hpa => ?_⟩
  obtain ⟨q, hq, hqf⟩ := hc p a hpa
  exact ⟨q, hq, Representation.subtype_names_iff.mpr hqf⟩

/-- **The domain of the uncurried positive conditioning theorem**: the subtype
representation carrying a density-and-joint-law pair together with the proof that it is a
bounded-Lipschitz everywhere-positive conditional density pair. -/
noncomputable def densityPairRep (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    Representation {d : BoundedLipschitzFun (X × Y) × ProbabilityMeasure (X × Y) //
        IsCondDensityPair d.2 d.1} :=
  letI : BorelSpace (X × Y) := P.borelSpace_prod
  ((blRep (P.prod Q)).prod (weakMeasureRep (P.prod Q))).subtype fun d =>
    IsCondDensityPair d.2 d.1

/-- **The uncurried positive conditioning theorem**: from a name of the density–joint-law
pair (the subtype representation `densityPairRep`) and a name of the observed point, the
Bayes conditional law `bayesLaw` is computed as a weak measure name.  Assembled by
composing the density-slice, second-marginal, and normalized-reweighting realizers. -/
theorem computableMap_bayesCond (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    ComputableMap ((densityPairRep P Q).prod P.cauchyRep) (weakMeasureRep Q)
      (fun w => bayesLaw w.1.val.2 w.1.val.1 w.1.property w.2) := by
  letI : BorelSpace (X × Y) := P.borelSpace_prod
  have hslice : ComputableMap ((densityPairRep P Q).prod P.cauchyRep) (blRep Q)
      (fun w => w.1.val.1.slice w.2) :=
    (computableMap_blSlice P Q).comp
      ((computableMap_fst.comp (computableMap_subtypeVal.comp computableMap_fst)).pair
        computableMap_snd)
  have hsnd : ComputableMap ((densityPairRep P Q).prod P.cauchyRep) (weakMeasureRep Q)
      (fun w => sndMarginal w.1.val.2) :=
    (computableMap_sndMarginal P Q).comp
      (computableMap_snd.comp (computableMap_subtypeVal.comp computableMap_fst))
  have hpair : ComputableMap ((densityPairRep P Q).prod P.cauchyRep)
      (((blRep Q).prod (weakMeasureRep Q)).subtype fun v => PosDensityPair v)
      (fun w => ⟨(w.1.val.1.slice w.2, sndMarginal w.1.val.2),
        w.1.property.posDensityPair w.2⟩) :=
    computableMap_subtypeMk (hslice.pair hsnd) fun w => w.1.property.posDensityPair w.2
  have hcomp := (computableMap_reweight Q).comp hpair
  have hfun : (reweight ∘ fun w : {d : BoundedLipschitzFun (X × Y) ×
        ProbabilityMeasure (X × Y) // IsCondDensityPair d.2 d.1} × X =>
        (⟨(w.1.val.1.slice w.2, sndMarginal w.1.val.2),
          w.1.property.posDensityPair w.2⟩ : {v // PosDensityPair v}))
      = fun w => bayesLaw w.1.val.2 w.1.val.1 w.1.property w.2 := by
    funext w
    exact (bayesLaw_eq_reweight w.1.property w.2).symm
  rwa [hfun] at hcomp

end BayesCond

section Curried

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The Bayes conditional as an advice-realizable map `X ⟶ ProbabilityMeasure Y`: the
section of the uncurried computable map at a fixed density–joint-law pair, so that
`(bayesCondFun P Q d).toFun x = bayesLaw d.val.2 d.val.1 d.property x`. -/
noncomputable def bayesCondFun (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y)
    (d : {d : BoundedLipschitzFun (X × Y) × ProbabilityMeasure (X × Y) //
        IsCondDensityPair d.2 d.1}) :
    RealizableFun P.cauchyRep (weakMeasureRep Q) :=
  RealizableFun.curry (computableMap_bayesCond P Q) d

/-- **The curried positive conditioning headline**: the map sending each bounded-Lipschitz
everywhere-positive conditional density pair to its Bayes conditional (as an
advice-realizable map into the weak measure space) is computable, and its output is
`Condition`-accepted at the pair's joint law — with everywhere (not merely a.e.)
agreement with the Bayes-ratio kernel. -/
theorem computableMap_bayesCond_curried (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) [SecondCountableTopology X] :
    ComputableMap (densityPairRep P Q) (condFunSpace P Q).rep (fun d => bayesCondFun P Q d) ∧
      ∀ d : {d : BoundedLipschitzFun (X × Y) × ProbabilityMeasure (X × Y) //
          IsCondDensityPair d.2 d.1},
        (Condition P Q).accepts d.val.2 (bayesCondFun P Q d) := by
  letI : BorelSpace (X × Y) := P.borelSpace_prod
  refine ⟨computableMap_funRep_curry (computableMap_bayesCond P Q), fun d => ?_⟩
  refine ⟨bayesKernel d.val.2.toMeasure.snd d.val.1.toFun,
    d.property.isCondKernel, Filter.Eventually.of_forall fun x => ?_⟩
  exact bayesLaw_toMeasure_eq_bayesKernel d.property x

end Curried

end ComputableAnalysis
