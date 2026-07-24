/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.CantorPresentation
import ComputableAnalysis.Measure.Constructors
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Support

/-!
# Cantor space is standard Borel; the fair coin has full support

Two classical facts consumed by the conditioning layer, both under convention 11's
scoped `PiNatInstances` structures.

**Standard Borel.** The scoped Cantor metric is complete (the controlled-sequences
criterion, exactly as in mathlib's `PiNat.completeSpace`, restated here because that
lemma is pinned to `PiNat.metricSpace`'s uniformity rather than the scoped
`PiNat.metricSpaceOfDiscreteUniformity`) and separable (the Cantor presentation's dense
sequence), hence Polish; with the scoped Borel structure this gives
`StandardBorelSpace Cantor` through mathlib's `standardBorel_of_polish`. The instance
chain: `cantorMetricSpace` + `completeSpace_cantor` ⟶
`MetricSpace.toIsCompletelyMetrizableSpace`, and `cantorPresentation.separableSpace` ⟶
`UniformSpace.secondCountable_of_separable`, assembled into `PolishSpace` ⟶ (+ the
scoped `BorelSpace Cantor`) `standardBorel_of_polish`.

**Full support.** Every nondegenerate Bernoulli product measure is open-positive: every
nonempty open set contains a cylinder around each of its points (metric balls at radius
`(1/2)^n` are cylinders), and `cylMass_bernoulliProduct` makes every cylinder mass a
positive product of bit probabilities. `Measure.support_eq_univ` then gives full
support; the fair coin `bernoulliProduct ⟨1/2, _⟩` is the concrete instance.
-/

open MeasureTheory

namespace ComputableAnalysis

namespace PiNatInstances

/-- **Completeness of the scoped Cantor metric.** The controlled-sequences criterion at
rate `(1/2)^n`: a sequence with `dist (u n) (u m) < (1/2)^N` for `n, m ≥ N` has each
coordinate eventually constant, so it converges to the diagonal limit. This is
mathlib's `PiNat.completeSpace` proof, restated because that lemma is stated for
`PiNat.metricSpace`'s uniformity, not the scoped
`PiNat.metricSpaceOfDiscreteUniformity` one. -/
scoped instance completeSpace_cantor : CompleteSpace Cantor := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2 : ℝ) ^ n)
    (fun n => by positivity) fun u hu => ?_
  refine ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i] with n hn
  exact PiNat.apply_eq_of_dist_lt (hu i i n le_rfl hn) le_rfl

/-- **Polishness of Cantor space**, assembled through the scoped metric: second
countability from separability (the Cantor presentation's dense sequence through
`UniformSpace.secondCountable_of_separable`), complete metrizability from the scoped
metric plus `completeSpace_cantor` through `MetricSpace.toIsCompletelyMetrizableSpace`.
Built as an explicit structure term, not `inferInstance`: the ambient topology in the
statement elaborates to `Pi.topologicalSpace`, and only *term-level* (full
transparency) unification crosses the definitional equality with the scoped metric
topology — instance search rejects `MetricSpace.toIsCompletelyMetrizableSpace` at
instance transparency and would silently fall back to mathlib's
`IsCompletelyMetrizableSpace.pi_countable`/`.discrete` route instead. -/
scoped instance polishSpace_cantor : PolishSpace Cantor :=
  haveI : TopologicalSpace.SeparableSpace Cantor := cantorPresentation.separableSpace
  { toSecondCountableTopology := UniformSpace.secondCountable_of_separable Cantor
    toIsCompletelyMetrizableSpace := MetricSpace.toIsCompletelyMetrizableSpace }

/-- **Cantor space is standard Borel**: the scoped metric topology is Polish and the
scoped Borel structure is a Borel structure for it, so mathlib's
`standardBorel_of_polish` applies. -/
scoped instance standardBorelSpace_cantor : StandardBorelSpace Cantor :=
  standardBorel_of_polish

end PiNatInstances

open scoped PiNatInstances

/-! ### Full support of the Bernoulli product -/

/-- **Open-positivity of a nondegenerate Bernoulli product.** Every nonempty open set
contains a cylinder around each of its points (a metric ball of radius `(1/2)^n`
contains the length-`n` cylinder), and every cylinder has positive mass: each factor of
`cylMass_bernoulliProduct` is `p` or `1 - p`, positive by nondegeneracy. -/
theorem isOpenPosMeasure_bernoulliProduct {p : Set.Icc (0 : ℝ) 1} (hp0 : 0 < p.1)
    (hp1 : p.1 < 1) : (bernoulliProduct p).toMeasure.IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  have hsub : (cylinder (streamTake x n) : Set Cantor) ⊆ U := by
    rw [cylinder_streamTake]
    intro y hy
    exact hball (Metric.mem_ball.mpr ((PiNat.mem_cylinder_iff_dist_le.mp hy).trans_lt hn))
  have hpos : 0 < cylMass (bernoulliProduct p) (streamTake x n) := by
    rw [cylMass_bernoulliProduct]
    refine Finset.prod_pos fun i _ => ?_
    cases (streamTake x n)[i]
    · exact sub_pos.mpr hp1
    · exact hp0
  have hcyl : (bernoulliProduct p).toMeasure (cylinder (streamTake x n)) ≠ 0 := by
    intro h0
    exact hpos.ne' (by simp [cylMass, h0])
  exact fun h0 => hcyl (measure_mono_null hsub h0)

/-- **Full support of a nondegenerate Bernoulli product**: open-positivity plus
`Measure.support_eq_univ`. -/
theorem support_bernoulliProduct {p : Set.Icc (0 : ℝ) 1} (hp0 : 0 < p.1) (hp1 : p.1 < 1) :
    (bernoulliProduct p).toMeasure.support = Set.univ :=
  haveI := isOpenPosMeasure_bernoulliProduct hp0 hp1
  Measure.support_eq_univ

/-- **The fair coin has full support**: the `p = 1/2` instance of
`support_bernoulliProduct`. -/
theorem support_bernoulliProduct_half :
    (bernoulliProduct ⟨1 / 2, by norm_num⟩).toMeasure.support = Set.univ :=
  support_bernoulliProduct (by norm_num) (by norm_num)

end ComputableAnalysis
