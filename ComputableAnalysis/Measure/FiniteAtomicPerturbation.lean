/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Perturbing the weights of a finite atomic measure

Two finite atomic probability measures carried by the *same* family of atoms are close in
Lévy–Prokhorov distance as soon as their weight vectors are close in `ℓ¹`:

  `levyProkhorovDist P Q ≤ ∑ i, |a i - b i|`  (`levyProkhorovDist_le_sum_abs`).

This is the estimate every atomic-approximation argument in the library ends with: the
analytic work produces an atomic measure with real weights, the effective layer can only
emit rational (or otherwise rounded) weights, and the two sit on the same atoms, so all
that is left to control is the weight vector.

The proof uses no thickening at all — the test set `B` already witnesses the bound, and
the `ε`-thickening in the definition of the Lévy–Prokhorov distance only helps.

The hypotheses are exactly those of `levyProkhorovDist_le_of_forall_le`: a
`PseudoEMetricSpace` structure whose open sets are measurable. In particular no
`MetricSpace` or `BorelSpace` assumption is needed, which is what lets the single statement
below serve carriers as different as Cantor space, a product of Cantor spaces, and the unit
interval.

Following the quarantine rule of `ComputableAnalysis.Measure.WeakRepresentation`, the
`LevyProkhorov` type synonym appears in no statement here: only the *function*
`levyProkhorovDist` on `Measure`s does.
-/

namespace ComputableAnalysis

open MeasureTheory Metric

variable {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X] [OpensMeasurableSpace X]

omit [PseudoEMetricSpace X] [OpensMeasurableSpace X] in
/-- Evaluating a finite atomic measure on a measurable set: the mass of the set is the sum,
over the atoms, of the indicator of the set evaluated at that atom. -/
private theorem sum_smul_dirac_apply {k : ℕ} (a : Fin k → ℝ) (x : Fin k → X) {A : Set X}
    (hA : MeasurableSet A) :
    (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) A =
      ∑ i, A.indicator (fun _ ↦ ENNReal.ofReal (a i)) (x i) := by
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  by_cases hi : x i ∈ A
  · simp [Set.indicator_of_mem hi]
  · simp [Set.indicator_of_notMem hi]

/-- **Same atoms, close weights.** Two finite atomic probability measures carried by the
same family of atoms `x : Fin k → X` are close in Lévy–Prokhorov distance as soon as their
weight vectors are close in `ℓ¹`: the distance is at most `∑ i, |a i - b i|`.

No thickening is used in the proof: the set `B` itself already witnesses the bound, so the
`ε`-thickening only helps. -/
theorem levyProkhorovDist_le_sum_abs {k : ℕ} (x : Fin k → X) (a b : Fin k → ℝ)
    (hb : ∀ i, 0 ≤ b i) (P Q : ProbabilityMeasure X)
    (hP : P.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Q.toMeasure = ∑ i, ENNReal.ofReal (b i) • Measure.dirac (x i)) :
    levyProkhorovDist P.toMeasure Q.toMeasure ≤ ∑ i, |a i - b i| := by
  refine levyProkhorovDist_le_of_forall_le _ _
    (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) fun ε B hε hB ↦ ?_
  have hε0 : 0 < ε := lt_of_le_of_lt (Finset.sum_nonneg fun i _ ↦ abs_nonneg _) hε
  have hPB : P.toMeasure B = ∑ i, B.indicator (fun _ ↦ ENNReal.ofReal (a i)) (x i) := by
    rw [hP]; exact sum_smul_dirac_apply a x hB
  have hQB : Q.toMeasure B = ∑ i, B.indicator (fun _ ↦ ENNReal.ofReal (b i)) (x i) := by
    rw [hQ]; exact sum_smul_dirac_apply b x hB
  have hpoint : ∀ i, B.indicator (fun _ ↦ ENNReal.ofReal (a i)) (x i) ≤
      B.indicator (fun _ ↦ ENNReal.ofReal (b i)) (x i) + ENNReal.ofReal |a i - b i| := by
    intro i
    by_cases hi : x i ∈ B
    · rw [Set.indicator_of_mem hi, Set.indicator_of_mem hi,
        ← ENNReal.ofReal_add (hb i) (abs_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := le_abs_self (a i - b i)
      linarith
    · simp [Set.indicator_of_notMem hi]
  calc P.toMeasure B
      ≤ ∑ i, (B.indicator (fun _ ↦ ENNReal.ofReal (b i)) (x i) +
          ENNReal.ofReal |a i - b i|) := by
        rw [hPB]; exact Finset.sum_le_sum fun i _ ↦ hpoint i
    _ = Q.toMeasure B + ENNReal.ofReal (∑ i, |a i - b i|) := by
        rw [Finset.sum_add_distrib, hQB, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ abs_nonneg _]
    _ ≤ Q.toMeasure (thickening ε B) + ENNReal.ofReal ε :=
        add_le_add (measure_mono (self_subset_thickening hε0 B))
          (ENNReal.ofReal_le_ofReal hε.le)

end ComputableAnalysis
