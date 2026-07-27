/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The binomial approximant of a measure on the unit interval

For a probability measure `η` on `[0, 1]` and `N : ℕ`, the *binomial approximant* of `η` at
level `N` is the finitely supported measure on the grid `{k / N : k ≤ N}` that gives the grid
point `bernstein.z k = k / N` the mass

  `binomialWeight N k η = ∫ p, bernstein N k p ∂η`,

the `η`-average of the `k`-th Bernstein basis polynomial. Probabilistically it is the law of
`Bin(N, p) / N` for `p ∼ η`, so it converges weakly to `η`; the rate is quantified here by
Chebyshev's inequality applied to `bernstein.variance`.

The two layers are independent:

* **The approximant.** `binomialWeight` and `binomialApproximant` are defined, and shown to be
  a probability measure, without any reference to the convergence estimate.
* **The estimate.** `sum_bernstein_far_le` is the Chebyshev tail bound, in the general form
  `1 / (4 N ε²)`; `sum_bernstein_far_le_dyadic` instantiates it at `N = 2 ^ (3 m)` and
  `ε = 2⁻ᵐ`, where the bound becomes `2⁻ᵐ / 4`, keeping all the arithmetic dyadic; and
  `levyProkhorovDist_binomialApproximant_le` turns that into the weak estimate
  `levyProkhorovDist η (binomialApproximant (2 ^ (3 m)) η) ≤ 2⁻ᵐ`.

The choice `N = 2 ^ (3 m)` is deliberate: no real cube root ever appears, so the rate plugs
straight into a `2⁻ⁿ`-rate name construction.

This module is self-contained classical measure theory: it imports mathlib only, and nothing
from the rest of this library. That isolation is intentional and should be preserved.

Following the quarantine rule of `ComputableAnalysis.Measure.WeakRepresentation`, the
`LevyProkhorov` type synonym appears in no statement here: only the *function*
`levyProkhorovDist` on `Measure`s does.
-/

namespace ComputableAnalysis

open MeasureTheory Metric

/-! ### The binomial weights -/

/-- A continuous function on the compact space `[0, 1]` is integrable against a finite
measure. -/
private theorem integrable_of_continuous {μ : Measure (Set.Icc (0 : ℝ) 1)} [IsFiniteMeasure μ]
    {f : Set.Icc (0 : ℝ) 1 → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Each Bernstein basis polynomial is integrable against a probability measure on `[0, 1]`. -/
private theorem integrable_bernstein (N k : ℕ)
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    Integrable (fun p : Set.Icc (0 : ℝ) 1 ↦ bernstein N k p) η.toMeasure :=
  integrable_of_continuous (bernstein N k).continuous

/-- The **binomial weight** of the grid point `k / N`: the `η`-average
`∫ p, bernstein N k p ∂η` of the `k`-th Bernstein basis polynomial of degree `N`.

Probabilistically this is `ℙ[Bin(N, p) = k]` averaged over `p ∼ η`. -/
noncomputable def binomialWeight (N : ℕ) (k : Fin (N + 1))
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) : ℝ :=
  ∫ p, bernstein N k p ∂η.toMeasure

/-- The binomial weights are nonnegative. -/
theorem binomialWeight_nonneg (N : ℕ) (k : Fin (N + 1))
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) : 0 ≤ binomialWeight N k η :=
  integral_nonneg fun _ ↦ bernstein_nonneg

/-- The binomial weights sum to `1`: the Bernstein basis of degree `N` is a partition of
unity, and `η` is a probability measure. -/
theorem sum_binomialWeight (N : ℕ) (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    ∑ k : Fin (N + 1), binomialWeight N k η = 1 := by
  simp only [binomialWeight]
  rw [← integral_finsetSum (Finset.univ : Finset (Fin (N + 1)))
    fun k _ ↦ integrable_bernstein N k η]
  simp

/-! ### The approximant -/

/-- The atomic measure carrying mass `binomialWeight N k η` at the grid point `k / N` is a
probability measure. -/
private theorem isProbabilityMeasure_binomial (N : ℕ)
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    IsProbabilityMeasure (∑ k : Fin (N + 1),
      ENNReal.ofReal (binomialWeight N k η) • Measure.dirac (bernstein.z k)) := by
  constructor
  rw [Measure.coe_finsetSum]
  simp only [Finset.sum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ binomialWeight_nonneg N k η,
    sum_binomialWeight N η, ENNReal.ofReal_one]

/-- The **binomial approximant** of `η` at level `N`: the atomic probability measure putting
mass `binomialWeight N k η` at the grid point `bernstein.z k = k / N`. -/
noncomputable def binomialApproximant (N : ℕ) (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    ProbabilityMeasure (Set.Icc (0 : ℝ) 1) :=
  ⟨∑ k : Fin (N + 1), ENNReal.ofReal (binomialWeight N k η) • Measure.dirac (bernstein.z k),
    isProbabilityMeasure_binomial N η⟩

/-- The binomial approximant, as a measure: a weighted sum of Diracs on the grid. -/
@[simp] theorem binomialApproximant_toMeasure (N : ℕ)
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    (binomialApproximant N η).toMeasure =
      ∑ k : Fin (N + 1), ENNReal.ofReal (binomialWeight N k η) • Measure.dirac (bernstein.z k) :=
  rfl

/-! ### The Chebyshev tail estimate -/

/-- **Chebyshev's inequality for the Bernstein basis.** At any `x ∈ [0, 1]` the total mass that
the binomial distribution `Bin(N, x)` puts on grid points further than `ε` from `x` is at most
`1 / (4 N ε²)`. -/
theorem sum_bernstein_far_le {N : ℕ} (hN : N ≠ 0) (x : Set.Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    ∑ k ∈ Finset.univ.filter fun k : Fin (N + 1) ↦ ε < |(x : ℝ) - bernstein.z k|,
      bernstein N k x ≤ 1 / (4 * N * ε ^ 2) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
  have hx := x.2
  calc ∑ k ∈ Finset.univ.filter fun k : Fin (N + 1) ↦ ε < |(x : ℝ) - bernstein.z k|,
        bernstein N k x
      ≤ ∑ k ∈ Finset.univ.filter fun k : Fin (N + 1) ↦ ε < |(x : ℝ) - bernstein.z k|,
          ((x : ℝ) - bernstein.z k) ^ 2 / ε ^ 2 * bernstein N k x := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        have hk' : ε < |(x : ℝ) - bernstein.z k| := (Finset.mem_filter.mp hk).2
        have hsq : ε ^ 2 ≤ ((x : ℝ) - bernstein.z k) ^ 2 := by
          rw [← sq_abs ((x : ℝ) - bernstein.z k)]
          exact pow_le_pow_left₀ hε.le hk'.le 2
        have h1 : 1 ≤ ((x : ℝ) - bernstein.z k) ^ 2 / ε ^ 2 :=
          (one_le_div (by positivity)).mpr hsq
        nlinarith [bernstein_nonneg (n := N) (ν := (k : ℕ)) (x := x)]
    _ ≤ ∑ k : Fin (N + 1), ((x : ℝ) - bernstein.z k) ^ 2 / ε ^ 2 * bernstein N k x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ ↦ by positivity
    _ = (∑ k : Fin (N + 1), ((x : ℝ) - bernstein.z k) ^ 2 * bernstein N k x) / ε ^ 2 := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ = (x : ℝ) * (1 - x) / N / ε ^ 2 := by rw [bernstein.variance hN]
    _ ≤ 1 / (4 * N * ε ^ 2) := by
        rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_pos hNpos (pow_pos hε 2)).le (sq_nonneg (2 * (x : ℝ) - 1))]

/-- **The dyadic form of the Chebyshev estimate.** At `N = 2 ^ (3 m)` and `ε = 2⁻ᵐ` the general
bound `1 / (4 N ε²)` becomes `2⁻ᵐ / 4`; the arithmetic stays dyadic throughout, so no real cube
root is ever needed. -/
theorem sum_bernstein_far_le_dyadic (m : ℕ) (x : Set.Icc (0 : ℝ) 1) :
    ∑ k ∈ Finset.univ.filter fun k : Fin (2 ^ (3 * m) + 1) ↦
        (2 : ℝ)⁻¹ ^ m < |(x : ℝ) - bernstein.z k|,
      bernstein (2 ^ (3 * m)) k x ≤ (2 : ℝ)⁻¹ ^ m / 4 := by
  refine (sum_bernstein_far_le (N := 2 ^ (3 * m)) (Nat.pos_of_neZero _).ne' x
    (by positivity)).trans_eq ?_
  have h2 : (2 : ℝ) ^ m ≠ 0 := by positivity
  rw [Nat.cast_pow, Nat.cast_ofNat, mul_comm 3 m, pow_mul, inv_pow]
  field_simp

/-! ### The Lévy–Prokhorov estimate -/

/-- Any partial sum of the Bernstein basis at a point is at most `1`. -/
private theorem sum_bernstein_le_one {N : ℕ} (x : Set.Icc (0 : ℝ) 1) (S : Finset (Fin (N + 1))) :
    ∑ k ∈ S, bernstein N k x ≤ 1 :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    fun _ _ _ ↦ bernstein_nonneg).trans (bernstein.probability N x).le

/-- Any partial sum of the Bernstein basis at a point is nonnegative. -/
private theorem sum_bernstein_nonneg {N : ℕ} (x : Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin (N + 1))) : 0 ≤ ∑ k ∈ S, bernstein N k x :=
  Finset.sum_nonneg fun _ _ ↦ bernstein_nonneg

/-- The mass the binomial approximant gives a measurable set `B` is the `η`-integral of the
sum of the Bernstein basis functions indexed by the grid points lying in `B`. -/
private theorem binomialApproximant_apply_toReal {N : ℕ}
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) {B : Set (Set.Icc (0 : ℝ) 1)}
    (hB : MeasurableSet B) (S : Finset (Fin (N + 1)))
    (hS : ∀ k, k ∈ S ↔ bernstein.z k ∈ B) :
    ((binomialApproximant N η).toMeasure B).toReal =
      ∫ x, (∑ k ∈ S, bernstein N k x) ∂η.toMeasure := by
  have hsum : (binomialApproximant N η).toMeasure B =
      ∑ k ∈ S, ENNReal.ofReal (binomialWeight N k η) := by
    rw [binomialApproximant_toMeasure, Measure.coe_finsetSum]
    simp only [Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply' _ hB, smul_eq_mul]
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin (N + 1))),
        ENNReal.ofReal (binomialWeight N k η) * B.indicator 1 (bernstein.z k) =
          if k ∈ S then ENNReal.ofReal (binomialWeight N k η) else 0 := by
      intro k _
      by_cases hk : k ∈ S
      · simp [hk, Set.indicator_of_mem ((hS k).mp hk)]
      · simp [hk, Set.indicator_of_notMem fun h ↦ hk ((hS k).mpr h)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.univ_inter]
  rw [hsum, ← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ binomialWeight_nonneg N k η,
    ENNReal.toReal_ofReal (Finset.sum_nonneg fun k _ ↦ binomialWeight_nonneg N k η)]
  simp only [binomialWeight]
  rw [integral_finsetSum S fun k _ ↦ integrable_bernstein N k η]

/-- A real estimate between the masses of two finite measures upgrades to an `ℝ≥0∞` one. -/
private theorem le_add_ofReal_of_toReal_le {μ ν : Measure (Set.Icc (0 : ℝ) 1)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {B C : Set (Set.Icc (0 : ℝ) 1)} {c : ℝ}
    (hc : 0 ≤ c) (h : (μ B).toReal ≤ (ν C).toReal + c) : μ B ≤ ν C + ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ B), ← ENNReal.ofReal_toReal (measure_ne_top ν C),
    ← ENNReal.ofReal_add ENNReal.toReal_nonneg hc]
  exact ENNReal.ofReal_le_ofReal h

/-- **The weak convergence estimate.** The binomial approximant of `η` at level `2 ^ (3 m)` lies
within `2⁻ᵐ` of `η` in Lévy–Prokhorov distance.

The proof couples the two measures through the Bernstein basis: for `x ∈ B`, all but `2⁻ᵐ / 4`
of the binomial mass `Bin(2 ^ (3 m), x)` sits on grid points within `2⁻ᵐ` of `x`, hence inside
any `ε`-thickening of `B` with `2⁻ᵐ < ε`. -/
theorem levyProkhorovDist_binomialApproximant_le (m : ℕ)
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    levyProkhorovDist η.toMeasure (binomialApproximant (2 ^ (3 * m)) η).toMeasure ≤
      (2 : ℝ)⁻¹ ^ m := by
  classical
  have hδ : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  refine levyProkhorovDist_le_of_forall_le _ _ hδ.le fun ε B hεgt hB ↦ ?_
  have hT : MeasurableSet (thickening ε B) := isOpen_thickening.measurableSet
  refine le_add_ofReal_of_toReal_le (hδ.trans hεgt).le ?_
  -- The grid points inside the `ε`-thickening of `B`.
  set S : Finset (Fin (2 ^ (3 * m) + 1)) :=
    Finset.univ.filter fun k ↦ bernstein.z k ∈ thickening ε B with hS_def
  have hS : ∀ k, k ∈ S ↔ bernstein.z k ∈ thickening ε B := by
    intro k; simp [hS_def]
  rw [binomialApproximant_apply_toReal η hT S hS, ← measureReal_def, ← integral_indicator_one hB]
  -- Pointwise: the indicator of `B` is dominated by the near-`B` Bernstein mass, plus `ε`.
  have hpt : ∀ x : Set.Icc (0 : ℝ) 1,
      B.indicator (1 : Set.Icc (0 : ℝ) 1 → ℝ) x ≤
        (∑ k ∈ S, bernstein (2 ^ (3 * m)) k x) + ε := by
    intro x
    by_cases hxB : x ∈ B
    · rw [Set.indicator_of_mem hxB, Pi.one_apply]
      -- The grid points near `x` are among those in the thickening of `B`.
      have hsub : (Finset.univ.filter fun k : Fin (2 ^ (3 * m) + 1) ↦
            ¬ (2 : ℝ)⁻¹ ^ m < |(x : ℝ) - bernstein.z k|) ⊆ S := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hk
        refine (hS k).mpr (mem_thickening_iff.mpr ⟨x, hxB, ?_⟩)
        rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
        exact lt_of_le_of_lt hk hεgt
      have hmono : ∑ k ∈ Finset.univ.filter fun k : Fin (2 ^ (3 * m) + 1) ↦
            ¬ (2 : ℝ)⁻¹ ^ m < |(x : ℝ) - bernstein.z k|, bernstein (2 ^ (3 * m)) k x ≤
          ∑ k ∈ S, bernstein (2 ^ (3 * m)) k x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ bernstein_nonneg
      -- All but `2⁻ᵐ / 4` of the binomial mass sits near `x`.
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin (2 ^ (3 * m) + 1)))
        (fun k ↦ (2 : ℝ)⁻¹ ^ m < |(x : ℝ) - bernstein.z k|)
        fun k ↦ bernstein (2 ^ (3 * m)) k x
      rw [bernstein.probability] at hsplit
      linarith [sum_bernstein_far_le_dyadic m x]
    · rw [Set.indicator_of_notMem hxB]
      linarith [sum_bernstein_nonneg x S, hδ.trans hεgt]
  have hSint : Integrable (fun x : Set.Icc (0 : ℝ) 1 ↦ ∑ k ∈ S, bernstein (2 ^ (3 * m)) k x)
      η.toMeasure :=
    integrable_of_continuous (continuous_finsetSum S fun k _ ↦
      (bernstein (2 ^ (3 * m)) k).continuous)
  have hint := integral_mono ((integrable_const (1 : ℝ)).indicator hB)
    (hSint.add (integrable_const ε)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add hSint (integrable_const ε)] at hint
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul] at hint
  exact hint

end ComputableAnalysis
