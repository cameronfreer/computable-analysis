/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Moments of a probability measure on the unit interval

The moment sequence `moment η n = ∫ p^n dη` of a probability measure on `[0, 1]`. Its two
basic properties are recorded here — every moment lies in `[0, 1]`, and the zeroth is `1` —
together with complete monotonicity and, the substantial result, **determinacy**: a
probability measure on `[0, 1]` is determined by its moments.

Determinacy is proved by Weierstrass approximation. Polynomials integrate according to their
coefficients and moments, so equal moments give equal integrals of every polynomial; uniform
approximation transfers that to every bounded continuous function; and a finite Borel measure
is determined by those integrals.

Only determinacy is proved here. The converse — that every normalized completely monotone
sequence is realized by some measure — is a genuinely separate classical theorem and is not
needed by anything downstream of this module, since the representations built on moments have
*measures* as their carrier and so only ever need names for measures that already exist.

The module closes with `hausdorffMomentRep`, the representation of a measure by a packed
family of names of all its moments. Determinacy is exactly what makes that a representation:
it is what forces a moment name to determine its measure.
-/

namespace ComputableAnalysis

open MeasureTheory

/-- The `n`-th moment `∫ p^n dη` of a probability measure on the unit interval. -/
noncomputable def moment (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) (n : ℕ) : ℝ :=
  ∫ p, (p : ℝ) ^ n ∂η.toMeasure

/-- Moments of a probability measure on `[0, 1]` lie in `[0, 1]`: the integrand `p ^ n` is
itself confined to `[0, 1]`, and the measure has total mass one. -/
theorem moment_mem_unitInterval (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) (n : ℕ) :
    moment η n ∈ Set.Icc (0 : ℝ) 1 := by
  have hint : Integrable (fun p : Set.Icc (0 : ℝ) 1 => (p : ℝ) ^ n) η.toMeasure :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)
  refine Set.mem_Icc.mpr ⟨integral_nonneg fun p => pow_nonneg p.2.1 n, ?_⟩
  calc moment η n ≤ ∫ _ : Set.Icc (0 : ℝ) 1, (1 : ℝ) ∂η.toMeasure :=
        integral_mono hint (integrable_const 1) fun p => pow_le_one₀ p.2.1 p.2.2
    _ = 1 := by simp

/-- The zeroth moment of a probability measure is `1`. -/
theorem moment_zero (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) : moment η 0 = 1 := by
  simp [moment]

/-- Complete monotonicity of a sequence: all iterated forward differences alternate in sign,
phrased through the binomial expansion `(-1)^k Δ^k m n = ∑ j (-1)^j C(k,j) m (n+j) ≥ 0`. For a
moment sequence the sum is `∫ p^n (1-p)^k dη`. -/
def IsCompletelyMonotone (m : ℕ → ℝ) : Prop :=
  ∀ n k : ℕ, 0 ≤ ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) * m (n + j)

/-- Moment sequences are completely monotone: the alternating binomial sum is the integral of
`p ^ n (1 - p) ^ k`, which is nonnegative on `[0, 1]`. -/
theorem isCompletelyMonotone_moment (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    IsCompletelyMonotone (moment η) := by
  intro n k
  have hint : ∀ m : ℕ, Integrable (fun p : Set.Icc (0 : ℝ) 1 => (p : ℝ) ^ m) η.toMeasure :=
    fun m => Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (HasCompactSupport.of_compactSpace _)
  have hsum : ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) * moment η (n + j)
      = ∫ p : Set.Icc (0 : ℝ) 1, (p : ℝ) ^ n * (1 - (p : ℝ)) ^ k ∂η.toMeasure := by
    simp_rw [moment, ← integral_const_mul]
    rw [← integral_finsetSum _ fun j _ => (hint (n + j)).const_mul _]
    refine integral_congr_ae (.of_forall fun p => ?_)
    change ∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j * (k.choose j : ℝ) * (p : ℝ) ^ (n + j)
      = (p : ℝ) ^ n * (1 - (p : ℝ)) ^ k
    rw [show (1 : ℝ) - (p : ℝ) = -(p : ℝ) + 1 by ring, add_pow, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one, neg_pow, pow_add]; ring
  rw [hsum]
  exact integral_nonneg fun p =>
    mul_nonneg (pow_nonneg p.2.1 n) (pow_nonneg (sub_nonneg.mpr p.2.2) k)

/-- A continuous function on the compact space `[0, 1]` is integrable against a finite
measure. -/
private lemma integrable_of_continuous {μ : Measure (Set.Icc (0 : ℝ) 1)} [IsFiniteMeasure μ]
    {f : Set.Icc (0 : ℝ) 1 → ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- Integrating a polynomial against `η` is the corresponding linear combination of the
moments of `η`. -/
private lemma integral_polynomial_eq_sum_moment (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (q : Polynomial ℝ) :
    ∫ x, q.eval (x : ℝ) ∂η.toMeasure
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * moment η i := by
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [integral_finsetSum _ fun i _ ↦ integrable_of_continuous (by fun_prop)]
  simp_rw [integral_const_mul, moment]

/-- Integration against a probability measure on `[0, 1]` is `1`-Lipschitz for the uniform
norm on continuous functions. -/
private lemma abs_integral_sub_integral_le_norm (μ : Measure (Set.Icc (0 : ℝ) 1))
    [IsProbabilityMeasure μ] (f g : C(Set.Icc (0 : ℝ) 1, ℝ)) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂μ| ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_of_continuous f.continuous)
    (integrable_of_continuous g.continuous)]
  have := BoundedContinuousFunction.norm_integral_le_norm (μ := μ)
    (BoundedContinuousFunction.mkOfCompact (f - g))
  simpa [← BoundedContinuousFunction.mkOfCompact_sub,
    BoundedContinuousFunction.norm_mkOfCompact, Real.norm_eq_abs] using this

/-- **Moment determinacy on `[0, 1]`**: a probability measure on a compact interval is
determined by its moments, by Weierstrass density of the polynomials. -/
theorem eq_of_forall_moment_eq {η ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    (h : ∀ n, moment η n = moment ν n) : η = ν := by
  -- Equal moments give equal integrals of every continuous function, by Weierstrass.
  have key : ∀ f : C(Set.Icc (0 : ℝ) 1, ℝ),
      ∫ x, f x ∂η.toMeasure = ∫ x, f x ∂ν.toMeasure := by
    intro f
    have hle : ∀ ε : ℝ, 0 < ε →
        |(∫ x, f x ∂η.toMeasure) - ∫ x, f x ∂ν.toMeasure| ≤ 0 + ε := by
      intro ε hε
      obtain ⟨q, hq⟩ := exists_polynomial_near_continuousMap 0 1 f (ε / 3) (by positivity)
      set g : C(Set.Icc (0 : ℝ) 1, ℝ) := q.toContinuousMapOn (Set.Icc 0 1)
      have hgapp : ∀ x : Set.Icc (0 : ℝ) 1, g x = q.eval (x : ℝ) := fun _ ↦ rfl
      have hmid : ∫ x, g x ∂η.toMeasure = ∫ x, g x ∂ν.toMeasure := by
        simp_rw [hgapp, integral_polynomial_eq_sum_moment]
        exact Finset.sum_congr rfl fun i _ ↦ by rw [h i]
      have h1 : |(∫ x, f x ∂η.toMeasure) - ∫ x, g x ∂η.toMeasure| ≤ ε / 3 := by
        refine le_trans (abs_integral_sub_integral_le_norm _ f g) ?_
        rw [← norm_neg, neg_sub]
        exact hq.le
      have h2 : |(∫ x, g x ∂ν.toMeasure) - ∫ x, f x ∂ν.toMeasure| ≤ ε / 3 :=
        le_trans (abs_integral_sub_integral_le_norm _ g f) hq.le
      have h3 := abs_sub_le (∫ x, f x ∂η.toMeasure) (∫ x, g x ∂η.toMeasure)
        (∫ x, f x ∂ν.toMeasure)
      rw [hmid] at h1 h3
      linarith
    have h0 : |(∫ x, f x ∂η.toMeasure) - ∫ x, f x ∂ν.toMeasure| ≤ 0 :=
      le_of_forall_pos_le_add hle
    have habs := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
    linarith
  -- A finite Borel measure is determined by the integrals of bounded continuous functions.
  refine ProbabilityMeasure.toMeasure_injective ?_
  exact MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure fun f ↦
    key f.toContinuousMap

/-- Moment determinacy, as injectivity of the moment sequence map. -/
theorem moment_injective : Function.Injective moment :=
  fun _ _ h => eq_of_forall_moment_eq (congrFun h)

/-! ### The moment-sequence representation -/

/-- A moment name of `η` packs, at slice `n`, a `[0, 1]`-name of the `n`-th moment; slices are
indexed by `Nat.pair`, matching the repository's packing convention. -/
def MomentNames (F : Baire) (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) : Prop :=
  ∀ n : ℕ,
    unitIntervalRep.Names (fun k => F (Nat.pair n k)) ⟨moment η n, moment_mem_unitInterval η n⟩

/-- A moment name determines its measure: names of reals are single-valued, so the two
measures share every moment, and moments are determining. -/
theorem momentNames_unique {F : Baire} {η ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    (hη : MomentNames F η) (hν : MomentNames F ν) : η = ν :=
  eq_of_forall_moment_eq fun n =>
    congrArg Subtype.val (Representation.names_unique (hη n) (hν n))

/-- **The moment-sequence representation**: a name is a packed family of `[0, 1]`-names of all
moments. Genuinely partial (convention 2) — a stream naming no measure denotes nothing, and
there is no default measure.

The carrier is *measures*, so surjectivity only ever needs names for measures that already
exist; nothing here asserts that an arbitrary completely monotone sequence is realized. -/
noncomputable def hausdorffMomentRep :
    Representation (ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) where
  rep F := ⟨∃ η, MomentNames F η, fun h => h.choose⟩
  onto η := by
    classical
    have hname : ∀ n : ℕ, ∃ p : Baire,
        unitIntervalRep.Names p ⟨moment η n, moment_mem_unitInterval η n⟩ :=
      fun n => unitIntervalRep.onto _
    set g : ℕ → Baire := fun n => (hname n).choose with hg
    refine ⟨fun z => g z.unpair.1 z.unpair.2, ?_⟩
    have hM : MomentNames (fun z => g z.unpair.1 z.unpair.2) η := by
      intro n
      have hslice : (fun k => g (Nat.pair n k).unpair.1 (Nat.pair n k).unpair.2) = g n := by
        funext k
        rw [Nat.unpair_pair]
      rw [hslice, hg]
      exact (hname n).choose_spec
    exact ⟨⟨η, hM⟩, momentNames_unique (Exists.choose_spec _) hM⟩

/-- Names of the moment representation are exactly moment names — the chosen witness stays
hidden behind determinacy. -/
@[simp]
theorem hausdorffMomentRep_names_iff {F : Baire}
    {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)} :
    hausdorffMomentRep.Names F η ↔ MomentNames F η := by
  constructor
  · rintro ⟨hex, rfl⟩
    exact hex.choose_spec
  · intro h
    exact ⟨⟨η, h⟩, momentNames_unique (Exists.choose_spec _) h⟩

end ComputableAnalysis
