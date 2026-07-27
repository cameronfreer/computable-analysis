/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.BinomialApproximant
import ComputableAnalysis.Measure.HausdorffMoments

/-!
# From approximate moments to a probability vector of binomial weights

The binomial weight `binomialWeight N k η = ∫ p, bernstein N k p ∂η` of
`ComputableAnalysis.Measure.BinomialApproximant` is a *polynomial* functional of `η`, hence
an explicit finite linear combination of the moments of `η` (`binomialWeight_eq_moment_sum`):

  `binomialWeight N k η = C(N, k) * ∑ j ≤ N - k, (-1)^j * C(N - k, j) * moment η (k + j)`.

This module turns that identity into a quantitative reconstruction: given *any* real vector
`a : ℕ → ℝ` with `|a n - moment η n| ≤ δ` for every `n`, the *approximate weights*
`approxWeight N k a` obtained by substituting `a` for the moments approximate the true
weights in `ℓ¹`, with the explicit constant `3 ^ N` (`sum_abs_approxWeight_sub_le`):
the coefficient mass of the `k`-th weight is `C(N, k) * 2 ^ (N - k)`, and
`∑ k, C(N, k) * 2 ^ (N - k) = 3 ^ N` (`sum_choose_mul_two_pow`) by the binomial theorem at
`(1 + 2) ^ N`.

The approximate weights need not be nonnegative and need not sum to `1`, so they are
repaired in two steps, each of which is proved not to spoil the `ℓ¹` estimate:

* **clipping** into `[0, 1]` (`clipWeight`), which is `1`-Lipschitz and fixes the true
  weights, hence can only decrease the error (`sum_abs_clipWeight_sub_le`);
* **normalisation** by the clipped total `totalClipWeight` (`normWeight`), which is legitimate
  because `3 ^ N * δ < 1` forces `0 < totalClipWeight N a` (`totalClipWeight_pos`), and costs
  at most a second `3 ^ N * δ` (`sum_abs_normWeight_sub_le`).

The outcome is a genuine probability vector — `normWeight_nonneg` and `sum_normWeight` — at
`ℓ¹` distance at most `2 * 3 ^ N * δ` from the binomial weights of `η`.

Everything here is classical and real-valued: no rational codes, no names, no computability.
The carrier already supplies the measure `η`, so nonnegativity and total mass one of the true
weights come from the Bernstein integral (`binomialWeight_nonneg`, `sum_binomialWeight`).
In particular `IsCompletelyMonotone` appears in no hypothesis: nothing here asserts, or
needs, that an abstract sequence is realized by a measure.
-/

namespace ComputableAnalysis

open MeasureTheory

/-! ### The exact moment expansion of a binomial weight -/

/-- Every monomial is integrable against a probability measure on the compact space `[0, 1]`. -/
private theorem integrable_pow (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) (m : ℕ) :
    Integrable (fun p : Set.Icc (0 : ℝ) 1 ↦ (p : ℝ) ^ m) η.toMeasure :=
  Continuous.integrable_of_hasCompactSupport (by fun_prop) (HasCompactSupport.of_compactSpace _)

/-- Expanding `(1 - p) ^ (N - k)` by the binomial theorem writes the `k`-th Bernstein basis
polynomial of degree `N` as an explicit alternating combination of monomials. -/
private theorem bernstein_eq_sum_pow (N : ℕ) (k : Fin (N + 1)) (p : Set.Icc (0 : ℝ) 1) :
    bernstein N k p = ∑ j ∈ Finset.range (N - (k : ℕ) + 1),
      (N.choose k : ℝ) * ((-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ)) *
        (p : ℝ) ^ ((k : ℕ) + j) := by
  rw [bernstein_apply, show (1 : ℝ) - (p : ℝ) = -(p : ℝ) + 1 by ring, add_pow, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [one_pow, mul_one, neg_pow, pow_add]; ring

/-- **The binomial weight is an explicit linear combination of the moments.** Expanding
`(1 - p) ^ (N - k)` and integrating termwise turns `∫ p, bernstein N k p ∂η` into the
alternating sum

  `C(N, k) * ∑ j ≤ N - k, (-1)^j * C(N - k, j) * moment η (k + j)`.

This is the bridge from the moment sequence of `η` to its binomial approximant. -/
theorem binomialWeight_eq_moment_sum (N : ℕ) (k : Fin (N + 1))
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    binomialWeight N k η = (N.choose k : ℝ) * ∑ j ∈ Finset.range (N - (k : ℕ) + 1),
      (-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ) * moment η ((k : ℕ) + j) := by
  rw [binomialWeight, integral_congr_ae (.of_forall (bernstein_eq_sum_pow N k)),
    integral_finsetSum _ fun j _ ↦ (integrable_pow η _).const_mul _]
  simp only [moment]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- Each binomial weight is at most `1`: the weights are nonnegative and sum to `1`. -/
theorem binomialWeight_le_one (N : ℕ) (k : Fin (N + 1))
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) : binomialWeight N k η ≤ 1 := by
  rw [← sum_binomialWeight N η]
  exact Finset.single_le_sum (fun i _ ↦ binomialWeight_nonneg N i η) (Finset.mem_univ k)

/-! ### The coefficient `ℓ¹` budget -/

/-- **The coefficient-mass identity.** The alternating expansion of `binomialWeight N k η`
carries total coefficient mass `C(N, k) * ∑ j ≤ N - k, C(N - k, j) = C(N, k) * 2 ^ (N - k)`,
and summing that over `k` gives `3 ^ N`, by the binomial theorem at `(1 + 2) ^ N`. -/
theorem sum_choose_mul_two_pow (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), N.choose k * 2 ^ (N - k) = 3 ^ N := by
  have h := (add_pow (1 : ℕ) 2 N).symm
  norm_num at h
  rw [← h]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- The real-valued form of `sum_choose_mul_two_pow`, indexed by `Fin (N + 1)`. -/
private theorem sum_choose_mul_two_pow_real (N : ℕ) :
    ∑ k : Fin (N + 1), (N.choose k : ℝ) * 2 ^ (N - (k : ℕ)) = 3 ^ N := by
  rw [Fin.sum_univ_eq_sum_range fun k ↦ (N.choose k : ℝ) * 2 ^ (N - k)]
  exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (sum_choose_mul_two_pow N)

/-! ### Approximate weights -/

/-- The **approximate binomial weight** built from a real vector `a : ℕ → ℝ` of putative
moments: the exact expansion of `binomialWeight N k η` given by `binomialWeight_eq_moment_sum`,
with `a (k + j)` substituted for `moment η (k + j)`. -/
noncomputable def approxWeight (N : ℕ) (k : Fin (N + 1)) (a : ℕ → ℝ) : ℝ :=
  (N.choose k : ℝ) * ∑ j ∈ Finset.range (N - (k : ℕ) + 1),
    (-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ) * a ((k : ℕ) + j)

/-- A single approximate weight is off by at most its coefficient mass `C(N, k) * 2 ^ (N - k)`
times the moment error `δ`. -/
theorem abs_approxWeight_sub_le {N : ℕ} (k : Fin (N + 1))
    {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)} {a : ℕ → ℝ} {δ : ℝ}
    (ha : ∀ n, |a n - moment η n| ≤ δ) :
    |approxWeight N k a - binomialWeight N k η| ≤ (N.choose k : ℝ) * 2 ^ (N - (k : ℕ)) * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (ha 0)
  rw [binomialWeight_eq_moment_sum, approxWeight, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg _), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  calc |∑ j ∈ Finset.range (N - (k : ℕ) + 1),
          ((-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ) * a ((k : ℕ) + j) -
            (-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ) * moment η ((k : ℕ) + j))|
      ≤ ∑ j ∈ Finset.range (N - (k : ℕ) + 1),
          |(-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ) * a ((k : ℕ) + j) -
            (-1 : ℝ) ^ j * ((N - (k : ℕ)).choose j : ℝ) * moment η ((k : ℕ) + j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (N - (k : ℕ) + 1), ((N - (k : ℕ)).choose j : ℝ) * δ := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (Nat.cast_nonneg _)]
        exact mul_le_mul_of_nonneg_left (ha _) (Nat.cast_nonneg _)
    _ = 2 ^ (N - (k : ℕ)) * δ := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_range_choose (N - (k : ℕ)))

/-- **The `ℓ¹` budget for the approximate weights.** If `a` approximates every moment of `η`
to within `δ`, the approximate weights approximate the binomial weights to within `3 ^ N * δ`
in total. The constant is exactly the coefficient mass `∑ k, C(N, k) * 2 ^ (N - k) = 3 ^ N`. -/
theorem sum_abs_approxWeight_sub_le (N : ℕ) {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    {a : ℕ → ℝ} {δ : ℝ} (ha : ∀ n, |a n - moment η n| ≤ δ) :
    ∑ k : Fin (N + 1), |approxWeight N k a - binomialWeight N k η| ≤ 3 ^ N * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (ha 0)
  calc ∑ k : Fin (N + 1), |approxWeight N k a - binomialWeight N k η|
      ≤ ∑ k : Fin (N + 1), (N.choose k : ℝ) * 2 ^ (N - (k : ℕ)) * δ :=
        Finset.sum_le_sum fun k _ ↦ abs_approxWeight_sub_le k ha
    _ = 3 ^ N * δ := by rw [← Finset.sum_mul, sum_choose_mul_two_pow_real]

/-! ### Clipping into `[0, 1]`

The two real facts used are that `max 0 (min 1 ·)` fixes `[0, 1]` and is `1`-Lipschitz; both
are already public in `ComputableAnalysis.Metric.Real`, as `clamp_eq_self` and
`abs_clamp_sub_clamp_le`. -/

/-- The **clipped weight** `max 0 (min 1 x)`: the projection of a real number onto `[0, 1]`. -/
noncomputable def clipWeight (x : ℝ) : ℝ := max 0 (min 1 x)

/-- A clipped weight is nonnegative. -/
theorem clipWeight_nonneg (x : ℝ) : 0 ≤ clipWeight x := le_max_left _ _

/-- Clipping is `1`-Lipschitz. -/
theorem abs_clipWeight_sub_clipWeight_le (x y : ℝ) :
    |clipWeight x - clipWeight y| ≤ |x - y| :=
  abs_clamp_sub_clamp_le x y

/-- Clipping fixes a true binomial weight, which already lies in `[0, 1]`. -/
theorem clipWeight_binomialWeight (N : ℕ) (k : Fin (N + 1))
    (η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    clipWeight (binomialWeight N k η) = binomialWeight N k η :=
  clamp_eq_self ⟨binomialWeight_nonneg N k η, binomialWeight_le_one N k η⟩

/-- **Clipping does not spoil the `ℓ¹` estimate.** Clipping is `1`-Lipschitz and fixes the true
weights, so the clipped approximate weights are still within `3 ^ N * δ` of the binomial
weights in total — and, unlike the raw approximate weights, they lie in `[0, 1]`. -/
theorem sum_abs_clipWeight_sub_le (N : ℕ) {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    {a : ℕ → ℝ} {δ : ℝ} (ha : ∀ n, |a n - moment η n| ≤ δ) :
    ∑ k : Fin (N + 1), |clipWeight (approxWeight N k a) - binomialWeight N k η| ≤ 3 ^ N * δ := by
  refine le_trans (Finset.sum_le_sum fun k _ ↦ ?_) (sum_abs_approxWeight_sub_le N ha)
  calc |clipWeight (approxWeight N k a) - binomialWeight N k η|
      = |clipWeight (approxWeight N k a) - clipWeight (binomialWeight N k η)| := by
        rw [clipWeight_binomialWeight]
    _ ≤ |approxWeight N k a - binomialWeight N k η| := abs_clipWeight_sub_clipWeight_le _ _

/-! ### Normalisation -/

/-- The total mass of the clipped approximate weights at level `N`. -/
noncomputable def totalClipWeight (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ k : Fin (N + 1), clipWeight (approxWeight N k a)

/-- The clipped total is nonnegative. -/
theorem totalClipWeight_nonneg (N : ℕ) (a : ℕ → ℝ) : 0 ≤ totalClipWeight N a :=
  Finset.sum_nonneg fun _ _ ↦ clipWeight_nonneg _

/-- The clipped total is within `3 ^ N * δ` of `1`, because the true weights sum to `1` and
the clipped weights are within `3 ^ N * δ` of them in `ℓ¹`. -/
theorem abs_totalClipWeight_sub_one_le (N : ℕ) {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    {a : ℕ → ℝ} {δ : ℝ} (ha : ∀ n, |a n - moment η n| ≤ δ) :
    |totalClipWeight N a - 1| ≤ 3 ^ N * δ := by
  have hsum : totalClipWeight N a - 1 =
      ∑ k : Fin (N + 1), (clipWeight (approxWeight N k a) - binomialWeight N k η) := by
    rw [Finset.sum_sub_distrib, sum_binomialWeight N η, totalClipWeight]
  rw [hsum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (sum_abs_clipWeight_sub_le N ha)

/-- **Positivity of the clipped total.** As soon as the moment error is small enough that
`3 ^ N * δ < 1`, the clipped approximate weights have strictly positive total mass, so they can
be normalised. This is what guarantees that no degenerate fallback is ever needed. -/
theorem totalClipWeight_pos (N : ℕ) {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)} {a : ℕ → ℝ}
    {δ : ℝ} (ha : ∀ n, |a n - moment η n| ≤ δ) (hδ : 3 ^ N * δ < 1) :
    0 < totalClipWeight N a := by
  have h := abs_le.mp (abs_totalClipWeight_sub_one_le N ha)
  linarith [h.1]

/-- The **normalised weight**: the clipped approximate weight, rescaled to make the family sum
to `1`. Well behaved as soon as `3 ^ N * δ < 1`, by `totalClipWeight_pos`. -/
noncomputable def normWeight (N : ℕ) (k : Fin (N + 1)) (a : ℕ → ℝ) : ℝ :=
  clipWeight (approxWeight N k a) / totalClipWeight N a

/-- The normalised weights are nonnegative. No hypothesis is needed: both the clipped weight
and the clipped total are nonnegative. -/
theorem normWeight_nonneg (N : ℕ) (k : Fin (N + 1)) (a : ℕ → ℝ) : 0 ≤ normWeight N k a :=
  div_nonneg (clipWeight_nonneg _) (totalClipWeight_nonneg N a)

/-- The normalised weights sum to `1`, so together with `normWeight_nonneg` they form a genuine
probability vector on the grid `{k / N : k ≤ N}`. -/
theorem sum_normWeight (N : ℕ) {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)} {a : ℕ → ℝ} {δ : ℝ}
    (ha : ∀ n, |a n - moment η n| ≤ δ) (hδ : 3 ^ N * δ < 1) :
    ∑ k : Fin (N + 1), normWeight N k a = 1 := by
  have hS := (totalClipWeight_pos N ha hδ).ne'
  calc ∑ k : Fin (N + 1), normWeight N k a
      = (∑ k : Fin (N + 1), clipWeight (approxWeight N k a)) / totalClipWeight N a := by
        simp only [normWeight]
        rw [Finset.sum_div]
    _ = 1 := div_self hS

/-- **The `ℓ¹` reconstruction bound.** If `a` approximates every moment of `η` to within `δ`
and `3 ^ N * δ < 1`, the normalised weights approximate the binomial weights of `η` to within
`2 * 3 ^ N * δ` in total.

The second copy of `3 ^ N * δ` is the price of normalisation: writing `c k` for the clipped
weights and `S` for their total, `∑ k, |c k / S - c k| = |1 / S - 1| * S = |1 - S|`, which is
itself at most `3 ^ N * δ`. -/
theorem sum_abs_normWeight_sub_le (N : ℕ) {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    {a : ℕ → ℝ} {δ : ℝ} (ha : ∀ n, |a n - moment η n| ≤ δ) (hδ : 3 ^ N * δ < 1) :
    ∑ k : Fin (N + 1), |normWeight N k a - binomialWeight N k η| ≤ 2 * 3 ^ N * δ := by
  have hS : 0 < totalClipWeight N a := totalClipWeight_pos N ha hδ
  have hstep : ∀ k : Fin (N + 1),
      |normWeight N k a - clipWeight (approxWeight N k a)| =
        clipWeight (approxWeight N k a) * |1 / totalClipWeight N a - 1| := by
    intro k
    have hfac : clipWeight (approxWeight N k a) / totalClipWeight N a -
        clipWeight (approxWeight N k a) =
          clipWeight (approxWeight N k a) * (1 / totalClipWeight N a - 1) := by ring
    rw [normWeight, hfac, abs_mul, abs_of_nonneg (clipWeight_nonneg _)]
  have hne : totalClipWeight N a ≠ 0 := hS.ne'
  have hnorm : totalClipWeight N a * |1 / totalClipWeight N a - 1| =
      |1 - totalClipWeight N a| := by
    have h1 : 1 / totalClipWeight N a - 1 =
        (1 - totalClipWeight N a) / totalClipWeight N a := by field_simp
    rw [h1, abs_div, abs_of_pos hS]
    field_simp
  calc ∑ k : Fin (N + 1), |normWeight N k a - binomialWeight N k η|
      ≤ ∑ k : Fin (N + 1), (|normWeight N k a - clipWeight (approxWeight N k a)| +
          |clipWeight (approxWeight N k a) - binomialWeight N k η|) :=
        Finset.sum_le_sum fun k _ ↦ abs_sub_le _ _ _
    _ = (∑ k : Fin (N + 1), |normWeight N k a - clipWeight (approxWeight N k a)|) +
          ∑ k : Fin (N + 1), |clipWeight (approxWeight N k a) - binomialWeight N k η| :=
        Finset.sum_add_distrib
    _ = |1 - totalClipWeight N a| +
          ∑ k : Fin (N + 1), |clipWeight (approxWeight N k a) - binomialWeight N k η| := by
        rw [Finset.sum_congr rfl fun k _ ↦ hstep k, ← Finset.sum_mul, ← totalClipWeight, hnorm]
    _ ≤ 3 ^ N * δ + 3 ^ N * δ := by
        refine add_le_add ?_ (sum_abs_clipWeight_sub_le N ha)
        rw [abs_sub_comm]
        exact abs_totalClipWeight_sub_one_le N ha
    _ = 2 * 3 ^ N * δ := by ring

end ComputableAnalysis
