/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.Admissibility

/-!
# The converse admissibility half: realizable ⇒ pointwise continuous

Unit 34's converse to the Cauchy-admissibility bridge: any advice-realized map between
Cauchy-presented metric spaces is continuous. Together with unit 29's
`continuous_advisedRealizable`, the carrier of `funRep P.cauchyRep Q.cauchyRep` is
*exactly* the continuous maps.

The proof is the classical finite-use argument, run pointwise at the names where the
(partial) realizer converges:

* **Finite use** (`OracleCode.eval_eq_of_agree_on_use`): each output coordinate of the
  realizer on the advice-interleaved oracle is determined by finitely many oracle
  coordinates. The advice track is *fixed*, so only finitely many argument-name
  coordinates matter — all of index `≤ M` for `M` the sup of the use set.
* **Name extension** (`exists_namesPoint_agree`): a *slack* name of `x` (one naming `x`
  at the shifted rate `(2⁻¹)^(i+1)`, obtained by dropping the head of any fast name)
  can be transplanted onto any `x'` with `dist x' x ≤ (2⁻¹)^(M+1)`: keep coordinates
  `≤ M` (the slack absorbs the perturbation: `(2⁻¹)^(i+1) + (2⁻¹)^(M+1) ≤ (2⁻¹)^i` for
  `i ≤ M`) and continue with any fast name of `x'` from density plus choice.

Constants (documented per the unit contract): with output precision `m` chosen so that
`(2⁻¹)^m < ε/2`, the modulus at `x` is `δ = (2⁻¹)^(M+1)` where `M` is the sup of the
finite use set of output coordinate `m` on the interleaved oracle; the final estimate is
`dist (f x') (f x) ≤ (2⁻¹)^m + (2⁻¹)^m < ε`.

## Main results

* `continuous_of_advisedRealizes` — advised realization over the fast Cauchy
  representations forces continuity.
* `RealizableFun.continuous_toFun_of_cauchy` — every point of the Cauchy function space
  has a continuous underlying map.
-/

namespace ComputableAnalysis

open OracleCode Metric ComputableMetricPresentation

variable {X Y : Type} [MetricSpace X] [MetricSpace Y]

/-- **Name extension.** Given a *slack* name of `x` — dense indices approximating `x` at
the shifted rate `(2⁻¹)^(i+1)` — every `x'` within `(2⁻¹)^(M+1)` of `x` has a genuine
fast Cauchy name agreeing with the given one on all coordinates `≤ M`: the kept
coordinates satisfy the pinned rate because
`(2⁻¹)^(i+1) + (2⁻¹)^(M+1) ≤ (2⁻¹)^(i+1) + (2⁻¹)^(i+1) = (2⁻¹)^i` for `i ≤ M`, and the
tail continues with an arbitrary fast name of `x'` from density plus choice. -/
private theorem exists_namesPoint_agree (P : ComputableMetricPresentation X) {p : Baire}
    {x : X} (hp : ∀ i, dist (P.dense (p i)) x ≤ ((2 : ℝ)⁻¹) ^ (i + 1)) (M : ℕ) {x' : X}
    (hx' : dist x' x ≤ ((2 : ℝ)⁻¹) ^ (M + 1)) :
    ∃ p' : Baire, P.NamesPoint p' x' ∧ ∀ k ≤ M, p' k = p k := by
  classical
  have hd : ∀ n : ℕ, ∃ i, dist (P.dense i) x' ≤ ((2 : ℝ)⁻¹) ^ n := fun n => by
    obtain ⟨i, hi⟩ := P.denseRange.exists_dist_lt x'
      (by positivity : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ n)
    exact ⟨i, by rw [dist_comm]; exact hi.le⟩
  refine ⟨fun k => if k ≤ M then p k else (hd k).choose, fun k => ?_, fun k hk => ite_eq_left hk⟩
  change dist (P.dense (if k ≤ M then p k else (hd k).choose)) x' ≤ ((2 : ℝ)⁻¹) ^ k
  by_cases hk : k ≤ M
  · rw [ite_eq_left hk]
    have hMk : ((2 : ℝ)⁻¹) ^ (M + 1) ≤ ((2 : ℝ)⁻¹) ^ (k + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    calc dist (P.dense (p k)) x'
        ≤ dist (P.dense (p k)) x + dist x x' := dist_triangle _ _ _
      _ ≤ ((2 : ℝ)⁻¹) ^ (k + 1) + ((2 : ℝ)⁻¹) ^ (k + 1) := by
          rw [dist_comm x x']
          exact add_le_add (hp k) (hx'.trans hMk)
      _ = ((2 : ℝ)⁻¹) ^ k := by rw [pow_succ]; ring
  · rw [ite_eq_right hk]
    exact (hd k).choose_spec

/-- **Realizable ⇒ continuous** (the converse admissibility half). A map advised-realized
over the fast Cauchy representations is continuous: each output coordinate of the
realizer has finite use on the interleaved oracle, the advice track is fixed, and nearby
points have names agreeing with a slack name of `x` on the finitely many argument
coordinates read (`exists_namesPoint_agree`), so output names agree at the queried
coordinate and the images are `2·(2⁻¹)^m`-close. -/
theorem continuous_of_advisedRealizes (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) {c : OracleCode} {q : Baire} {f : X → Y}
    (h : AdvisedRealizes P.cauchyRep Q.cauchyRep c q f) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  -- a slack name of `x`: drop the head of any fast name, leaving rate `(2⁻¹)^(i+1)`
  obtain ⟨p₀, hp₀⟩ := P.cauchyRep.onto x
  have hx₀ : P.NamesPoint p₀ x := P.cauchyRep_names_iff.mp hp₀
  set p₁ : Baire := fun i => p₀ (i + 1) with hp₁def
  have hslack : ∀ i, dist (P.dense (p₁ i)) x ≤ ((2 : ℝ)⁻¹) ^ (i + 1) := fun i =>
    hx₀ (i + 1)
  have hpx : P.cauchyRep.Names p₁ x := P.cauchyRep_names_iff.mpr fun i =>
    (hslack i).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ i))
  obtain ⟨r, hr, hrf⟩ := h p₁ x hpx
  have hrn : Q.NamesPoint r (f x) := Q.cauchyRep_names_iff.mp hrf
  -- output precision `m` with `2 · (2⁻¹)^m < ε`
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (half_pos hε) (by norm_num : (2 : ℝ)⁻¹ < 1)
  -- finite use of output coordinate `m`; `M` bounds every argument coordinate read
  obtain ⟨u, hu⟩ := eval_eq_of_agree_on_use (mem_evalStream.mp hr m)
  set M := u.sup id with hMdef
  refine ⟨((2 : ℝ)⁻¹) ^ (M + 1), by positivity, fun x' hx' => ?_⟩
  obtain ⟨p', hp', hagree⟩ := exists_namesPoint_agree P hslack M hx'.le
  obtain ⟨r', hr', hr'f⟩ := h p' x' (P.cauchyRep_names_iff.mpr hp')
  have hr'n : Q.NamesPoint r' (f x') := Q.cauchyRep_names_iff.mp hr'f
  -- the two interleaved oracles agree on the use set: even = the fixed advice,
  -- odd = argument coordinates `≤ M`, kept by the name extension
  have horacle : ∀ j ∈ u, Baire.interleave q p' j = Baire.interleave q p₁ j := by
    intro j hj
    rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
    · rw [Baire.interleave_even, Baire.interleave_even]
    · have hle : 2 * k + 1 ≤ M := Finset.le_sup (f := id) hj
      rw [Baire.interleave_odd, Baire.interleave_odd, hagree k (by omega)]
  have hrm : r' m = r m := Part.mem_unique (mem_evalStream.mp hr' m) (hu _ horacle)
  have hr'nm : dist (Q.dense (r m)) (f x') ≤ ((2 : ℝ)⁻¹) ^ m := by
    rw [← hrm]
    exact hr'n m
  calc dist (f x') (f x)
      ≤ dist (f x') (Q.dense (r m)) + dist (Q.dense (r m)) (f x) := dist_triangle _ _ _
    _ ≤ ((2 : ℝ)⁻¹) ^ m + ((2 : ℝ)⁻¹) ^ m := by
        rw [dist_comm (f x') (Q.dense (r m))]
        exact add_le_add hr'nm (hrn m)
    _ < ε := by linarith

/-- Every point of the Cauchy function space `funRep P.cauchyRep Q.cauchyRep` has a
continuous underlying map: unpack the realizability certificate and apply
`continuous_of_advisedRealizes`. -/
theorem RealizableFun.continuous_toFun_of_cauchy {P : ComputableMetricPresentation X}
    {Q : ComputableMetricPresentation Y} (f : RealizableFun P.cauchyRep Q.cauchyRep) :
    Continuous f.toFun := by
  obtain ⟨c, q, hc⟩ := f.exists_advised
  exact continuous_of_advisedRealizes P Q hc

end ComputableAnalysis
