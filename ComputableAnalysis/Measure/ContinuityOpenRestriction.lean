/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.ContinuityOpenMass
import ComputableAnalysis.TypeTwo.Universal

/-!
# The normalized restriction to an effective continuity open

Conditioning a joint law on a set of positive mass is restriction followed by normalization.
This module shows that from a weak name of `µ` and an effective `µ`-continuity open `U` of
positive mass, one fixed oracle code emits a weak name of `µ (· ∩ U) / µ U`.

The route stays inside the atomic machinery: restrict and renormalize the atomic approximant
directly, and control the error by the *residual*, what neither track of the continuity-open
name has yet certified. Because the two tracks are disjoint and carry full mass, the residual's
`µ`-mass tends to zero; residual transfer moves that to the approximant across the
Lévy–Prokhorov bound, and the restriction estimate splits `A ∩ U` at the certified part so
that both error terms are effective. No lower-semicomputability characterization of the weak
representation is needed.

## Main definitions and results

* `residual`, `thickening_residual_subset`, `measure_residual_transfer` — the two-track
  residual and its transfer to an LP-close approximant.
* `measure_restrict_le`, `levyProkhorovEDist_restrict_le_dyadic` — the unnormalized
  restriction comparison with explicit error parameters.
* `normalizedRestriction`, `levyProkhorovEDist_normalize_lipschitz` — normalization is
  Lipschitz in Lévy–Prokhorov, with constant controlled by a positive mass floor.
* `explicit_normalized_budget` — the code-free budget the realizer certifies.
* `RestrictionSuccess`, `restrictionSuccess_sound`, `exists_restrictionSuccess` — the packed
  search witness, its soundness for every successful candidate, and its existence.
* `exists_contSetRestrictionCode` — the realizer.

## Implementation notes

The realizer's output is a finite submeasure made only of atoms certified inside `U`, so its
deficit has two sources: mass in the residual, and atoms genuinely inside that the finite
dovetail has not yet discovered. The packed witness `(level, stage, fuel, rest)` drives both;
soundness is candidate-wise, and the least successful packed index carries no semantic
ordering. Every rational the success test compares is built as a code, so the test is
primitive recursive and never touches `ℝ`.
-/

open MeasureTheory Metric Encodable Denumerable
open scoped ENNReal NNReal

set_option linter.style.longFile 1900

namespace ComputableAnalysis

open OracleCode

section ContinuityOpenRestriction

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {P : ComputableMetricPresentation X}

section Residual
variable (P)
/-- The stage-`n` residual: what neither track has yet certified. -/
noncomputable def residual (uv : Baire) (n : ℕ) : Set X :=
  (innerApprox P uv.evenPart n ∪ innerApprox P uv.oddPart n)ᶜ

omit [MeasurableSpace X] [BorelSpace X] in
theorem isClosed_residual (uv : Baire) (n : ℕ) : IsClosed (residual P uv n) :=
  isClosed_compl_iff.mpr ((isOpen_innerApprox _ n).union (isOpen_innerApprox _ n))

theorem measurableSet_residual (uv : Baire) (n : ℕ) : MeasurableSet (residual P uv n) :=
  (isClosed_residual P uv n).measurableSet

omit [MeasurableSpace X] [BorelSpace X] in
theorem antitone_residual (uv : Baire) : Antitone (residual P uv) := fun _ _ hij =>
  Set.compl_subset_compl.mpr
    (Set.union_subset_union (monotone_innerApprox P _ hij) (monotone_innerApprox P _ hij))

omit [MeasurableSpace X] [BorelSpace X] in
/-- One shrink stage absorbs a thickening of radius `2⁻ᵐ` when `k + 1 ≤ m`. -/
private theorem mem_innerApprox_succ_of_thickening {u : Baire} {k m : ℕ} (hkm : k + 1 ≤ m)
    {x y : X} (hxy : dist x y < (2 : ℝ)⁻¹ ^ m) (hx : x ∈ innerApprox P u k) :
    y ∈ innerApprox P u (k + 1) := by
  simp only [innerApprox, Set.mem_iUnion, Finset.mem_range, mem_ball, exists_prop] at hx ⊢
  obtain ⟨j, hj, hdist⟩ := hx
  refine ⟨j, Nat.lt_succ_of_lt hj, ?_⟩
  have hpow : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (k + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hkm
  have hhalf : (2 : ℝ)⁻¹ ^ k = 2 * (2 : ℝ)⁻¹ ^ (k + 1) := by ring
  have htri := dist_triangle y x (P.dense (u j).unpair.1)
  rw [dist_comm y x] at htri
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The two-scale containment.** Thickening the stage-`(k+1)` residual by `2⁻ᵐ` stays inside
the stage-`k` residual, provided `k + 1 ≤ m`. -/
theorem thickening_residual_subset (uv : Baire) {k m : ℕ} (hkm : k + 1 ≤ m) :
    thickening ((2 : ℝ)⁻¹ ^ m) (residual P uv (k + 1)) ⊆ residual P uv k := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  refine Set.mem_compl fun hmem => hy ?_
  rcases hmem with h | h
  · exact Set.mem_union_left _ (mem_innerApprox_succ_of_thickening P hkm hxy h)
  · exact Set.mem_union_right _ (mem_innerApprox_succ_of_thickening P hkm hxy h)

/-- **Residual transfer.** The approximant's residual mass at stage `k+1` is bounded by the
reference measure's residual mass at stage `k`, plus the Lévy–Prokhorov error. This is what
lets the `ν`-residual be driven to zero using only `μ`'s continuity information. -/
theorem measure_residual_transfer {μ ν : ProbabilityMeasure X} {uv : Baire} {c : ℝ≥0∞}
    {k m : ℕ} (hlt : levyProkhorovEDist ν.toMeasure μ.toMeasure < c)
    (hc : c ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m)) (hkm : k + 1 ≤ m) :
    ν.toMeasure (residual P uv (k + 1)) ≤ μ.toMeasure (residual P uv k) + c := by
  refine le_measure_of_thickening_subset hlt hc ENNReal.ofReal_ne_top
    (measurableSet_residual P uv (k + 1)) ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact thickening_residual_subset P uv hkm

variable {P}

end Residual
omit [MeasurableSpace X] [BorelSpace X] in
/-- What `U` leaves uncertified at stage `n` is inside the residual: a point of `U` outside
`innerApprox U n` is in neither track, the tracks being disjoint. -/
theorem diff_subset_residual {uv : Baire}
    (hdisj : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart)) (n : ℕ) :
    openOf P uv.evenPart \ innerApprox P uv.evenPart n ⊆ residual P uv n := by
  rintro x ⟨hxU, hxn⟩
  refine Set.mem_compl fun hx => ?_
  rcases hx with hxU' | hxV
  · exact hxn hxU'
  · have hVsub : innerApprox P uv.oddPart n ⊆ openOf P uv.oddPart := by
      rw [← iUnion_innerApprox P uv.oddPart]
      exact Set.subset_iUnion _ n
    exact Set.disjoint_left.mp hdisj hxU (hVsub hxV)

/-- **Unnormalized restriction comparison**, with both error parameters explicit: the
approximation error `c` from the Lévy–Prokhorov bound, and the residual mass at stage `n`.

Splitting `A ∩ U` at the certified part is what makes both terms effective — the certified part
goes through the engine estimate, and what is left over sits inside the residual. -/
theorem measure_restrict_le {μ ν : ProbabilityMeasure X} {uv : Baire} {c : ℝ≥0∞} {m n : ℕ}
    (hdisj : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart))
    (hlt : levyProkhorovEDist ν.toMeasure μ.toMeasure < c)
    (hc : c ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m)) (hnm : n ≤ m)
    {A : Set X} (hA : MeasurableSet A) :
    ν.toMeasure (A ∩ openOf P uv.evenPart)
      ≤ μ.toMeasure (thickening ((2 : ℝ)⁻¹ ^ m) A ∩ openOf P uv.evenPart) + c
          + ν.toMeasure (residual P uv n) := by
  have hinner : MeasurableSet (innerApprox P uv.evenPart n) := measurableSet_innerApprox _ n
  have hsplit : ν.toMeasure (A ∩ openOf P uv.evenPart)
      = ν.toMeasure ((A ∩ openOf P uv.evenPart) ∩ innerApprox P uv.evenPart n)
        + ν.toMeasure ((A ∩ openOf P uv.evenPart) \ innerApprox P uv.evenPart n) :=
    (measure_inter_add_sdiff _ hinner).symm
  have hcert : ν.toMeasure ((A ∩ openOf P uv.evenPart) ∩ innerApprox P uv.evenPart n)
      ≤ μ.toMeasure (thickening ((2 : ℝ)⁻¹ ^ m) A ∩ openOf P uv.evenPart) + c := by
    refine le_measure_of_thickening_subset hlt hc ENNReal.ofReal_ne_top
      ((hA.inter (isOpen_openOf P _).measurableSet).inter hinner) ?_
    rw [ENNReal.toReal_ofReal (by positivity)]
    refine Set.subset_inter ?_ ?_
    · exact thickening_subset_of_subset _ fun x hx => hx.1.1
    · exact subset_trans (thickening_subset_of_subset _ fun x hx => hx.2)
        (thickening_innerApprox_subset _ hnm)
  have hrest : ν.toMeasure ((A ∩ openOf P uv.evenPart) \ innerApprox P uv.evenPart n)
      ≤ ν.toMeasure (residual P uv n) :=
    measure_mono fun x hx => diff_subset_residual hdisj n ⟨hx.1.2, hx.2⟩
  rw [hsplit]
  exact add_le_add hcert hrest

omit [BorelSpace X] in
/-- Uniform closeness on measurable sets bounds the Lévy–Prokhorov distance. The thickening
in mathlib's criterion is free here: any `ε` exceeding `δ` is positive, so `B` sits inside
its own `ε`-thickening and monotonicity absorbs the difference. -/
theorem levyProkhorovEDist_le_of_forall_le_add {μ ν : Measure X} {δ : ℝ≥0∞}
    (h : ∀ B, MeasurableSet B → μ B ≤ ν B + δ ∧ ν B ≤ μ B + δ) :
    levyProkhorovEDist μ ν ≤ δ := by
  refine levyProkhorovEDist_le_of_forall μ ν δ fun ε B hδε hεtop hB => ?_
  have hε0 : 0 < ε := lt_of_le_of_lt (by simp : (0 : ℝ≥0∞) ≤ δ) hδε
  have hsub : B ⊆ thickening ε.toReal B :=
    self_subset_thickening (ENNReal.toReal_pos hε0.ne' hεtop.ne) B
  obtain ⟨h₁, h₂⟩ := h B hB
  exact ⟨h₁.trans (add_le_add (measure_mono hsub) hδε.le),
    h₂.trans (add_le_add (measure_mono hsub) hδε.le)⟩

omit [BorelSpace X] in
/-- **The certified-submeasure bridge.** If `ρ ≤ σ` and `ρ` omits at most `δ` of `σ`'s total
mass, then normalizing both moves them at most `δ / β` apart, where `β` is any positive lower
bound on `ρ`'s total mass.

This is the step `measure_restrict_le` cannot supply: the realizer never sees `σ = ν|U`, only
the finite certified submeasure `ρ`. Both sources of deficit — residual mass, and atoms inside
the certified region the dovetail has not yet found — enter only through `δ`, which is exactly
why they must be bounded separately upstream. -/
theorem levyProkhorovEDist_normalized_le {ρ σ : Measure X} [IsFiniteMeasure σ]
    (hle : ρ ≤ σ) {δ β : ℝ≥0∞} (hβ0 : 0 < β) (hβ : β ≤ ρ Set.univ)
    (hδ : σ Set.univ ≤ ρ Set.univ + δ) :
    levyProkhorovEDist ((ρ Set.univ)⁻¹ • ρ) ((σ Set.univ)⁻¹ • σ) ≤ δ / β := by
  set a := ρ Set.univ with ha
  set b := σ Set.univ with hb
  have hab : a ≤ b := Measure.le_iff'.mp hle _
  have hbtop : b ≠ ∞ := measure_ne_top σ _
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top hbtop hab
  have ha0 : a ≠ 0 := (lt_of_lt_of_le hβ0 hβ).ne'
  have hb0 : b ≠ 0 := fun h => ha0 (by simpa [h] using hab)
  -- `β ≤ a ≤ b` inverts the three reciprocals we need
  have hinv_ba : b⁻¹ ≤ a⁻¹ := ENNReal.inv_le_inv.mpr hab
  have hinv_bβ : b⁻¹ ≤ β⁻¹ := ENNReal.inv_le_inv.mpr (hβ.trans hab)
  refine levyProkhorovEDist_le_of_forall_le_add fun B hB => ?_
  have hρB : ρ B ≤ a := measure_mono (Set.subset_univ _)
  have hσρ : σ B ≤ ρ B + δ := by
    have hcompl : ρ Bᶜ ≤ σ Bᶜ := Measure.le_iff'.mp hle _
    have hsplit : σ B + σ Bᶜ ≤ ρ B + δ + σ Bᶜ := by
      calc σ B + σ Bᶜ = b := by rw [hb, ← measure_add_measure_compl hB]
        _ ≤ a + δ := hδ
        _ = ρ B + ρ Bᶜ + δ := by rw [ha, ← measure_add_measure_compl hB]
        _ ≤ ρ B + σ Bᶜ + δ := by gcongr
        _ = ρ B + δ + σ Bᶜ := by ring
    exact (ENNReal.add_le_add_iff_right (measure_ne_top σ _)).mp hsplit
  -- The single multiplicative step both directions share.
  have hkey : ρ B * a⁻¹ ≤ (ρ B + δ) * b⁻¹ := by
    have hunit : ρ B * a⁻¹ ≤ 1 := by
      calc ρ B * a⁻¹ ≤ a * a⁻¹ := by gcongr
        _ = 1 := ENNReal.mul_inv_cancel ha0 hatop
    have hmul : ρ B * a⁻¹ * b ≤ ρ B + δ := by
      calc ρ B * a⁻¹ * b ≤ ρ B * a⁻¹ * (a + δ) := by gcongr
        _ = ρ B * a⁻¹ * a + ρ B * a⁻¹ * δ := by ring
        _ ≤ ρ B + δ := by
            gcongr ?_ + ?_
            · rw [mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, mul_one]
            · simpa using mul_le_mul_left hunit δ
    have h := (ENNReal.le_div_iff_mul_le (Or.inl hb0) (Or.inl hbtop)).mpr hmul
    rwa [div_eq_mul_inv] at h
  have hexp : (ρ B + δ) * b⁻¹ = ρ B * b⁻¹ + δ * b⁻¹ := add_mul _ _ _
  have hδβ : δ * b⁻¹ ≤ δ / β := by rw [div_eq_mul_inv]; gcongr
  simp only [Measure.smul_apply, smul_eq_mul]
  constructor
  · calc a⁻¹ * ρ B = ρ B * a⁻¹ := mul_comm _ _
      _ ≤ ρ B * b⁻¹ + δ * b⁻¹ := hexp ▸ hkey
      _ ≤ b⁻¹ * σ B + δ / β := by rw [mul_comm (ρ B)]; gcongr
  · calc b⁻¹ * σ B = σ B * b⁻¹ := mul_comm _ _
      _ ≤ (ρ B + δ) * b⁻¹ := by gcongr
      _ = ρ B * b⁻¹ + δ * b⁻¹ := hexp
      _ ≤ a⁻¹ * ρ B + δ / β := by rw [mul_comm (ρ B)]; gcongr

/-- **(1a) The unnormalized restriction comparison.** Restricting two Lévy–Prokhorov-close
measures to a common open set keeps them close, with the loss controlled by the approximation
radius, the original distance, and the residual mass of BOTH measures.

This is the half of `restrict_lp_estimate` where the geometry lives; combined with
`levyProkhorovEDist_normalize_lipschitz` it yields the normalized statement. Note that both
residual terms appear: the certified/uncertified split is performed separately under each
measure, so neither side's residual can be dropped. -/
theorem levyProkhorovEDist_restrict_le {μ ν : ProbabilityMeasure X} {uv : Baire} {c : ℝ≥0∞}
    {m n : ℕ}
    (hdisj : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart))
    (hlt : levyProkhorovEDist μ.toMeasure ν.toMeasure < c)
    (hc : c ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m)) (hnm : n ≤ m) :
    levyProkhorovEDist (μ.toMeasure.restrict (openOf P uv.evenPart))
        (ν.toMeasure.restrict (openOf P uv.evenPart))
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + c
          + (μ.toMeasure (residual P uv n) + ν.toMeasure (residual P uv n)) := by
  have hlt' : levyProkhorovEDist ν.toMeasure μ.toMeasure < c := by
    rwa [levyProkhorovEDist_comm] at hlt
  set A₀ := ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) with hA₀
  set M := μ.toMeasure (residual P uv n) with hM
  set N := ν.toMeasure (residual P uv n) with hN
  set R := A₀ + c + (M + N) with hR
  -- the three ways the budget `R` dominates a piece of the estimate
  have h1 : A₀ ≤ R := hR ▸ le_trans le_self_add le_self_add
  have h2 : c + M ≤ R := by
    have he : A₀ + c + (M + N) = c + M + (A₀ + N) := by ring
    rw [hR, he]; exact le_self_add
  have h3 : c + N ≤ R := by
    have he : A₀ + c + (M + N) = c + N + (A₀ + M) := by ring
    rw [hR, he]; exact le_self_add
  refine levyProkhorovEDist_le_of_forall _ _ _ fun ε S hδε hεtop hS => ?_
  have hrad : ((2 : ℝ)⁻¹ ^ m) ≤ ε.toReal := by
    have h := ENNReal.toReal_mono hεtop.ne (h1.trans hδε.le)
    rwa [hA₀, ENNReal.toReal_ofReal (by positivity)] at h
  have hthick : thickening ((2 : ℝ)⁻¹ ^ m) S ⊆ thickening ε.toReal S := thickening_mono hrad S
  have hmt : MeasurableSet (thickening ε.toReal S) := isOpen_thickening.measurableSet
  simp only [Measure.restrict_apply hS, Measure.restrict_apply hmt]
  constructor
  · calc μ.toMeasure (S ∩ openOf P uv.evenPart)
        ≤ ν.toMeasure (thickening ((2 : ℝ)⁻¹ ^ m) S ∩ openOf P uv.evenPart) + c + M :=
          measure_restrict_le hdisj hlt hc hnm hS
      _ ≤ ν.toMeasure (thickening ε.toReal S ∩ openOf P uv.evenPart) + (c + M) := by
          rw [add_assoc]; gcongr
      _ ≤ ν.toMeasure (thickening ε.toReal S ∩ openOf P uv.evenPart) + ε := by
          gcongr; exact h2.trans hδε.le
  · calc ν.toMeasure (S ∩ openOf P uv.evenPart)
        ≤ μ.toMeasure (thickening ((2 : ℝ)⁻¹ ^ m) S ∩ openOf P uv.evenPart) + c + N :=
          measure_restrict_le hdisj hlt' hc hnm hS
      _ ≤ μ.toMeasure (thickening ε.toReal S ∩ openOf P uv.evenPart) + (c + N) := by
          rw [add_assoc]; gcongr
      _ ≤ μ.toMeasure (thickening ε.toReal S ∩ openOf P uv.evenPart) + ε := by
          gcongr; exact h3.trans hδε.le

/-- **The collapsed restriction bound.** With the stage choice `n = k + 1`, both residual terms
in `levyProkhorovEDist_restrict_le` reduce to the single quantity `μ (residual k)` — the only
one the continuity-open contract can drive to zero.

The choice order that makes this work runs: pick `k` from `tendsto_residual_zero` for `μ`; set
`n = k + 1`; pick `m ≥ n` large enough for the radius and LP-error budgets; transfer `ν`'s
residual back to `μ` at stage `k`. Antitonicity handles `μ`'s own residual, the two-scale
containment handles `ν`'s, and no continuity assumption on the approximant `ν` survives. -/
theorem levyProkhorovEDist_restrict_le_residual {μ ν : ProbabilityMeasure X} {uv : Baire}
    {c : ℝ≥0∞} {k m : ℕ}
    (hdisj : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart))
    (hlt : levyProkhorovEDist μ.toMeasure ν.toMeasure < c)
    (hc : c ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m)) (hkm : k + 1 ≤ m) :
    levyProkhorovEDist (μ.toMeasure.restrict (openOf P uv.evenPart))
        (ν.toMeasure.restrict (openOf P uv.evenPart))
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + 2 * c + 2 * μ.toMeasure (residual P uv k) := by
  have hlt' : levyProkhorovEDist ν.toMeasure μ.toMeasure < c := by
    rwa [levyProkhorovEDist_comm] at hlt
  have hμ : μ.toMeasure (residual P uv (k + 1)) ≤ μ.toMeasure (residual P uv k) :=
    measure_mono (antitone_residual P uv (Nat.le_succ k))
  have hν : ν.toMeasure (residual P uv (k + 1)) ≤ μ.toMeasure (residual P uv k) + c :=
    measure_residual_transfer P hlt' hc hkm
  refine (levyProkhorovEDist_restrict_le hdisj hlt hc hkm).trans ?_
  calc ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + c
        + (μ.toMeasure (residual P uv (k + 1)) + ν.toMeasure (residual P uv (k + 1)))
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + c
        + (μ.toMeasure (residual P uv k) + (μ.toMeasure (residual P uv k) + c)) := by gcongr
    _ = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + 2 * c + 2 * μ.toMeasure (residual P uv k) := by ring

/-- **The dyadic specialization.** Taking `c = ofReal (2⁻ᵐ)` makes the slack hypothesis
reflexivity, and the bound reduces to three dyadic terms plus twice the residual.

At the call site `hlt` is supplied by reading the weak approximant at coordinate `m + 1`, whose
naming bound gives `d_LP(μ, ν) ≤ 2⁻⁽ᵐ⁺¹⁾ < 2⁻ᵐ`. -/
theorem levyProkhorovEDist_restrict_le_dyadic {μ ν : ProbabilityMeasure X} {uv : Baire} {k m : ℕ}
    (hdisj : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart))
    (hlt : levyProkhorovEDist μ.toMeasure ν.toMeasure < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m))
    (hkm : k + 1 ≤ m) :
    levyProkhorovEDist (μ.toMeasure.restrict (openOf P uv.evenPart))
        (ν.toMeasure.restrict (openOf P uv.evenPart))
      ≤ 3 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + 2 * μ.toMeasure (residual P uv k) := by
  refine (levyProkhorovEDist_restrict_le_residual hdisj hlt le_rfl hkm).trans ?_
  rw [show (3 : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m)
      = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) + 2 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) by ring]

/-- Reciprocal comparison: when `b` exceeds `a` by at most `d` and `m ≤ b`, replacing `b⁻¹`
by the larger `a⁻¹` costs at most `d / β`. Proved by multiplying through by `a`, so that
truncated subtraction never appears. -/
private theorem inv_mul_le_inv_mul_add {a b d β m : ℝ≥0∞}
    (hβ0 : β ≠ 0) (hβtop : β ≠ ∞) (hβa : β ≤ a) (hatop : a ≠ ∞)
    (hb0 : b ≠ 0) (hbtop : b ≠ ∞) (hba : b ≤ a + d) (hm : m ≤ b) :
    a⁻¹ * m ≤ b⁻¹ * m + d / β := by
  have ha0 : a ≠ 0 := fun h => hβ0 (le_antisymm (h ▸ hβa) (by simp))
  have hmb : b⁻¹ * m ≤ 1 := by
    calc b⁻¹ * m ≤ b⁻¹ * b := by gcongr
      _ = 1 := ENNReal.inv_mul_cancel hb0 hbtop
  have hstep : m ≤ a * (b⁻¹ * m + d / β) := by
    calc m = b⁻¹ * m * b := by
            rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hb0 hbtop, one_mul]
      _ ≤ b⁻¹ * m * (a + d) := by gcongr
      _ = a * (b⁻¹ * m) + b⁻¹ * m * d := by ring
      _ ≤ a * (b⁻¹ * m) + a * (d / β) := by
          gcongr ?_ + ?_
          · exact le_rfl
          · calc b⁻¹ * m * d ≤ 1 * d := by gcongr
              _ = d := one_mul d
              _ = β * (d / β) := by
                  rw [ENNReal.mul_div_cancel hβ0 hβtop]
              _ ≤ a * (d / β) := by gcongr
      _ = a * (b⁻¹ * m + d / β) := by ring
  calc a⁻¹ * m ≤ a⁻¹ * (a * (b⁻¹ * m + d / β)) := by gcongr
    _ = b⁻¹ * m + d / β := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha0 hatop, one_mul]

/-- `μ` conditioned on `U`: the normalized restriction to `U`. -/
noncomputable def normalizedRestriction (μ : ProbabilityMeasure X) (U : Set X) : Measure X :=
  (μ.toMeasure U)⁻¹ • μ.toMeasure.restrict U

omit [BorelSpace X] in
/-- **Normalization is Lipschitz in Lévy–Prokhorov**, with constant controlled by any common
positive lower bound `β` on the two total masses: `LP(ρ̂, σ̂) ≤ 2 d / β` whenever `LP(ρ, σ) ≤ d`.

The constant `2` is not slack: one factor of `d / β` pays for the reciprocal mismatch
`a⁻¹` versus `b⁻¹`, the other for the Lévy–Prokhorov additive term after division by `a`.
`β ≤ 1` is genuinely required — it is what makes the auxiliary radius `ε β / 2` no larger than
`ε`, so that the thickening at the smaller radius still sits inside the one the criterion
demands. For restrictions of probability measures it is automatic. -/
theorem levyProkhorovEDist_normalize_lipschitz {ρ σ : Measure X}
    [IsFiniteMeasure ρ] [IsFiniteMeasure σ] {d β : ℝ≥0∞}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hβρ : β ≤ ρ Set.univ) (hβσ : β ≤ σ Set.univ)
    (hd : levyProkhorovEDist ρ σ ≤ d) :
    levyProkhorovEDist ((ρ Set.univ)⁻¹ • ρ) ((σ Set.univ)⁻¹ • σ) ≤ 2 * d / β := by
  set a := ρ Set.univ with ha
  set b := σ Set.univ with hb
  have hβ0' : β ≠ 0 := hβ0.ne'
  have hβtop : β ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hβ1
  have hatop : a ≠ ∞ := measure_ne_top ρ _
  have hbtop : b ≠ ∞ := measure_ne_top σ _
  have ha0 : a ≠ 0 := fun h => hβ0' (le_antisymm (h ▸ hβρ) (by simp))
  have hb0 : b ≠ 0 := fun h => hβ0' (le_antisymm (h ▸ hβσ) (by simp))
  refine levyProkhorovEDist_le_of_forall _ _ _ fun ε B hεgt hεtop hB => ?_
  set c := ε * β / 2 with hc
  -- `c` sits strictly above `d`, and below `ε`
  have hεβ : 2 * d < ε * β := by
    rw [ENNReal.div_lt_iff (Or.inl hβ0') (Or.inl hβtop)] at hεgt
    exact hεgt
  have hcd : d < c := by
    rw [hc, ENNReal.lt_div_iff_mul_lt (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    rw [mul_comm d 2]
    exact hεβ
  have hce : c ≤ ε := by
    calc c = ε * β / 2 := hc
      _ ≤ ε * 1 / 2 := by gcongr
      _ ≤ ε := by
          rw [mul_one]
          exact ENNReal.half_le_self
  have hcc : 2 * c / β = ε := by
    rw [hc, ENNReal.mul_div_cancel (two_ne_zero) (ENNReal.ofNat_ne_top),
      ENNReal.mul_div_cancel_right hβ0' hβtop]
  have hlp : levyProkhorovEDist ρ σ < c := lt_of_le_of_lt hd hcd
  have hlp' : levyProkhorovEDist σ ρ < c := by rwa [levyProkhorovEDist_comm] at hlp
  -- the two total-mass comparisons
  have hab : a ≤ b + c :=
    (left_measure_le_of_levyProkhorovEDist_lt hlp MeasurableSet.univ).trans
      (add_le_add (measure_mono (Set.subset_univ _)) le_rfl)
  have hba : b ≤ a + c :=
    (left_measure_le_of_levyProkhorovEDist_lt hlp' MeasurableSet.univ).trans
      (add_le_add (measure_mono (Set.subset_univ _)) le_rfl)
  have hthick : thickening c.toReal B ⊆ thickening ε.toReal B :=
    thickening_mono (ENNReal.toReal_mono hεtop.ne hce) B
  have hinv_a : a⁻¹ ≤ β⁻¹ := ENNReal.inv_le_inv.mpr hβρ
  have hinv_b : b⁻¹ ≤ β⁻¹ := ENNReal.inv_le_inv.mpr hβσ
  simp only [Measure.smul_apply, smul_eq_mul]
  constructor
  · have hmain := left_measure_le_of_levyProkhorovEDist_lt hlp hB
    calc a⁻¹ * ρ B ≤ a⁻¹ * (σ (thickening c.toReal B) + c) := by gcongr
      _ = a⁻¹ * σ (thickening c.toReal B) + a⁻¹ * c := by ring
      _ ≤ (b⁻¹ * σ (thickening c.toReal B) + c / β) + c / β := by
          gcongr ?_ + ?_
          · exact inv_mul_le_inv_mul_add hβ0' hβtop hβρ hatop hb0 hbtop hba
              (measure_mono (Set.subset_univ _))
          · rw [div_eq_mul_inv, mul_comm c]
            gcongr
      _ ≤ b⁻¹ * σ (thickening ε.toReal B) + 2 * c / β := by
          rw [add_assoc, ENNReal.div_add_div_same, ← two_mul]
          gcongr
      _ = b⁻¹ * σ (thickening ε.toReal B) + ε := by rw [hcc]
  · have hmain := left_measure_le_of_levyProkhorovEDist_lt hlp' hB
    calc b⁻¹ * σ B ≤ b⁻¹ * (ρ (thickening c.toReal B) + c) := by gcongr
      _ = b⁻¹ * ρ (thickening c.toReal B) + b⁻¹ * c := by ring
      _ ≤ (a⁻¹ * ρ (thickening c.toReal B) + c / β) + c / β := by
          gcongr ?_ + ?_
          · exact inv_mul_le_inv_mul_add hβ0' hβtop hβσ hbtop ha0 hatop hab
              (measure_mono (Set.subset_univ _))
          · rw [div_eq_mul_inv, mul_comm c]
            gcongr
      _ ≤ a⁻¹ * ρ (thickening ε.toReal B) + 2 * c / β := by
          rw [add_assoc, ENNReal.div_add_div_same, ← two_mul]
          gcongr
      _ = a⁻¹ * ρ (thickening ε.toReal B) + ε := by rw [hcc]

/-- **The transfer, in the direction the realizer needs.** `le_atomic_of_weakName` sends `μ`'s
mass on
`innerApprox u n` into the approximant's at `n + 1`; this is the mirror image, sending the
approximant's into `μ`'s. Same thickening room, same strict coupling `n < m`. -/
theorem atomic_le_measure_succ {μ : ProbabilityMeasure X} {p u : Baire}
    (hp : WeakMeasureNames P p μ) {m n : ℕ} (hnm : n < m) :
    (atomic P (p (m + 1))).toMeasure (innerApprox P u n)
      ≤ μ.toMeasure (innerApprox P u (n + 1)) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) := by
  have hfin : levyProkhorovEDist μ.toMeasure (atomic P (p (m + 1))).toMeasure ≠ ⊤ := by simp
  have hle : levyProkhorovEDist (atomic P (p (m + 1))).toMeasure μ.toMeasure
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (m + 1)) := by
    rw [levyProkhorovEDist_comm, ← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hp (m + 1))
  have hstrict : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (m + 1)) < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) := by
    refine ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr ?_
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
    rw [pow_succ]
    linarith
  refine le_measure_of_thickening_subset (lt_of_le_of_lt hle hstrict) le_rfl
    ENNReal.ofReal_ne_top (measurableSet_innerApprox u n) ?_
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact thickening_innerApprox_subset_succ u hnm

/-- **The complement track pays for the residual.** Two certified lower bounds at level `ℓ`,
transferred to `μ` at level `ℓ + 1`, leave the residual no more room than the gap plus two
dyadic errors. This is where `δ` earns its double role. -/
theorem measure_residual_le_of_certified {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (hcont : ContinuityOpenNames P μ uv)
    {ℓ s : ℕ} (hls : ℓ < s) {cU cV δ : ℝ≥0∞}
    (hcU : cU ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P uv.evenPart ℓ))
    (hcV : cV ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P uv.oddPart ℓ))
    (hgap : 1 ≤ cU + cV + δ) :
    μ.toMeasure (residual P uv (ℓ + 1))
      ≤ δ + 2 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) := by
  set q := ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) with hq
  set iu := innerApprox P uv.evenPart (ℓ + 1) with hiu
  set iv := innerApprox P uv.oddPart (ℓ + 1) with hiv
  -- the two inner approximations are disjoint, being inside the disjoint tracks
  have hsubU : iu ⊆ openOf P uv.evenPart := by
    rw [hiu, ← iUnion_innerApprox P uv.evenPart]; exact Set.subset_iUnion _ (ℓ + 1)
  have hsubV : iv ⊆ openOf P uv.oddPart := by
    rw [hiv, ← iUnion_innerApprox P uv.oddPart]; exact Set.subset_iUnion _ (ℓ + 1)
  have hdisj : Disjoint iu iv := hcont.disjoint.mono hsubU hsubV
  have hunion : μ.toMeasure (iu ∪ iv) = μ.toMeasure iu + μ.toMeasure iv :=
    measure_union hdisj (measurableSet_innerApprox _ _)
  -- transfer both certified bounds to `μ` one level up
  have hU := le_trans hcU (atomic_le_measure_succ (u := uv.evenPart) hp hls)
  have hV := le_trans hcV (atomic_le_measure_succ (u := uv.oddPart) hp hls)
  have hcc : cU + cV ≤ μ.toMeasure (iu ∪ iv) + 2 * q := by
    rw [hunion]
    calc cU + cV ≤ (μ.toMeasure iu + q) + (μ.toMeasure iv + q) := add_le_add hU hV
      _ = μ.toMeasure iu + μ.toMeasure iv + 2 * q := by ring
  -- the residual is exactly the complement of that union
  have hcompl : μ.toMeasure (residual P uv (ℓ + 1)) + μ.toMeasure (iu ∪ iv) = 1 := by
    rw [residual, ← hiu, ← hiv, add_comm]
    rw [← measure_univ (μ := μ.toMeasure)]
    exact measure_add_measure_compl
      ((measurableSet_innerApprox _ _).union (measurableSet_innerApprox _ _))
  have hkey : μ.toMeasure (residual P uv (ℓ + 1)) + μ.toMeasure (iu ∪ iv)
      ≤ (δ + 2 * q) + μ.toMeasure (iu ∪ iv) := by
    rw [hcompl]
    calc (1 : ℝ≥0∞) ≤ cU + cV + δ := hgap
      _ ≤ (μ.toMeasure (iu ∪ iv) + 2 * q) + δ := add_le_add hcc le_rfl
      _ = (δ + 2 * q) + μ.toMeasure (iu ∪ iv) := by ring
  exact (ENNReal.add_le_add_iff_right (measure_ne_top _ _)).mp hkey

/-- **The explicit unnormalized budget.** `7q + 2δ`, with `q = 2⁻ˢ`: three dyadic terms from the
collapsed restriction estimate and twice the residual bound above. The index coupling is
`ℓ + 2 ≤ s` — the residual is read at `ℓ + 1`, and the estimate needs one further step. -/
theorem explicit_restrict_budget {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (hcont : ContinuityOpenNames P μ uv)
    {ℓ s : ℕ} (hls : ℓ + 2 ≤ s) {cU cV δ : ℝ≥0∞}
    (hcU : cU ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P uv.evenPart ℓ))
    (hcV : cV ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P uv.oddPart ℓ))
    (hgap : 1 ≤ cU + cV + δ) :
    levyProkhorovEDist (μ.toMeasure.restrict (openOf P uv.evenPart))
        ((atomic P (p (s + 1))).toMeasure.restrict (openOf P uv.evenPart))
      ≤ 7 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) + 2 * δ := by
  set q := ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) with hq
  have hlt : levyProkhorovEDist μ.toMeasure (atomic P (p (s + 1))).toMeasure < q := by
    have hfin : levyProkhorovEDist μ.toMeasure (atomic P (p (s + 1))).toMeasure ≠ ⊤ := by simp
    have hle : levyProkhorovEDist μ.toMeasure (atomic P (p (s + 1))).toMeasure
        ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (s + 1)) := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (hp (s + 1))
    refine lt_of_le_of_lt hle ?_
    rw [hq]
    refine ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr ?_
    have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ s := by positivity
    rw [pow_succ]
    linarith
  have hres := measure_residual_le_of_certified hp hcont (by omega : ℓ < s) hcU hcV hgap
  refine (levyProkhorovEDist_restrict_le_dyadic hcont.disjoint hlt (by omega)).trans ?_
  calc 3 * q + 2 * μ.toMeasure (residual P uv (ℓ + 1))
      ≤ 3 * q + 2 * (δ + 2 * q) := by gcongr
    _ = 7 * q + 2 * δ := by ring

/-- **The explicit normalized budget**, i.e. the `d₀` a success predicate may store: the
unnormalized bound divided by the mass floor, with the factor two the two-sided normalization
costs. Code-free; the realizer supplies the three floors. -/
theorem explicit_normalized_budget {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (hcont : ContinuityOpenNames P μ uv)
    {ℓ s : ℕ} (hls : ℓ + 2 ≤ s) {cU cV δ β₀ : ℝ≥0∞}
    (hcU : cU ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P uv.evenPart ℓ))
    (hcV : cV ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P uv.oddPart ℓ))
    (hgap : 1 ≤ cU + cV + δ)
    (hβ0 : 0 < β₀) (hβ1 : β₀ ≤ 1)
    (hβμ : β₀ ≤ μ.toMeasure.restrict (openOf P uv.evenPart) Set.univ)
    (hβa : β₀ ≤ (atomic P (p (s + 1))).toMeasure.restrict (openOf P uv.evenPart) Set.univ) :
    levyProkhorovEDist
        (((atomic P (p (s + 1))).toMeasure.restrict (openOf P uv.evenPart) Set.univ)⁻¹
          • (atomic P (p (s + 1))).toMeasure.restrict (openOf P uv.evenPart))
        (normalizedRestriction μ (openOf P uv.evenPart))
      ≤ 2 * (7 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) + 2 * δ) / β₀ := by
  have hd := explicit_restrict_budget hp hcont hls hcU hcV hgap
  have hmain := levyProkhorovEDist_normalize_lipschitz hβ0 hβ1 hβμ hβa hd
  rw [normalizedRestriction, ← Measure.restrict_univ (μ := μ.toMeasure)]
  rw [levyProkhorovEDist_comm]
  simpa [Measure.restrict_univ] using hmain

section RestrictionWitness
/-- The proof-side half of a restriction witness. Open-ended: later fields append into
`rstRest`, leaving every accessor below unchanged. -/
def rstProof (w : ℕ) : ℕ := w.unpair.1

/-- The emitted atomic index of a restriction witness. -/
def rstAtomic (w : ℕ) : ℕ := w.unpair.2.unpair.1

/-- The emitted mask of a restriction witness. -/
def rstMask (w : ℕ) : ℕ := w.unpair.2.unpair.2

/-- The inner-approximation level recorded by a restriction witness. -/
def rstLevel (w : ℕ) : ℕ := (rstProof w).unpair.1

/-- The weak-name stage recorded by a restriction witness. -/
def rstStage (w : ℕ) : ℕ := (rstProof w).unpair.2.unpair.1

/-- The mask fuel recorded by a restriction witness. -/
def rstFuel (w : ℕ) : ℕ := (rstProof w).unpair.2.unpair.2.unpair.1

/-- The reserved tail of the proof-side half: where the analytic argument's later fields go. -/
def rstRest (w : ℕ) : ℕ := (rstProof w).unpair.2.unpair.2.unpair.2

/-- The restriction-witness packer. -/
def packRestrictWit (level stage fuel rest atomicIndex mask : ℕ) : ℕ :=
  Nat.pair (Nat.pair level (Nat.pair stage (Nat.pair fuel rest)))
    (Nat.pair atomicIndex mask)

@[simp] theorem rstLevel_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstLevel (packRestrictWit level stage fuel rest a mk) = level := by
  simp [rstLevel, rstProof, packRestrictWit]

@[simp] theorem rstStage_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstStage (packRestrictWit level stage fuel rest a mk) = stage := by
  simp [rstStage, rstProof, packRestrictWit]

@[simp] theorem rstFuel_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstFuel (packRestrictWit level stage fuel rest a mk) = fuel := by
  simp [rstFuel, rstProof, packRestrictWit]

@[simp] theorem rstRest_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstRest (packRestrictWit level stage fuel rest a mk) = rest := by
  simp [rstRest, rstProof, packRestrictWit]

@[simp] theorem rstAtomic_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstAtomic (packRestrictWit level stage fuel rest a mk) = a := by
  simp [rstAtomic, packRestrictWit]

@[simp] theorem rstMask_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstMask (packRestrictWit level stage fuel rest a mk) = mk := by
  simp [rstMask, packRestrictWit]

theorem primrec_rstAtomic : Primrec rstAtomic :=
  (Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)

theorem primrec_rstMask : Primrec rstMask :=
  (Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)

theorem primrec_rstLevel : Primrec rstLevel :=
  (Primrec.fst.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)

theorem primrec_rstStage : Primrec rstStage :=
  (Primrec.fst.comp Primrec.unpair).comp
    ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair))

theorem primrec_rstFuel : Primrec rstFuel :=
  (Primrec.fst.comp Primrec.unpair).comp
    ((Primrec.snd.comp Primrec.unpair).comp
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)))

/-- **The consistency clauses.** They are what make the emitted tail redundant *information* but
indispensable *access*: the atomic index must be the weak name's own stage entry, and the mask
must be the certified mask at the recorded level and fuel. Checking them in the search predicate
is what lets the postprocessor use the tail without re-reading the oracle. -/
def RestrictWitConsistent (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p u : Baire) (w : ℕ) : Prop :=
  rstAtomic w = p (rstStage w + 1) ∧
    rstMask w = mac (atoms (rstAtomic w)) (streamTake u (rstLevel w)) (rstLevel w) (rstFuel w)

/-- **The oracle-free postprocessor**: a successful witness is turned into the emitted atomic
index by the package's own emitter, reading nothing else. -/
def restrictionOut (emit : ℕ → ℕ → ℕ) (w : ℕ) : ℕ := emit (rstAtomic w) (rstMask w)

theorem primrec_restrictionOut {emit : ℕ → ℕ → ℕ} (hemit : Primrec₂ emit) :
    Primrec (restrictionOut emit) := by
  have h := hemit.comp primrec_rstAtomic primrec_rstMask
  exact h.of_eq fun _ => rfl

/-- The `β₀` field, given its own accessor so that further budget fields may still be appended
into `(rstRest w).unpair.2` without disturbing any consumer. -/
def rstBeta (w : ℕ) : ℕ := (rstRest w).unpair.1

@[simp] theorem rstBeta_packRestrictWit (level stage fuel rest a mk : ℕ) :
    rstBeta (packRestrictWit level stage fuel rest a mk) = rest.unpair.1 := by
  simp [rstBeta]

theorem primrec_rstRest : Primrec rstRest :=
  (Primrec.snd.comp Primrec.unpair).comp
    ((Primrec.snd.comp Primrec.unpair).comp
      ((Primrec.snd.comp Primrec.unpair).comp (Primrec.fst.comp Primrec.unpair)))

theorem primrec_rstBeta : Primrec rstBeta :=
  (Primrec.fst.comp Primrec.unpair).comp primrec_rstRest

/-- **The arithmetic quarter step**, one half of the mass ledger. `β₀ + q ≤ a` gives the quarter
floor `β₀ / 4 ≤ a` outright, so the retained-mass clause of a success predicate is *derived*
rather than independently checked and cannot be chosen inconsistently with `β₀`. The ledger's
other half is `floor_le_measure_of_success`, which is where the one-way `β₀ → β₁` dependency
actually lives. -/
theorem quarter_le_of_floor {β₀ q a : ℝ≥0∞} (h : β₀ + q ≤ a) : β₀ / 4 ≤ a := by
  refine le_trans (le_trans ?_ le_self_add) h
  calc β₀ / 4 ≤ β₀ / 1 := ENNReal.div_le_div_left (by norm_num) β₀
    _ = β₀ := div_one β₀

/-- **The mass ledger proper.** The single coded comparison `β₀ + q ≤ acc`, together with
consistency, `ℓ ≤ s` and accumulator soundness, certifies that `β₀` really is a floor on
`μ U` — with `q = 2⁻ˢ` paying for the weak name's own error and nothing else. This is the
one-way step: `β₀` is established against `μ` here, and only afterwards may `β₁ = β₀ / 4` be
read off by `quarter_le_of_floor`. Note every deficit refers to the same `m = rstAtomic w`,
`A = innerApprox P u (rstLevel w)` and `mask = rstMask w` that the emitter uses. -/
theorem floor_le_measure_of_success
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (haccsound : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    {μ : ProbabilityMeasure X} {p uv : Baire} (hp : WeakMeasureNames P p μ) {w : ℕ}
    (hcons : RestrictWitConsistent atoms mac p uv.evenPart w)
    (hls : rstLevel w ≤ rstStage w)
    (hfloor : ENNReal.ofReal ((ratOfCode (rstBeta w) : ℚ) : ℝ)
          + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ rstStage w)
        ≤ ENNReal.ofReal ((ratOfCode (acc (rstAtomic w) (rstMask w)) : ℚ) : ℝ)) :
    ENNReal.ofReal ((ratOfCode (rstBeta w) : ℚ) : ℝ)
      ≤ μ.toMeasure (openOf P uv.evenPart) := by
  obtain ⟨hm, hmask⟩ := hcons
  set u := uv.evenPart with hu
  set A := innerApprox P u (rstLevel w) with hA
  -- the mask is certified at exactly the recorded level, so its bits land in `A`
  have hbits : ∀ i, i < (atoms (rstAtomic w)).length → (rstMask w).testBit i = true →
      P.dense ((atoms (rstAtomic w)).getD i (0, 0)).1 ∈ A := by
    intro i hi hb
    rw [hmask] at hb
    exact hmacsound _ u _ _ i hi hb
  -- accumulator soundness at that same mask and set
  have h1 : ENNReal.ofReal ((ratOfCode (acc (rstAtomic w) (rstMask w)) : ℚ) : ℝ)
      ≤ (atomic P (rstAtomic w)).toMeasure A :=
    haccsound _ _ A (measurableSet_innerApprox u (rstLevel w)) hbits
  -- the weak name's own bound, at the coupled indices `ℓ ≤ s`
  have h2 : (atomic P (rstAtomic w)).toMeasure A
      ≤ μ.toMeasure (openOf P u) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ rstStage w) := by
    rw [hm]; exact atomic_le_of_weakName hp hls
  have hchain : ENNReal.ofReal ((ratOfCode (rstBeta w) : ℚ) : ℝ)
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ rstStage w)
      ≤ μ.toMeasure (openOf P u) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ rstStage w) :=
    le_trans hfloor (le_trans h1 h2)
  exact ENNReal.add_le_add_iff_right (by simp)|>.mp hchain

/-- **The metric ledger, abstractly.** The emitted normalized submeasure is compared to the
target in two hops: the submeasure bridge pays `δ / β₁`, and the `μ`-versus-atomic normalized
restriction error pays `d₀`. Nothing here knows what `δ` or `d₀` are made of. -/
theorem lp_normalized_triangle {μ : ProbabilityMeasure X} {U : Set X}
    {ρ σ : Measure X} [IsFiniteMeasure σ] {d₀ δ β₁ : ℝ≥0∞}
    (hρσ : ρ ≤ σ) (hβ₁ : 0 < β₁) (hmass : β₁ ≤ ρ Set.univ)
    (hδ : σ Set.univ ≤ ρ Set.univ + δ)
    (hd₀ : levyProkhorovEDist ((σ Set.univ)⁻¹ • σ) (normalizedRestriction μ U) ≤ d₀) :
    levyProkhorovEDist ((ρ Set.univ)⁻¹ • ρ) (normalizedRestriction μ U) ≤ δ / β₁ + d₀ :=
  calc levyProkhorovEDist ((ρ Set.univ)⁻¹ • ρ) (normalizedRestriction μ U)
      ≤ levyProkhorovEDist ((ρ Set.univ)⁻¹ • ρ) ((σ Set.univ)⁻¹ • σ)
        + levyProkhorovEDist ((σ Set.univ)⁻¹ • σ) (normalizedRestriction μ U) :=
        levyProkhorovEDist_triangle _ _ _
    _ ≤ δ / β₁ + d₀ :=
        add_le_add (levyProkhorovEDist_normalized_le hρσ hβ₁ hmass hδ) hd₀

/-- **The exact final inequality.** This is the shape a success predicate's last clause must
certify: the two ledgers, already combined, fit inside the requested dyadic precision. Making
`j` occur here is what stops one witness from succeeding at every precision. -/
theorem lp_normalized_le_dyadic {μ : ProbabilityMeasure X} {U : Set X}
    {ρ σ : Measure X} [IsFiniteMeasure σ] {d₀ δ β₁ : ℝ≥0∞} {j : ℕ}
    (hρσ : ρ ≤ σ) (hβ₁ : 0 < β₁) (hmass : β₁ ≤ ρ Set.univ)
    (hδ : σ Set.univ ≤ ρ Set.univ + δ)
    (hd₀ : levyProkhorovEDist ((σ Set.univ)⁻¹ • σ) (normalizedRestriction μ U) ≤ d₀)
    (hbudget : δ / β₁ + d₀ ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j)) :
    levyProkhorovEDist ((ρ Set.univ)⁻¹ • ρ) (normalizedRestriction μ U)
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j) :=
  le_trans (lp_normalized_triangle hρσ hβ₁ hmass hδ hd₀) hbudget

/-- **The index choice.** The realizer needs the coupling `ℓ + 2 ≤ s` with `ℓ = n + 1`, i.e.
`n + 3 ≤ s`, and it must be able to place `n` above a floor already fixed by the positive-mass
choice: an arbitrary positive target `t` and a floor `N` on the level.

Taking `ℓ` as the successor of a chosen `n` is what avoids having to recover an earlier inner
approximation from an arbitrary `ℓ`: the lower-bound transfer `le_atomic_of_weakName` steps the
level up by one, so the predecessor is the natural thing to choose. -/
private theorem exists_indices_gap_floor {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ∃ n s : ℕ, N ≤ n ∧ n + 3 ≤ s ∧
      (1 : ℝ) - ((atomic P (p (s + 1))).toMeasure (innerApprox P uv.oddPart (n + 1))).toReal
          - ((atomic P (p (s + 1))).toMeasure (innerApprox P uv.evenPart (n + 1))).toReal
          + 2 * (2 : ℝ)⁻¹ ^ s
        < t := by
  -- the level: track convergence, and the floor, at once
  obtain ⟨n, hn, hnN⟩ :=
    (((tendsto_gap h).eventually
        (gt_mem_nhds (show (0 : ℝ) < t / 2 by linarith))).and
      (Filter.eventually_ge_atTop N)).exists
  -- the stage: clear the level by three, and leave room for four copies of the LP error
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < t / 8 by linarith)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨n, max k (n + 3), hnN, le_max_right _ _, ?_⟩
  set s := max k (n + 3) with hs
  have hsk : (2 : ℝ)⁻¹ ^ s ≤ (2 : ℝ)⁻¹ ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have hspow : (2 : ℝ)⁻¹ ^ s < t / 8 := lt_of_le_of_lt hsk hk
  have hns : n < s := lt_of_lt_of_le (by omega) (le_max_right _ _)
  have key : ∀ v : Baire, μ.toMeasure (innerApprox P v n)
      ≤ (atomic P (p (s + 1))).toMeasure (innerApprox P v (n + 1))
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) := fun v => le_atomic_of_weakName hp hns
  have toRealKey : ∀ v : Baire, (μ.toMeasure (innerApprox P v n)).toReal
      ≤ ((atomic P (p (s + 1))).toMeasure (innerApprox P v (n + 1))).toReal
        + (2 : ℝ)⁻¹ ^ s := by
    intro v
    have hfin : (atomic P (p (s + 1))).toMeasure (innerApprox P v (n + 1))
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
    have hR := ENNReal.toReal_mono hfin (key v)
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ s)] at hR
  have hU := toRealKey uv.evenPart
  have hV := toRealKey uv.oddPart
  rw [lowerU, lowerV] at hn
  linarith

/-- The odd-track mask, derived at the same atomic index, level and fuel as the emitted one. -/
def rstOddMask (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (uv : Baire) (w : ℕ) : ℕ :=
  mac (atoms (rstAtomic w)) (streamTake uv.oddPart (rstLevel w)) (rstLevel w) (rstFuel w)

/-- The certified mass retained on the even track: the emitted mask's accumulator. -/
def rstMassU (acc : ℕ → ℕ → RatCode) (w : ℕ) : ℚ :=
  ratOfCode (acc (rstAtomic w) (rstMask w))

/-- The certified mass on the odd track, at the same atomic index, level and fuel. -/
def rstMassV (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (uv : Baire) (w : ℕ) : ℚ :=
  ratOfCode (acc (rstAtomic w) (rstOddMask atoms mac uv w))

/-- The stage dyadic `q = 2⁻ˢ`. -/
def rstQ (w : ℕ) : ℚ := (2 : ℚ)⁻¹ ^ rstStage w

/-- The single gap `δ = 1 - (cU + cV)`, covering inner-approximation shortfall and mask
omission together. -/
def rstGap (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (uv : Baire) (w : ℕ) : ℚ :=
  1 - (rstMassU acc w + rstMassV atoms acc mac uv w)

/-- The searched dyadic floor `β₀`, as a rational. -/
def rstBetaQ (w : ℕ) : ℚ := ratOfCode (rstBeta w)

/-- **The success predicate.** Six clauses; `j` occurs in the last, so no witness can
succeed at every precision. -/
def RestrictionSuccess (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (j w : ℕ) : Prop :=
  RestrictWitConsistent atoms mac p uv.evenPart w ∧
  rstLevel w + 2 ≤ rstStage w ∧
  0 < rstBetaQ w ∧
  rstMassU acc w + rstMassV atoms acc mac uv w ≤ 1 ∧
  rstBetaQ w + rstQ w ≤ rstMassU acc w ∧
  14 * rstQ w + 8 * rstGap atoms acc mac uv w ≤ rstBetaQ w * (2 : ℚ)⁻¹ ^ j

/-- **The transport, isolated.** Rational algebra happens in `budget_clause_iff`; measure
semantics happens in `lp_normalized_le_dyadic`; this is the only place `ENNReal.ofReal` crosses
between them. Everything on the left is nonnegative, so no truncated subtraction arises. -/
private theorem ofReal_budget_transport {β q δ e : ℚ}
    (hβ : 0 < β) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (h : 14 * q + 8 * δ ≤ β * e) :
    ENNReal.ofReal ((δ : ℝ)) / (ENNReal.ofReal ((β : ℝ)) / 4)
        + 2 * (7 * ENNReal.ofReal ((q : ℝ)) + 2 * ENNReal.ofReal ((δ : ℝ)))
          / ENNReal.ofReal ((β : ℝ))
      ≤ ENNReal.ofReal ((e : ℝ)) := by
  have hβR : (0 : ℝ) < (β : ℝ) := by exact_mod_cast hβ
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  -- the rational inequality, in ℝ and already in divided form
  have hreal : (δ : ℝ) / ((β : ℝ) / 4)
      + 2 * (7 * (q : ℝ) + 2 * (δ : ℝ)) / (β : ℝ) ≤ (e : ℝ) := by
    have hle : 14 * (q : ℝ) + 8 * (δ : ℝ) ≤ (β : ℝ) * (e : ℝ) := by exact_mod_cast h
    have hid : (δ : ℝ) / ((β : ℝ) / 4) + 2 * (7 * (q : ℝ) + 2 * (δ : ℝ)) / (β : ℝ)
        = (14 * (q : ℝ) + 8 * (δ : ℝ)) / (β : ℝ) := by
      field_simp; ring
    rw [hid, div_le_iff₀ hβR]
    calc 14 * (q : ℝ) + 8 * (δ : ℝ) ≤ (β : ℝ) * (e : ℝ) := hle
      _ = (e : ℝ) * (β : ℝ) := mul_comm _ _
  -- both summands are nonnegative reals, so `ofReal` is additive and multiplicative here
  refine le_trans (le_of_eq ?_) (ENNReal.ofReal_le_ofReal hreal)
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by simp,
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by simp,
    show (7 : ℝ≥0∞) = ENNReal.ofReal (7 : ℝ) by simp,
    ← ENNReal.ofReal_div_of_pos (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 7),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_div_of_pos hβR,
    ← ENNReal.ofReal_div_of_pos (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **The certified bounds, proved once.** The even track needs the consistency rewrite, the odd
track needs only the structural fact that `rstOddMask` is `mac` at the same `m`, `ℓ` and fuel.
Both `restriction_bridge` and `explicit_normalized_budget` consume these, so neither argument is
made twice. -/
private theorem restriction_certified_bounds
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (haccsound : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    {uv p : Baire} {w : ℕ}
    (hcons : RestrictWitConsistent atoms mac p uv.evenPart w) :
    (∀ i, i < (atoms (rstAtomic w)).length → (rstMask w).testBit i = true →
        P.dense ((atoms (rstAtomic w)).getD i (0, 0)).1
          ∈ innerApprox P uv.evenPart (rstLevel w)) ∧
      ENNReal.ofReal ((rstMassU acc w : ℚ) : ℝ)
        ≤ (atomic P (rstAtomic w)).toMeasure (innerApprox P uv.evenPart (rstLevel w)) ∧
      ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
        ≤ (atomic P (rstAtomic w)).toMeasure (innerApprox P uv.oddPart (rstLevel w)) := by
  obtain ⟨_, hmask⟩ := hcons
  have hbitsU : ∀ i, i < (atoms (rstAtomic w)).length → (rstMask w).testBit i = true →
      P.dense ((atoms (rstAtomic w)).getD i (0, 0)).1
        ∈ innerApprox P uv.evenPart (rstLevel w) := by
    intro i hi hb
    rw [hmask] at hb
    exact hmacsound _ uv.evenPart _ _ i hi hb
  have hbitsV : ∀ i, i < (atoms (rstAtomic w)).length →
      (rstOddMask atoms mac uv w).testBit i = true →
      P.dense ((atoms (rstAtomic w)).getD i (0, 0)).1
        ∈ innerApprox P uv.oddPart (rstLevel w) := by
    intro i hi hb
    exact hmacsound _ uv.oddPart _ _ i hi hb
  exact ⟨hbitsU,
    haccsound _ _ _ (measurableSet_innerApprox _ _) hbitsU,
    haccsound _ _ _ (measurableSet_innerApprox _ _) hbitsV⟩

/-- **The bridge to the emitter's two obligations.** The four ledger lemmas do not supply
`hρσ` or `hδ` for `lp_normalized_le_dyadic`; this does, and it is where `A ⊆ U` and the
odd-track guard `cU + cV ≤ 1` are spent.

The deficit bound is proved additively — `atomicₘ(U) + cV ≤ 1 = cU + cV + δ`, then cancel
`cV` — so `ENNReal` truncated subtraction never appears. -/
theorem restriction_bridge
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {emit : ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (hemit : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ∃ ρ : Measure X,
        ρ ≤ (atomic P m).toMeasure.restrict A ∧
        ρ Set.univ = ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ∧
        (ρ Set.univ ≠ 0 →
          (atomic P (emit m mask)).toMeasure = (ρ Set.univ)⁻¹ • ρ))
    {uv : Baire} {w : ℕ}
    (hbitsU : ∀ i, i < (atoms (rstAtomic w)).length → (rstMask w).testBit i = true →
      P.dense ((atoms (rstAtomic w)).getD i (0, 0)).1
        ∈ innerApprox P uv.evenPart (rstLevel w))
    (hmassV : ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
      ≤ (atomic P (rstAtomic w)).toMeasure (innerApprox P uv.oddPart (rstLevel w)))
    (hdisj : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart))
    (hguard : rstMassU acc w + rstMassV atoms acc mac uv w ≤ 1) :
    ∃ ρ : Measure X,
      ρ ≤ (atomic P (rstAtomic w)).toMeasure.restrict (openOf P uv.evenPart) ∧
      ρ Set.univ = ENNReal.ofReal ((rstMassU acc w : ℚ) : ℝ) ∧
      (atomic P (rstAtomic w)).toMeasure.restrict (openOf P uv.evenPart) Set.univ
        ≤ ρ Set.univ + ENNReal.ofReal ((rstGap atoms acc mac uv w : ℚ) : ℝ) ∧
      (ρ Set.univ ≠ 0 →
        (atomic P (emit (rstAtomic w) (rstMask w))).toMeasure = (ρ Set.univ)⁻¹ • ρ) := by
  set m := rstAtomic w with hmdef
  set ℓ := rstLevel w with hldef
  set U := openOf P uv.evenPart with hU
  set V := openOf P uv.oddPart with hV
  set A := innerApprox P uv.evenPart ℓ with hA
  set B := innerApprox P uv.oddPart ℓ with hB
  have hAU : A ⊆ U := by
    rw [hA, hU, ← iUnion_innerApprox P uv.evenPart]; exact Set.subset_iUnion _ ℓ
  have hBV : B ⊆ V := by
    rw [hB, hV, ← iUnion_innerApprox P uv.oddPart]; exact Set.subset_iUnion _ ℓ
  obtain ⟨ρ, hρle, hρmass, hρemit⟩ :=
    hemit m (rstMask w) A (measurableSet_innerApprox _ _) hbitsU
  refine ⟨ρ, le_trans hρle (Measure.restrict_mono hAU le_rfl), hρmass, ?_, hρemit⟩
  -- the odd track's certified mass really sits in `V`
  have hcV : ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
      ≤ (atomic P m).toMeasure V := le_trans hmassV (measure_mono hBV)
  -- the two tracks together carry at most the whole mass
  have htracks : (atomic P m).toMeasure U + (atomic P m).toMeasure V ≤ 1 := by
    rw [← measure_union hdisj (isOpen_openOf P _).measurableSet]
    simpa using measure_mono (μ := (atomic P m).toMeasure) (Set.subset_univ (U ∪ V))
  -- `1` splits additively, because all three rationals are nonnegative
  have hU0 : (0 : ℝ) ≤ ((rstMassU acc w : ℚ) : ℝ) := hnonneg _ _
  have hV0 : (0 : ℝ) ≤ ((rstMassV atoms acc mac uv w : ℚ) : ℝ) := hnonneg _ _
  have hG0 : (0 : ℝ) ≤ ((rstGap atoms acc mac uv w : ℚ) : ℝ) := by
    have : (0 : ℚ) ≤ rstGap atoms acc mac uv w := by
      rw [rstGap]; linarith [hguard]
    exact_mod_cast this
  have hsplit : (1 : ℝ≥0∞)
      = ENNReal.ofReal ((rstMassU acc w : ℚ) : ℝ)
        + ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
        + ENNReal.ofReal ((rstGap atoms acc mac uv w : ℚ) : ℝ) := by
    rw [← ENNReal.ofReal_add hU0 hV0, ← ENNReal.ofReal_add (by positivity) hG0]
    rw [show ((rstMassU acc w : ℚ) : ℝ) + ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
          + ((rstGap atoms acc mac uv w : ℚ) : ℝ) = 1 by
        push_cast [rstGap]; ring]
    simp
  -- cancel the odd track additively
  have hkey : (atomic P m).toMeasure U
        + ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
      ≤ (ENNReal.ofReal ((rstMassU acc w : ℚ) : ℝ)
          + ENNReal.ofReal ((rstGap atoms acc mac uv w : ℚ) : ℝ))
        + ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ) := by
    calc (atomic P m).toMeasure U
          + ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
        ≤ (atomic P m).toMeasure U + (atomic P m).toMeasure V := add_le_add le_rfl hcV
      _ ≤ 1 := htracks
      _ = _ := by rw [hsplit]; ring
  rw [Measure.restrict_apply_univ, hρmass]
  exact (ENNReal.add_le_add_iff_right (by simp)).mp hkey

/-- **Soundness.** A successful witness names the normalized restriction to within `2⁻ʲ`.

The emitter rewrite is deliberately last: everything before it is stated about the normalized
retained submeasure, and `hρemit`'s `ρ univ ≠ 0` premise is discharged from the mass ledger
(`0 < β₁ ≤ ρ univ`) rather than assumed. -/
theorem restrictionSuccess_sound
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {emit : ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (haccsound : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    (hemit : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ∃ ρ : Measure X,
        ρ ≤ (atomic P m).toMeasure.restrict A ∧
        ρ Set.univ = ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ∧
        (ρ Set.univ ≠ 0 →
          (atomic P (emit m mask)).toMeasure = (ρ Set.univ)⁻¹ • ρ))
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    {μ : ProbabilityMeasure X} {p uv : Baire} {j w : ℕ}
    (hp : WeakMeasureNames P p μ) (hcont : ContinuityOpenNames P μ uv)
    (hsucc : RestrictionSuccess atoms acc mac p uv j w) :
    levyProkhorovEDist (atomic P (restrictionOut emit w)).toMeasure
        (normalizedRestriction μ (openOf P uv.evenPart))
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j) := by
  obtain ⟨hcons, hls, hβpos, hguard, hfloor, hbudget⟩ := hsucc
  have hm : rstAtomic w = p (rstStage w + 1) := hcons.1
  -- coded quantities, and their signs
  have hβR : (0 : ℝ) < ((rstBetaQ w : ℚ) : ℝ) := by exact_mod_cast hβpos
  have hqQ : (0 : ℚ) ≤ rstQ w := by rw [rstQ]; positivity
  have hgapQ : (0 : ℚ) ≤ rstGap atoms acc mac uv w := by rw [rstGap]; linarith [hguard]
  have hcastq : ((rstQ w : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ rstStage w := by push_cast [rstQ]; ring
  have hcaste : (((2 : ℚ)⁻¹ ^ j : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ j := by push_cast; ring
  -- 1. the certified bounds, proved once
  obtain ⟨hbitsU, hmassU, hmassV⟩ :=
    restriction_certified_bounds (P := P) haccsound hmacsound hcons
  -- 2. the emitter's `ρ` and its two obligations
  obtain ⟨ρ, hρσ, hρmass, hδ, hρemit⟩ :=
    restriction_bridge (P := P) hnonneg hemit hbitsU hmassV hcont.disjoint hguard
  -- the floor comparison in `ℝ≥0∞`
  have hfloorE : ENNReal.ofReal ((rstBetaQ w : ℚ) : ℝ)
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ rstStage w)
      ≤ ENNReal.ofReal ((rstMassU acc w : ℚ) : ℝ) := by
    rw [← hcastq, ← ENNReal.ofReal_add (le_of_lt hβR) (by exact_mod_cast hqQ)]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hfloor)
  -- 3. mass ledger: `β₀ ≤ μ U`
  have hβμ0 : ENNReal.ofReal ((rstBetaQ w : ℚ) : ℝ)
      ≤ μ.toMeasure (openOf P uv.evenPart) :=
    floor_le_measure_of_success (P := P) haccsound hmacsound hp hcons (by omega) hfloorE
  -- 4. `β₀ ≤ atomicₘ U`, hence `β₀ ≤ 1`
  have hsubU : innerApprox P uv.evenPart (rstLevel w) ⊆ openOf P uv.evenPart := by
    rw [← iUnion_innerApprox P uv.evenPart]; exact Set.subset_iUnion _ (rstLevel w)
  have hβa0 : ENNReal.ofReal ((rstBetaQ w : ℚ) : ℝ)
      ≤ (atomic P (rstAtomic w)).toMeasure (openOf P uv.evenPart) :=
    le_trans (le_trans le_self_add hfloorE) (le_trans hmassU (measure_mono hsubU))
  have hβle1 : ENNReal.ofReal ((rstBetaQ w : ℚ) : ℝ) ≤ 1 :=
    le_trans hβμ0 (by simpa using measure_mono (μ := μ.toMeasure) (Set.subset_univ _))
  -- 5. the quarter, and with it the emitter's nonzero premise
  have hβ1pos : 0 < ENNReal.ofReal ((rstBetaQ w : ℚ) : ℝ) / 4 :=
    ENNReal.div_pos (ENNReal.ofReal_pos.mpr hβR).ne' (by simp)
  have hquarter : ENNReal.ofReal ((rstBetaQ w : ℚ) : ℝ) / 4 ≤ ρ Set.univ := by
    rw [hρmass]; exact quarter_le_of_floor hfloorE
  have hρne : ρ Set.univ ≠ 0 := (lt_of_lt_of_le hβ1pos hquarter).ne'
  -- 6. the gap sums to one
  have hgapE : (1 : ℝ≥0∞)
      ≤ ENNReal.ofReal ((rstMassU acc w : ℚ) : ℝ)
        + ENNReal.ofReal ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
        + ENNReal.ofReal ((rstGap atoms acc mac uv w : ℚ) : ℝ) := by
    have hU0 : (0 : ℝ) ≤ ((rstMassU acc w : ℚ) : ℝ) := hnonneg _ _
    have hV0 : (0 : ℝ) ≤ ((rstMassV atoms acc mac uv w : ℚ) : ℝ) := hnonneg _ _
    have hG0 : (0 : ℝ) ≤ ((rstGap atoms acc mac uv w : ℚ) : ℝ) := by exact_mod_cast hgapQ
    rw [← ENNReal.ofReal_add hU0 hV0, ← ENNReal.ofReal_add (add_nonneg hU0 hV0) hG0]
    refine le_of_eq ?_
    rw [show ((rstMassU acc w : ℚ) : ℝ) + ((rstMassV atoms acc mac uv w : ℚ) : ℝ)
          + ((rstGap atoms acc mac uv w : ℚ) : ℝ) = 1 by push_cast [rstGap]; ring]
    simp
  -- 7. the metric ledger's `d₀`, at the coupled indices
  rw [hm] at hmassU hmassV hβa0
  have hd₀ := explicit_normalized_budget (P := P) hp hcont hls hmassU hmassV hgapE
    (ENNReal.ofReal_pos.mpr hβR) hβle1
    (by rw [Measure.restrict_apply_univ]; exact hβμ0)
    (by rw [Measure.restrict_apply_univ]; exact hβa0)
  -- 8. the budget, transported once
  have hbudgetE := ofReal_budget_transport hβpos hqQ hgapQ hbudget
  rw [hcastq, hcaste] at hbudgetE
  rw [restrictionOut, hρemit hρne, ← hm] at *
  exact lp_normalized_le_dyadic hρσ hβ1pos hquarter hδ hd₀ hbudgetE

/-- **Termination.** For every precision `j` there is a successful witness.

Slack allocation: `β₀` is a dyadic with `4β₀ < μ U`; the predecessor level `n₀` is late enough
that `3β₀ ≤ μ(innerApprox U n₀)`; `ℓ := n + 1` for the `n ≥ n₀` returned by the index lemma; and
the dyadic target `r` satisfies `8r ≤ β₀·2⁻ʲ` and `r ≤ 2β₀`. Then `q < β₀` follows from
`2q ≤ δ + 2q < r ≤ 2β₀` rather than being proved separately. -/
theorem exists_restrictionSuccess
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (haccexact : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length →
        (mask.testBit i = true ↔ P.dense ((atoms m).getD i (0, 0)).1 ∈ A)) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) = (atomic P m).toMeasure A)
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (hmacspec : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n : ℕ),
      (∀ t i, i < l.length →
          (mac l (streamTake u n) n t).testBit i = true →
          P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
        ∧ (∀ t t' i, t ≤ t' → i < l.length →
            (mac l (streamTake u n) n t).testBit i = true →
            (mac l (streamTake u n) n t').testBit i = true)
        ∧ ∃ t, ∀ i, i < l.length →
            P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n →
            (mac l (streamTake u n) n t).testBit i = true)
    {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (hcont : ContinuityOpenNames P μ uv)
    (hposU : μ.toMeasure (openOf P uv.evenPart) ≠ 0) (j : ℕ) :
    ∃ w : ℕ, RestrictionSuccess atoms acc mac p uv j w := by
  classical
  set U := openOf P uv.evenPart with hUdef
  have hposR : (0 : ℝ) < (μ.toMeasure U).toReal :=
    ENNReal.toReal_pos hposU (measure_ne_top _ _)
  -- 1. a dyadic floor with fourfold slack
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < (μ.toMeasure U).toReal / 4 by linarith)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  set β₀ : ℚ := (2 : ℚ)⁻¹ ^ a with hβdef
  have hβR : ((β₀ : ℚ) : ℝ) = (2 : ℝ)⁻¹ ^ a := by push_cast [hβdef]; ring
  have hβpos : (0 : ℚ) < β₀ := by rw [hβdef]; positivity
  have hβ4 : 4 * ((β₀ : ℚ) : ℝ) < (μ.toMeasure U).toReal := by rw [hβR]; linarith
  -- 2. a level where the inner approximation already carries `3β₀`
  obtain ⟨n₀, hn₀⟩ :=
    ((ENNReal.tendsto_toReal (measure_ne_top μ.toMeasure U)).comp
      (tendsto_innerApprox P μ uv.evenPart)
      |>.eventually (eventually_gt_nhds (show 3 * ((β₀ : ℚ) : ℝ) < (μ.toMeasure U).toReal by
        linarith))).exists
  -- 3. a dyadic target below both budgets
  obtain ⟨b, hb⟩ := exists_pow_lt_of_lt_one
    (show (0 : ℝ) < min (((β₀ : ℚ) : ℝ) * (2 : ℝ)⁻¹ ^ j / 8) (2 * ((β₀ : ℚ) : ℝ)) by
      have : (0 : ℝ) < ((β₀ : ℚ) : ℝ) := by exact_mod_cast hβpos
      have h2 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j := by positivity
      exact lt_min (by positivity) (by linarith))
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hb1 : (2 : ℝ)⁻¹ ^ b < ((β₀ : ℚ) : ℝ) * (2 : ℝ)⁻¹ ^ j / 8 :=
    lt_of_lt_of_le hb (min_le_left _ _)
  have hb2 : (2 : ℝ)⁻¹ ^ b < 2 * ((β₀ : ℚ) : ℝ) := lt_of_lt_of_le hb (min_le_right _ _)
  -- 4. the index choice, above that level and with the stronger coupling
  obtain ⟨n, s, hn₀n, hns, hgap⟩ :=
    exists_indices_gap_floor (P := P) hp hcont (by positivity : (0:ℝ) < (2 : ℝ)⁻¹ ^ b) n₀
  set ℓ := n + 1 with hℓdef
  set m := p (s + 1) with hmdef
  -- the floor transfers up to `n` by monotonicity
  have hn3 : 3 * ((β₀ : ℚ) : ℝ) < (μ.toMeasure (innerApprox P uv.evenPart n)).toReal := by
    refine lt_of_lt_of_le hn₀ (ENNReal.toReal_mono (measure_ne_top _ _) ?_)
    exact measure_mono (monotone_innerApprox P uv.evenPart hn₀n)
  -- 5. completeness fuels on both tracks, then their maximum
  obtain ⟨tU, htU⟩ := (hmacspec (atoms m) uv.evenPart ℓ).2.2
  obtain ⟨tV, htV⟩ := (hmacspec (atoms m) uv.oddPart ℓ).2.2
  set t := max tU tV with htdef
  set maskU := mac (atoms m) (streamTake uv.evenPart ℓ) ℓ t with hmaskU
  set maskV := mac (atoms m) (streamTake uv.oddPart ℓ) ℓ t with hmaskV
  -- the two biconditionals, at the common fuel
  have hbiU : ∀ i, i < (atoms m).length →
      (maskU.testBit i = true ↔
        P.dense ((atoms m).getD i (0, 0)).1 ∈ innerApprox P uv.evenPart ℓ) := by
    intro i hi
    exact ⟨fun hbit => (hmacspec (atoms m) uv.evenPart ℓ).1 t i hi hbit,
      fun hmem => (hmacspec (atoms m) uv.evenPart ℓ).2.1 tU t i (le_max_left _ _) hi
        (htU i hi hmem)⟩
  have hbiV : ∀ i, i < (atoms m).length →
      (maskV.testBit i = true ↔
        P.dense ((atoms m).getD i (0, 0)).1 ∈ innerApprox P uv.oddPart ℓ) := by
    intro i hi
    exact ⟨fun hbit => (hmacspec (atoms m) uv.oddPart ℓ).1 t i hi hbit,
      fun hmem => (hmacspec (atoms m) uv.oddPart ℓ).2.1 tV t i (le_max_right _ _) hi
        (htV i hi hmem)⟩
  -- 6. exactness pins both accumulators to the atomic masses
  have hexU := haccexact m maskU _ (measurableSet_innerApprox _ _) hbiU
  have hexV := haccexact m maskV _ (measurableSet_innerApprox _ _) hbiV
  have hCU : ((ratOfCode (acc m maskU) : ℚ) : ℝ)
      = ((atomic P m).toMeasure (innerApprox P uv.evenPart ℓ)).toReal := by
    rw [← hexU, ENNReal.toReal_ofReal (hnonneg _ _)]
  have hCV : ((ratOfCode (acc m maskV) : ℚ) : ℝ)
      = ((atomic P m).toMeasure (innerApprox P uv.oddPart ℓ)).toReal := by
    rw [← hexV, ENNReal.toReal_ofReal (hnonneg _ _)]
  -- 7. the two inner approximations are disjoint, so the masses sum to at most one
  have hdisjℓ : Disjoint (innerApprox P uv.evenPart ℓ) (innerApprox P uv.oddPart ℓ) := by
    refine hcont.disjoint.mono ?_ ?_
    · rw [← iUnion_innerApprox P uv.evenPart]; exact Set.subset_iUnion _ ℓ
    · rw [← iUnion_innerApprox P uv.oddPart]; exact Set.subset_iUnion _ ℓ
  have hsum1 : ((atomic P m).toMeasure (innerApprox P uv.evenPart ℓ)).toReal
      + ((atomic P m).toMeasure (innerApprox P uv.oddPart ℓ)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ← measure_union hdisjℓ (measurableSet_innerApprox _ _)]
    simpa using ENNReal.toReal_mono (measure_ne_top (atomic P m).toMeasure _)
      (measure_mono (Set.subset_univ _))
  -- 8. the lower transfer at the coupled indices
  have hlow : (μ.toMeasure (innerApprox P uv.evenPart n)).toReal
      ≤ ((atomic P m).toMeasure (innerApprox P uv.evenPart ℓ)).toReal + (2 : ℝ)⁻¹ ^ s := by
    have hE := le_atomic_of_weakName (P := P) (u := uv.evenPart) hp (by omega : n < s)
    have hfin : (atomic P (p (s + 1))).toMeasure (innerApprox P uv.evenPart (n + 1))
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ s) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
    have hR := ENNReal.toReal_mono hfin hE
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ s)] at hR
  -- 9. pack the witness and discharge the six clauses
  refine ⟨packRestrictWit ℓ s t (Nat.pair (halfPowCode a) 0) m maskU, ?_, by simp [hℓdef]; omega,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨by simp [hmdef], by simp [hmaskU]⟩
  · simp only [rstBetaQ, rstBeta_packRestrictWit, Nat.unpair_pair, ratOfCode_halfPowCode]
    exact hβpos
  · simp only [rstMassU, rstMassV, rstOddMask, rstAtomic_packRestrictWit,
      rstMask_packRestrictWit, rstLevel_packRestrictWit, rstFuel_packRestrictWit]
    rw [← hmaskV]
    have : ((ratOfCode (acc m maskU) : ℚ) : ℝ) + ((ratOfCode (acc m maskV) : ℚ) : ℝ) ≤ 1 := by
      rw [hCU, hCV]; exact hsum1
    exact_mod_cast this
  · simp only [rstBetaQ, rstMassU, rstQ, rstBeta_packRestrictWit, rstAtomic_packRestrictWit,
      rstMask_packRestrictWit, rstStage_packRestrictWit, Nat.unpair_pair, ratOfCode_halfPowCode]
    have hqβ : (2 : ℝ)⁻¹ ^ s < ((β₀ : ℚ) : ℝ) := by
      have h2 : 2 * (2 : ℝ)⁻¹ ^ s < 2 * ((β₀ : ℚ) : ℝ) := lt_of_le_of_lt (by linarith) hb2
      linarith
    have : ((β₀ : ℚ) : ℝ) + (2 : ℝ)⁻¹ ^ s ≤ ((ratOfCode (acc m maskU) : ℚ) : ℝ) := by
      rw [hCU]; linarith
    have hcast : ((β₀ + (2 : ℚ)⁻¹ ^ s : ℚ) : ℝ) ≤ ((ratOfCode (acc m maskU) : ℚ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast hcast
  · simp only [rstBetaQ, rstMassU, rstMassV, rstGap, rstQ, rstOddMask,
      rstBeta_packRestrictWit, rstAtomic_packRestrictWit, rstMask_packRestrictWit,
      rstStage_packRestrictWit, rstLevel_packRestrictWit, rstFuel_packRestrictWit,
      Nat.unpair_pair, ratOfCode_halfPowCode]
    rw [← hmaskV]
    have hδreal : (1 : ℝ) - (((ratOfCode (acc m maskU) : ℚ) : ℝ)
          + ((ratOfCode (acc m maskV) : ℚ) : ℝ)) + 2 * (2 : ℝ)⁻¹ ^ s < (2 : ℝ)⁻¹ ^ b := by
      rw [hCU, hCV]; linarith [hgap]
    have hβjpos : (0 : ℝ) < ((β₀ : ℚ) : ℝ) * (2 : ℝ)⁻¹ ^ j := by
      have : (0 : ℝ) < ((β₀ : ℚ) : ℝ) := by exact_mod_cast hβpos
      positivity
    have hqnn : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ s := by positivity
    have hfinal : 14 * (2 : ℝ)⁻¹ ^ s
        + 8 * ((1 : ℝ) - (((ratOfCode (acc m maskU) : ℚ) : ℝ)
            + ((ratOfCode (acc m maskV) : ℚ) : ℝ)))
        ≤ ((β₀ : ℚ) : ℝ) * (2 : ℝ)⁻¹ ^ j := by linarith [hδreal, hb1, hqnn]
    have hcast : ((14 * (2 : ℚ)⁻¹ ^ s + 8 * (1 - (ratOfCode (acc m maskU)
          + ratOfCode (acc m maskV))) : ℚ) : ℝ)
        ≤ ((β₀ * (2 : ℚ)⁻¹ ^ j : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast hcast

/-- The prefix of the payload that a success check can read. -/
def restrictionPrefixBound (w : ℕ) : ℕ :=
  max (2 * (rstStage w + 1) + 1) (4 * rstLevel w)

theorem primrec_restrictionPrefixBound : Primrec restrictionPrefixBound := by
  have h1 : Primrec fun w => 2 * (rstStage w + 1) + 1 :=
    Primrec.succ.comp ((Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp primrec_rstStage)))
  have h2 : Primrec fun w => 4 * rstLevel w :=
    Primrec.nat_mul.comp (Primrec.const 4) primrec_rstLevel
  exact (Primrec.nat_max.comp h1 h2).of_eq fun _ => rfl

/-- The atomic index is read inside the bound. -/
theorem lt_restrictionPrefixBound_atomic (w : ℕ) :
    2 * (rstStage w + 1) < restrictionPrefixBound w :=
  lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)

/-- Every even-track coordinate below the level is read inside the bound. -/
theorem lt_restrictionPrefixBound_even {w i : ℕ} (hi : i < rstLevel w) :
    4 * i + 1 < restrictionPrefixBound w :=
  lt_of_lt_of_le (by omega) (le_max_right _ _)

/-- Every odd-track coordinate below the level is read inside the bound. -/
theorem lt_restrictionPrefixBound_odd {w i : ℕ} (hi : i < rstLevel w) :
    4 * i + 3 < restrictionPrefixBound w :=
  lt_of_lt_of_le (by omega) (le_max_right _ _)

/-- Payload lookup: the weak-name coordinate. -/
theorem payload_read_stage (p uv : Baire) (k : ℕ) :
    Baire.interleave p uv (2 * k) = p k := Baire.interleave_even _ _ _

/-- Payload lookup: the even track. -/
theorem payload_read_even (p uv : Baire) (i : ℕ) :
    Baire.interleave p uv (4 * i + 1) = uv.evenPart i := by
  rw [show 4 * i + 1 = 2 * (2 * i) + 1 by ring, Baire.interleave_odd, Baire.evenPart_apply]

/-- Payload lookup: the odd track. -/
theorem payload_read_odd (p uv : Baire) (i : ℕ) :
    Baire.interleave p uv (4 * i + 3) = uv.oddPart i := by
  rw [show 4 * i + 3 = 2 * (2 * i + 1) + 1 by ring, Baire.interleave_odd, Baire.oddPart_apply]

/-- The atomic index as read from the prefix. Used only by the consistency clause. -/
def rstAtomicOf (pre : List ℕ) (w : ℕ) : ℕ := pre.getD (2 * (rstStage w + 1)) 0

/-- The even track's prefix, extracted from the payload prefix. -/
def rstEvenPre (pre : List ℕ) (w : ℕ) : List ℕ :=
  streamTake (fun i => pre.getD (4 * i + 1) 0) (rstLevel w)

/-- The odd track's prefix, extracted from the payload prefix. -/
def rstOddPre (pre : List ℕ) (w : ℕ) : List ℕ :=
  streamTake (fun i => pre.getD (4 * i + 3) 0) (rstLevel w)

/-- The odd mask, rebuilt from the extracted odd prefix at the *stored* atomic index. -/
def rstMaskVOf (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : ℕ :=
  mac (atoms (rstAtomic w)) (rstOddPre pre w) (rstLevel w) (rstFuel w)

/-- The odd track's certified mass — the only prefix-dependent coded quantity. -/
def rstMassVOf (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : ℚ :=
  ratOfCode (acc (rstAtomic w) (rstMaskVOf atoms mac pre w))

/-- The extracted gap, `1 - (cU + cV)` with `cU` witness-only. -/
def rstGapOf (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : ℚ :=
  1 - (rstMassU acc w + rstMassVOf atoms acc mac pre w)

theorem rstAtomicOf_streamTake (p uv : Baire) (w : ℕ) :
    rstAtomicOf (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w
      = p (rstStage w + 1) := by
  rw [rstAtomicOf, streamTake_getD _ (lt_restrictionPrefixBound_atomic w), payload_read_stage]

theorem rstEvenPre_streamTake (p uv : Baire) (w : ℕ) :
    rstEvenPre (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w
      = streamTake uv.evenPart (rstLevel w) := by
  unfold rstEvenPre
  refine List.ext_getElem (by simp [length_streamTake]) fun i h1 h2 => ?_
  rw [getElem_streamTake, getElem_streamTake]
  have hi : i < rstLevel w := by simpa [length_streamTake] using h1
  rw [streamTake_getD _ (lt_restrictionPrefixBound_even hi), payload_read_even]

theorem rstOddPre_streamTake (p uv : Baire) (w : ℕ) :
    rstOddPre (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w
      = streamTake uv.oddPart (rstLevel w) := by
  unfold rstOddPre
  refine List.ext_getElem (by simp [length_streamTake]) fun i h1 h2 => ?_
  rw [getElem_streamTake, getElem_streamTake]
  have hi : i < rstLevel w := by simpa [length_streamTake] using h1
  rw [streamTake_getD _ (lt_restrictionPrefixBound_odd hi), payload_read_odd]

theorem rstMaskVOf_streamTake (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) :
    rstMaskVOf atoms mac (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w
      = rstOddMask atoms mac uv w := by
  rw [rstMaskVOf, rstOddMask, rstOddPre_streamTake]

theorem rstMassVOf_streamTake (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) :
    rstMassVOf atoms acc mac
        (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w
      = rstMassV atoms acc mac uv w := by
  rw [rstMassVOf, rstMassV, rstMaskVOf_streamTake]

theorem rstGapOf_streamTake (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) :
    rstGapOf atoms acc mac
        (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w
      = rstGap atoms acc mac uv w := by
  rw [rstGapOf, rstGap, rstMassVOf_streamTake]

/-- The stage dyadic, as a code. -/
def rstQCode (w : ℕ) : RatCode := halfPowCode (rstStage w)

theorem ratOfCode_rstQCode (w : ℕ) : ratOfCode (rstQCode w) = rstQ w := by
  rw [rstQCode, ratOfCode_halfPowCode, rstQ]

/-- The even track's certified mass, as a code. Witness-only. -/
def rstMassUCode (acc : ℕ → ℕ → RatCode) (w : ℕ) : RatCode := acc (rstAtomic w) (rstMask w)

theorem ratOfCode_rstMassUCode (acc : ℕ → ℕ → RatCode) (w : ℕ) :
    ratOfCode (rstMassUCode acc w) = rstMassU acc w := rfl

/-- The odd track's certified mass, as a code. The only prefix-dependent one. -/
def rstMassVCodeOf (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : RatCode :=
  acc (rstAtomic w) (rstMaskVOf atoms mac pre w)

theorem ratOfCode_rstMassVCodeOf (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) :
    ratOfCode (rstMassVCodeOf atoms acc mac pre w) = rstMassVOf atoms acc mac pre w := rfl

/-- The gap, as a code. -/
def rstGapCodeOf (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : RatCode :=
  subCode oneCode (addCode (rstMassUCode acc w) (rstMassVCodeOf atoms acc mac pre w))

theorem ratOfCode_rstGapCodeOf (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) :
    ratOfCode (rstGapCodeOf atoms acc mac pre w) = rstGapOf atoms acc mac pre w := by
  rw [rstGapCodeOf, ratOfCode_subCode, ratOfCode_addCode, ratOfCode_oneCode,
    ratOfCode_rstMassUCode, ratOfCode_rstMassVCodeOf, rstGapOf]

/-- The budget's left-hand side `14q + 8δ`, as a code. -/
def rstBudgetLhsCode (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : RatCode :=
  addCode (mulCode (natCode 14) (rstQCode w))
    (mulCode (natCode 8) (rstGapCodeOf atoms acc mac pre w))

theorem ratOfCode_rstBudgetLhsCode (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) :
    ratOfCode (rstBudgetLhsCode atoms acc mac pre w)
      = 14 * rstQ w + 8 * rstGapOf atoms acc mac pre w := by
  rw [rstBudgetLhsCode, ratOfCode_addCode, ratOfCode_mulCode, ratOfCode_mulCode,
    ratOfCode_natCode, ratOfCode_natCode, ratOfCode_rstQCode, ratOfCode_rstGapCodeOf]
  norm_num

/-- The budget's right-hand side `β₀ · 2⁻ʲ`, as a code. -/
def rstBudgetRhsCode (w j : ℕ) : RatCode := mulCode (rstBeta w) (halfPowCode j)

theorem ratOfCode_rstBudgetRhsCode (w j : ℕ) :
    ratOfCode (rstBudgetRhsCode w j) = rstBetaQ w * (2 : ℚ)⁻¹ ^ j := by
  rw [rstBudgetRhsCode, ratOfCode_mulCode, ratOfCode_halfPowCode, rstBetaQ]

/-- Leaf 1: the stored atomic index is the payload's stage entry. -/
def rstBAtomic (pre : List ℕ) (w : ℕ) : Bool := decide (rstAtomicOf pre w = rstAtomic w)

theorem rstBAtomic_iff (pre : List ℕ) (w : ℕ) :
    rstBAtomic pre w = true ↔ rstAtomicOf pre w = rstAtomic w := by simp [rstBAtomic]

/-- Leaf 2: the stored even mask is `mac` at the extracted even prefix. -/
def rstBEvenMask (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : Bool :=
  decide (rstMask w = mac (atoms (rstAtomic w)) (rstEvenPre pre w) (rstLevel w) (rstFuel w))

theorem rstBEvenMask_iff (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) :
    rstBEvenMask atoms mac pre w = true ↔
      rstMask w = mac (atoms (rstAtomic w)) (rstEvenPre pre w) (rstLevel w) (rstFuel w) := by
  simp [rstBEvenMask]

/-- Leaf 3: the index coupling. -/
def rstBCoupling (w : ℕ) : Bool := decide (rstLevel w + 2 ≤ rstStage w)

theorem rstBCoupling_iff (w : ℕ) :
    rstBCoupling w = true ↔ rstLevel w + 2 ≤ rstStage w := by simp [rstBCoupling]

/-- Leaf 4: the floor is positive. -/
def rstBPos (w : ℕ) : Bool := decide (0 < ratOfCode (rstBeta w))

theorem rstBPos_iff (w : ℕ) : rstBPos w = true ↔ 0 < rstBetaQ w := by simp [rstBPos, rstBetaQ]

/-- Leaf 5: the two certified masses do not exceed the whole. -/
def rstBGuard (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : Bool :=
  decide (ratOfCode (addCode (rstMassUCode acc w) (rstMassVCodeOf atoms acc mac pre w)) ≤ 1)

theorem rstBGuard_iff (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) :
    rstBGuard atoms acc mac pre w = true ↔
      rstMassU acc w + rstMassVOf atoms acc mac pre w ≤ 1 := by
  simp [rstBGuard, ratOfCode_addCode, ratOfCode_rstMassUCode, ratOfCode_rstMassVCodeOf]

/-- Leaf 6: the floor comparison `β₀ + q ≤ cU`. -/
def rstBFloor (acc : ℕ → ℕ → RatCode) (w : ℕ) : Bool :=
  decide (ratOfCode (addCode (rstBeta w) (rstQCode w)) ≤ ratOfCode (rstMassUCode acc w))

theorem rstBFloor_iff (acc : ℕ → ℕ → RatCode) (w : ℕ) :
    rstBFloor acc w = true ↔ rstBetaQ w + rstQ w ≤ rstMassU acc w := by
  simp [rstBFloor, ratOfCode_addCode, ratOfCode_rstQCode, ratOfCode_rstMassUCode, rstBetaQ]

/-- Leaf 7: the division-free budget. Unconditional: an exact rational comparison. -/
def rstBBudget (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) : Bool :=
  decide (ratOfCode (rstBudgetLhsCode atoms acc mac pre w)
    ≤ ratOfCode (rstBudgetRhsCode w j))

theorem rstBBudget_iff (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) :
    rstBBudget atoms acc mac pre j w = true ↔
      14 * rstQ w + 8 * rstGapOf atoms acc mac pre w
        ≤ rstBetaQ w * (2 : ℚ)⁻¹ ^ j := by
  simp [rstBBudget, ratOfCode_rstBudgetLhsCode, ratOfCode_rstBudgetRhsCode]

/-- The consistency Boolean, from leaves 1 and 2. -/
def rstBConsistent (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : Bool :=
  rstBAtomic pre w && rstBEvenMask atoms mac pre w

/-- Clause 1 at the payload's own prefix. -/
theorem rstBConsistent_streamTake_iff (atoms : ℕ → List (ℕ × ℕ))
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) :
    rstBConsistent atoms mac
        (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w = true
      ↔ RestrictWitConsistent atoms mac p uv.evenPart w := by
  rw [rstBConsistent, Bool.and_eq_true, rstBAtomic_iff, rstBEvenMask_iff,
    rstAtomicOf_streamTake, rstEvenPre_streamTake, RestrictWitConsistent]
  exact and_congr_left' eq_comm

/-- Clause 4 at the payload's own prefix. -/
theorem rstBGuard_streamTake_iff (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) :
    rstBGuard atoms acc mac
        (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) w = true
      ↔ rstMassU acc w + rstMassV atoms acc mac uv w ≤ 1 := by
  rw [rstBGuard_iff, rstMassVOf_streamTake]

/-- Clause 6 at the payload's own prefix. -/
theorem rstBBudget_streamTake_iff (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (j w : ℕ) :
    rstBBudget atoms acc mac
        (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) j w = true
      ↔ 14 * rstQ w + 8 * rstGap atoms acc mac uv w
        ≤ rstBetaQ w * (2 : ℚ)⁻¹ ^ j := by
  rw [rstBBudget_iff, rstGapOf_streamTake]

/-- **The Boolean predicate**, in the semantic clause order. -/
def restrictionSuccessB (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) : Bool :=
  rstBConsistent atoms mac pre w && rstBCoupling w && rstBPos w
    && rstBGuard atoms acc mac pre w && rstBFloor acc w
    && rstBBudget atoms acc mac pre j w

/-- **Exact-prefix equivalence.** The Boolean test on the payload's own prefix is precisely the
semantic predicate — not merely sufficient for it. -/
theorem restrictionSuccessB_streamTake_iff (atoms : ℕ → List (ℕ × ℕ))
    (acc : ℕ → ℕ → RatCode) (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ)
    (p uv : Baire) (j w : ℕ) :
    restrictionSuccessB atoms acc mac
        (streamTake (Baire.interleave p uv) (restrictionPrefixBound w)) j w = true
      ↔ RestrictionSuccess atoms acc mac p uv j w := by
  rw [restrictionSuccessB, RestrictionSuccess, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    rstBConsistent_streamTake_iff, rstBCoupling_iff, rstBPos_iff,
    rstBGuard_streamTake_iff, rstBFloor_iff, rstBBudget_streamTake_iff]
  tauto

/-- The search predicate, packed as `⟨j, w⟩` and returning `0` exactly on success. -/
def restrictionCheck (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (n : ℕ) : ℕ :=
  if restrictionSuccessB atoms acc mac pre n.unpair.1 n.unpair.2 = true then 0 else 1

/-- Projection: the packed call unpacks to its components. -/
theorem restrictionCheck_pair (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) :
    restrictionCheck atoms acc mac pre (Nat.pair j w)
      = if restrictionSuccessB atoms acc mac pre j w = true then 0 else 1 := by
  rw [restrictionCheck, Nat.unpair_pair]

/-- Zero means success. Kept separate from the projection lemma. -/
theorem restrictionCheck_eq_zero_iff (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) :
    restrictionCheck atoms acc mac pre (Nat.pair j w) = 0
      ↔ restrictionSuccessB atoms acc mac pre j w = true := by
  rw [restrictionCheck_pair]
  split <;> simp_all

/-- The bound, in the builder's binary form. The oracle head is ignored. -/
def restrictionSearchBound (v : ℕ) (_ : ℕ) : ℕ := restrictionPrefixBound v.unpair.2

theorem restrictionSearchBound_pair (j w h : ℕ) :
    restrictionSearchBound (Nat.pair j w) h = restrictionPrefixBound w := by
  rw [restrictionSearchBound, Nat.unpair_pair]

theorem primrec₂_restrictionSearchBound : Primrec₂ restrictionSearchBound :=
  (primrec_restrictionPrefixBound.comp
    ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)).to₂

/-- The packed test, in the builder's convention. -/
def restrictionSearchG (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (v : ℕ) : ℕ :=
  restrictionCheck atoms acc mac (ofNat (List ℕ) v.unpair.2) v.unpair.1

/-- **Unpacking.** Pure projection bookkeeping. -/
theorem restrictionSearchG_pack {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (j w : ℕ) (pre : List ℕ) :
    restrictionSearchG atoms acc mac (Nat.pair (Nat.pair j w) (encode pre))
      = restrictionCheck atoms acc mac pre (Nat.pair j w) := by
  rw [restrictionSearchG]
  simp [Denumerable.ofNat_encode]

/-- **Zero means success.** The convention bridge, stated separately from the projection. -/
theorem restrictionSearchG_eq_zero_iff {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (j w : ℕ) (pre : List ℕ) :
    restrictionSearchG atoms acc mac (Nat.pair (Nat.pair j w) (encode pre)) = 0
      ↔ restrictionSuccessB atoms acc mac pre j w = true := by
  rw [restrictionSearchG_pack, restrictionCheck_eq_zero_iff]

/-- **The builder's success predicate is the semantic one.** On the payload `interleave p uv`,
`SearchSuccess` at input `j` and candidate `w` is exactly `RestrictionSuccess`. -/
theorem searchSuccess_iff_restrictionSuccess {atoms : ℕ → List (ℕ × ℕ)}
    {acc : ℕ → ℕ → RatCode} {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (p uv : Baire) (j w : ℕ) :
    SearchSuccess restrictionSearchBound (restrictionSearchG atoms acc mac)
        (Baire.interleave p uv) j w
      ↔ RestrictionSuccess atoms acc mac p uv j w := by
  rw [SearchSuccess, restrictionSearchBound_pair,
    restrictionSearchG_eq_zero_iff, restrictionSuccessB_streamTake_iff]

private theorem streamTake_eq_map_range {α : Type*} (f : ℕ → α) (n : ℕ) :
    streamTake f n = (List.range n).map f := by
  refine List.ext_getElem (by simp [length_streamTake]) fun i h1 h2 => ?_
  rw [getElem_streamTake, List.getElem_map, List.getElem_range]

theorem primrec_rstAtomicOf : Primrec fun x : List ℕ × ℕ => rstAtomicOf x.1 x.2 :=
  (Primrec.list_getD 0).comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (primrec_rstStage.comp Primrec.snd)))

theorem primrec_rstEvenPre : Primrec fun x : List ℕ × ℕ => rstEvenPre x.1 x.2 :=
  (Primrec.list_map (Primrec.list_range.comp (primrec_rstLevel.comp Primrec.snd))
    (((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd)
        (Primrec.const 1))).to₂)).of_eq fun x => by
      rw [rstEvenPre, streamTake_eq_map_range]

theorem primrec_rstOddPre : Primrec fun x : List ℕ × ℕ => rstOddPre x.1 x.2 :=
  (Primrec.list_map (Primrec.list_range.comp (primrec_rstLevel.comp Primrec.snd))
    (((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd)
        (Primrec.const 3))).to₂)).of_eq fun x => by
      rw [rstOddPre, streamTake_eq_map_range]

theorem primrec_rstMaskVOf {atoms : ℕ → List (ℕ × ℕ)}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstMaskVOf atoms mac x.1 x.2 :=
  hmac.comp
    (((hatoms.comp (primrec_rstAtomic.comp Primrec.snd)).pair primrec_rstOddPre).pair
      ((primrec_rstLevel.comp Primrec.snd).pair (primrec_rstFuel.comp Primrec.snd)))

theorem primrec_rstQCode : Primrec rstQCode :=
  primrec_halfPowCode.comp primrec_rstStage

theorem primrec_rstMassUCode {acc : ℕ → ℕ → RatCode} (hacc : Primrec₂ acc) :
    Primrec (rstMassUCode acc) :=
  hacc.comp primrec_rstAtomic primrec_rstMask

theorem primrec_rstMassVCodeOf {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstMassVCodeOf atoms acc mac x.1 x.2 :=
  hacc.comp (primrec_rstAtomic.comp Primrec.snd) (primrec_rstMaskVOf hatoms hmac)

theorem primrec_rstGapCodeOf {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstGapCodeOf atoms acc mac x.1 x.2 :=
  primrec₂_subCode.comp (Primrec.const oneCode)
    (primrec₂_addCode.comp ((primrec_rstMassUCode hacc).comp Primrec.snd)
      (primrec_rstMassVCodeOf hatoms hacc hmac))

theorem primrec_rstBudgetLhsCode {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstBudgetLhsCode atoms acc mac x.1 x.2 :=
  primrec₂_addCode.comp
    (primrec₂_mulCode.comp (Primrec.const (natCode 14))
      (primrec_rstQCode.comp Primrec.snd))
    (primrec₂_mulCode.comp (Primrec.const (natCode 8))
      (primrec_rstGapCodeOf hatoms hacc hmac))

theorem primrec_rstBudgetRhsCode : Primrec fun y : ℕ × ℕ => rstBudgetRhsCode y.1 y.2 :=
  primrec₂_mulCode.comp (primrec_rstBeta.comp Primrec.fst)
    (primrec_halfPowCode.comp Primrec.snd)

theorem primrec_rstBAtomic : Primrec fun x : List ℕ × ℕ => rstBAtomic x.1 x.2 :=
  (Primrec.ite (Primrec.eq.comp primrec_rstAtomicOf (primrec_rstAtomic.comp Primrec.snd))
    (Primrec.const true) (Primrec.const false)).of_eq fun x => by
      by_cases h : rstAtomicOf x.1 x.2 = rstAtomic x.2 <;> simp [rstBAtomic, h]

theorem primrec_rstBEvenMask {atoms : ℕ → List (ℕ × ℕ)}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstBEvenMask atoms mac x.1 x.2 :=
  (Primrec.ite
    (Primrec.eq.comp (primrec_rstMask.comp Primrec.snd)
      (hmac.comp
        (((hatoms.comp (primrec_rstAtomic.comp Primrec.snd)).pair primrec_rstEvenPre).pair
          ((primrec_rstLevel.comp Primrec.snd).pair (primrec_rstFuel.comp Primrec.snd)))))
    (Primrec.const true) (Primrec.const false)).of_eq fun x => by
      by_cases h : rstMask x.2
          = mac (atoms (rstAtomic x.2)) (rstEvenPre x.1 x.2) (rstLevel x.2) (rstFuel x.2) <;>
        simp [rstBEvenMask, h]

theorem primrec_rstBCoupling : Primrec rstBCoupling :=
  (Primrec.ite (Primrec.nat_le.comp
      (Primrec.nat_add.comp primrec_rstLevel (Primrec.const 2)) primrec_rstStage)
    (Primrec.const true) (Primrec.const false)).of_eq fun w => by
      by_cases h : rstLevel w + 2 ≤ rstStage w <;> simp [rstBCoupling, h]

theorem primrec_rstBPos : Primrec rstBPos :=
  (Primrec.ite (primrecPred_ratLt (Primrec.const (natCode 0)) primrec_rstBeta)
    (Primrec.const true) (Primrec.const false)).of_eq fun w => by
      simp only [rstBPos, ratOfCode_natCode, Nat.cast_zero]
      by_cases h : (0 : ℚ) < ratOfCode (rstBeta w) <;> simp [h]

theorem primrec_rstBGuard {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstBGuard atoms acc mac x.1 x.2 :=
  (Primrec.ite
    (primrecPred_ratLt (Primrec.const oneCode)
      (primrec₂_addCode.comp ((primrec_rstMassUCode hacc).comp Primrec.snd)
        (primrec_rstMassVCodeOf hatoms hacc hmac)))
    (Primrec.const false) (Primrec.const true)).of_eq fun x => by
      simp only [rstBGuard, ratOfCode_oneCode]
      by_cases h : (1 : ℚ)
          < ratOfCode (addCode (rstMassUCode acc x.2) (rstMassVCodeOf atoms acc mac x.1 x.2))
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mp h]

theorem primrec_rstBFloor {acc : ℕ → ℕ → RatCode} (hacc : Primrec₂ acc) :
    Primrec (rstBFloor acc) :=
  (Primrec.ite
    (primrecPred_ratLt (primrec_rstMassUCode hacc)
      (primrec₂_addCode.comp primrec_rstBeta primrec_rstQCode))
    (Primrec.const false) (Primrec.const true)).of_eq fun w => by
      simp only [rstBFloor]
      by_cases h : ratOfCode (rstMassUCode acc w)
          < ratOfCode (addCode (rstBeta w) (rstQCode w))
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mp h]

theorem primrec_rstBBudget {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun y : List ℕ × ℕ × ℕ => rstBBudget atoms acc mac y.1 y.2.1 y.2.2 :=
  (Primrec.ite
    (primrecPred_ratLt
      (primrec_rstBudgetRhsCode.comp
        ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd)))
      ((primrec_rstBudgetLhsCode hatoms hacc hmac).comp
        (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))))
    (Primrec.const false) (Primrec.const true)).of_eq fun y => by
      simp only [rstBBudget]
      by_cases h : ratOfCode (rstBudgetRhsCode y.2.2 y.2.1)
          < ratOfCode (rstBudgetLhsCode atoms acc mac y.1 y.2.2)
      · simp [h, not_le.mpr h]
      · simp [h, not_lt.mp h]

theorem primrec_rstBConsistent {atoms : ℕ → List (ℕ × ℕ)}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => rstBConsistent atoms mac x.1 x.2 :=
  (Primrec.cond primrec_rstBAtomic (primrec_rstBEvenMask hatoms hmac)
    (Primrec.const false)).of_eq fun x => by
      cases h : rstBAtomic x.1 x.2 <;> simp [rstBConsistent, h]

theorem primrec_restrictionSuccessB {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun y : List ℕ × ℕ × ℕ => restrictionSuccessB atoms acc mac y.1 y.2.1 y.2.2 := by
  have hpw : Primrec fun y : List ℕ × ℕ × ℕ => (y.1, y.2.2) :=
    Primrec.fst.pair (Primrec.snd.comp Primrec.snd)
  have hw : Primrec fun y : List ℕ × ℕ × ℕ => y.2.2 := Primrec.snd.comp Primrec.snd
  have hC := (primrec_rstBConsistent hatoms hmac).comp hpw
  have hCp := primrec_rstBCoupling.comp hw
  have hPo := primrec_rstBPos.comp hw
  have hG := (primrec_rstBGuard hatoms hacc hmac).comp hpw
  have hF := (primrec_rstBFloor hacc).comp hw
  have hB := primrec_rstBBudget hatoms hacc hmac
  exact (Primrec.cond
    (Primrec.cond
      (Primrec.cond
        (Primrec.cond (Primrec.cond hC hCp (Primrec.const false)) hPo (Primrec.const false))
        hG (Primrec.const false))
      hF (Primrec.const false))
    hB (Primrec.const false)).of_eq fun _ => by simp [restrictionSuccessB]

-- With its denotation (`restrictionSuccessB_streamTake_iff`) and `Primrec` lemma both in hand,
-- the Boolean layer is sealed: the packed test below composes it as a black box, which keeps
-- `whnf` from unfolding six nested leaves through the coded arithmetic.
attribute [local irreducible] restrictionSuccessB

theorem primrec_restrictionCheck {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => restrictionCheck atoms acc mac x.1 x.2 := by
  have htuple : Primrec fun x : List ℕ × ℕ => (x.1, (x.2.unpair.1, x.2.unpair.2)) :=
    Primrec.fst.pair
      ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
  exact (Primrec.cond ((primrec_restrictionSuccessB hatoms hacc hmac).comp htuple)
    (Primrec.const 0) (Primrec.const 1)).of_eq fun x => by
      cases h : restrictionSuccessB atoms acc mac x.1 x.2.unpair.1 x.2.unpair.2 <;>
        simp [restrictionCheck, h]

theorem primrec_restrictionSearchG {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec (restrictionSearchG atoms acc mac) := by
  have hpre : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)
  have hv : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  exact (primrec_restrictionCheck hatoms hacc hmac).comp (hpre.pair hv)

/-- **The normalized-restriction realizer.** From a weak name of `μ` and an effective
`μ`-continuity open of positive
mass, one code emits a weak name of the normalized restriction to that open.

The target is exposed as a probability measure together with the equation identifying its
underlying measure.  This avoids making the proof of the positive-mass promise part of the public
data while still stating exactly which normalized restriction the output names. -/
theorem exists_contSetRestrictionCode :
    ∃ c : OracleCode, ∀ (p uv : Baire) (μ : ProbabilityMeasure X),
      WeakMeasureNames P p μ → ContinuityOpenNames P μ uv →
      μ.toMeasure (openOf P uv.evenPart) ≠ 0 →
      ∃ r ∈ c.evalStream (Baire.interleave p uv), ∃ ν : ProbabilityMeasure X,
        ν.toMeasure = normalizedRestriction μ (openOf P uv.evenPart) ∧
        (weakMeasureRep P).Names r ν := by
  classical
  obtain ⟨atoms, acc, emit, hatoms, haccprim, hemitprim, hnonneg, haccsound,
      haccexact, hemitter⟩ := exists_completeCertifiedAtomicCode P
  obtain ⟨mac, hmacprim, hmacspec⟩ := exists_maskAtCode (P := P)
  obtain ⟨searchCode, hsearchmem, hsearchdom⟩ :=
    OracleCode.exists_prefixSearchCode primrec₂_restrictionSearchBound
      (primrec_restrictionSearchG hatoms haccprim hmacprim)
  obtain ⟨outCode, hout⟩ :=
    OracleCode.exists_ofNatFnCode (primrec_restrictionOut hemitprim).to_comp
  refine ⟨OracleCode.comp outCode searchCode, fun p uv μ hp hcont hpos => ?_⟩
  set F : Baire := Baire.interleave p uv with hF
  have hdom : ∀ j, (searchCode.eval F j).Dom := by
    intro j
    rw [hsearchdom]
    obtain ⟨w, hw⟩ :=
      exists_restrictionSuccess (P := P) haccexact hnonneg hmacspec hp hcont hpos j
    exact ⟨w, (searchSuccess_iff_restrictionSuccess p uv j w).2 hw⟩
  set wit : ℕ → ℕ := fun j => (searchCode.eval F j).get (hdom j) with hwit
  set r : Baire := fun j => restrictionOut emit (wit j) with hr
  let ν : ProbabilityMeasure X :=
    ⟨normalizedRestriction μ (openOf P uv.evenPart), by
      rw [normalizedRestriction]
      exact ProbabilityTheory.cond_isProbabilityMeasure hpos⟩
  refine ⟨r, ?_, ν, rfl, (weakMeasureRep_names_iff P).2 ?_⟩
  · refine OracleCode.mem_evalStream.mpr fun j => ?_
    have hs : searchCode.eval F j = Part.some (wit j) :=
      Part.eq_some_iff.mpr (Part.get_mem _)
    rw [OracleCode.eval_comp_some hs, hout]
    exact Part.mem_some _
  · intro j
    have hmem : wit j ∈ searchCode.eval F j := Part.get_mem _
    have hsuccess : RestrictionSuccess atoms acc mac p uv j (wit j) := by
      have hsearch := ((hsearchmem F j (wit j)).mp hmem).1
      rw [hF] at hsearch
      exact (searchSuccess_iff_restrictionSuccess p uv j (wit j)).1 hsearch
    have hbound := restrictionSuccess_sound (P := P) hnonneg haccsound hemitter
      (fun l u n t i hi hb => (hmacspec l u n).1 t i hi hb) hp hcont hsuccess
    rw [levyProkhorovDist, levyProkhorovEDist_comm]
    calc
      (levyProkhorovEDist (atomic P (r j)).toMeasure ν.toMeasure).toReal
          ≤ (ENNReal.ofReal ((2 : ℝ)⁻¹ ^ j)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (by simpa [ν, r] using hbound)
      _ = (2 : ℝ)⁻¹ ^ j := ENNReal.toReal_ofReal (by positivity)

end RestrictionWitness

end ContinuityOpenRestriction

end ComputableAnalysis
