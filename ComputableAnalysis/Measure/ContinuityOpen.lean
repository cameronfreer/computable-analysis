/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.WeakRepresentation

/-!
# Effective continuity opens

An effective `µ`-continuity open is named by a pair of open-set names on the two tracks of one
stream: the even track enumerates presented balls whose union is `U`, the odd track presented
balls whose union is `V`, subject to the semantic side condition that `U` and `V` are disjoint
and together carry all the mass. `U`'s enumeration gives lower bounds on `µ U`; `V`'s gives
lower bounds on `µ V = 1 - µ U`, hence upper bounds on `µ U`. This is the two-sided access that
makes `µ U` a computable real, and it is implied by (but weaker than) Ackerman–Freer–Roy's
naming of a continuity set by `U` together with an element of the interior of the complement:
disjointness of two opens gives `V ⊆ (closure U)ᶜ`, and full mass then forces the frontier to
be null.

Radii are coded rationals and a nonpositive radius gives the empty ball, so no skip marker is
needed and enumerations are total.

## Main definitions and results

* `openOf` — the open set named by a stream, `ContinuityOpenNames` — the two-track name.
* `innerApprox` — the stage-`n` inner approximation: the first `n` enumerated balls, each
  shrunk by `2⁻ⁿ`; monotone, open, exhausting `openOf` (`tendsto_innerApprox`).
* `le_measure_of_thickening_subset` — the engine estimate: if the `ε`-thickening of `A` sits
  inside `U`, an LP-`ε`-close approximant's mass on `A` is a lower bound for `µ U` up to `ε`.
* `atomic_le_of_weakName`, `le_atomic_of_weakName` — the two halves of the certified bracket
  read off a weak name at coupled indices.
* `tendsto_gap` — both tracks converge, so the bracket closes.

## Implementation notes

The index coupling is enforced by hypotheses (`n ≤ m`, `n < m`) of the thickening lemmas,
never by discipline. Membership in an inner approximation is a finite disjunction of strict
ball inequalities (`mem_innerApprox_iff`), which is what a presentation's `ltSemidec` can
certify; no negative information is ever needed.
-/

open MeasureTheory Metric Encodable Denumerable
open scoped ENNReal NNReal

namespace ComputableAnalysis

open OracleCode

section ContinuityOpen

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

/-! ### The representation -/

/-- The open set named by a stream: the union of the presented balls it enumerates. -/
noncomputable def openOf (u : Baire) : Set X :=
  ⋃ k, ball (P.dense (u k).unpair.1) ((ratOfCode (u k).unpair.2 : ℚ) : ℝ)

omit [MeasurableSpace X] [BorelSpace X] in
theorem isOpen_openOf (u : Baire) : IsOpen (openOf P u) :=
  isOpen_iUnion fun _ => isOpen_ball

theorem measurableSet_openOf (u : Baire) : MeasurableSet (openOf P u) :=
  (isOpen_openOf P u).measurableSet

/-- **The effective `µ`-continuity open.** The even track names the open set `U`; the odd track
names an effective a.e.-complement witness `V`, not required to be `interior Uᶜ`. -/
structure ContinuityOpenNames (μ : ProbabilityMeasure X) (uv : Baire) : Prop where
  disjoint : Disjoint (openOf P uv.evenPart) (openOf P uv.oddPart)
  full : μ.toMeasure (openOf P uv.evenPart) + μ.toMeasure (openOf P uv.oddPart) = 1

variable {P}

/-! ### The engine estimate -/

omit [BorelSpace X] in
/-- **The engine.** If the `ε`-thickening of `A` sits inside `U`, then the approximant's mass
on `A` is a lower bound for `µ U`, up to `ε`. -/
theorem le_measure_of_thickening_subset {μ ν : ProbabilityMeasure X} {ε c : ℝ≥0∞}
    (hlt : levyProkhorovEDist ν.toMeasure μ.toMeasure < c) (hc : c ≤ ε) (hεtop : ε ≠ ⊤)
    {A U : Set X} (hA : MeasurableSet A) (hsub : thickening ε.toReal A ⊆ U) :
    ν.toMeasure A ≤ μ.toMeasure U + c := by
  have hstep := left_measure_le_of_levyProkhorovEDist_lt hlt hA
  refine hstep.trans (add_le_add (measure_mono ?_) le_rfl)
  refine subset_trans (thickening_mono ?_ A) hsub
  exact ENNReal.toReal_mono hεtop hc

/-! ### The inner approximation

A monotone sequence of finite unions of *shrunken* enumerated balls, increasing to `U`.
Shrinking is what makes it inner: the engine estimate needs `thickening ε A ⊆ U`, and a ball
shrunk by `ε` thickens back inside the original. -/

section Inner

variable (P)

/-- The stage-`n` inner approximation: the first `n` enumerated balls, each shrunk by `2⁻ⁿ`. -/
noncomputable def innerApprox (u : Baire) (n : ℕ) : Set X :=
  ⋃ k ∈ Finset.range n,
    ball (P.dense (u k).unpair.1) (((ratOfCode (u k).unpair.2 : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ n)

omit [MeasurableSpace X] [BorelSpace X] in
theorem monotone_innerApprox (u : Baire) : Monotone (innerApprox P u) := by
  intro m n hmn x hx
  simp only [innerApprox, Set.mem_iUnion, Finset.mem_range, mem_ball, exists_prop] at hx ⊢
  obtain ⟨k, hk, hdist⟩ := hx
  refine ⟨k, lt_of_lt_of_le hk hmn, ?_⟩
  have hpow : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
theorem iUnion_innerApprox (u : Baire) : ⋃ n, innerApprox P u n = openOf P u := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => ?_) fun x hx => ?_
  · refine Set.iUnion₂_subset fun k _ => ?_
    refine subset_trans (ball_subset_ball (sub_le_self _ (by positivity))) ?_
    rw [openOf]
    exact Set.subset_iUnion
      (fun k => ball (P.dense (u k).unpair.1) (((ratOfCode (u k).unpair.2 : ℚ) : ℝ))) k
  · simp only [openOf, Set.mem_iUnion, mem_ball] at hx
    obtain ⟨k, hdist⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show (0:ℝ) < ((ratOfCode (u k).unpair.2 : ℚ) : ℝ) - dist x (P.dense (u k).unpair.1) by
        linarith) (by norm_num : (2:ℝ)⁻¹ < 1)
    refine Set.mem_iUnion.mpr ⟨max n (k + 1), ?_⟩
    simp only [innerApprox, Set.mem_iUnion, Finset.mem_range, mem_ball, exists_prop]
    refine ⟨k, by omega, ?_⟩
    have hpow : (2 : ℝ)⁻¹ ^ (max n (k + 1)) ≤ (2 : ℝ)⁻¹ ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
    linarith

omit [BorelSpace X] in
/-- The inner approximations exhaust `U` in measure. -/
theorem tendsto_innerApprox (μ : ProbabilityMeasure X) (u : Baire) :
    Filter.Tendsto (fun n => μ.toMeasure (innerApprox P u n)) Filter.atTop
      (nhds (μ.toMeasure (openOf P u))) := by
  have h := tendsto_measure_iUnion_atTop (μ := μ.toMeasure) (monotone_innerApprox P u)
  rwa [iUnion_innerApprox P u] at h

end Inner

/-! ### The two-sided bracket

The even track gives certified lower approximations to `µ U`; the odd track gives lower
approximations to `µ V`, which full mass converts into upper approximations to `µ U`. A stage
search can therefore be driven by the gap between the two bounds, never by an independent
convergence modulus. -/

section Bracket

variable (P)

/-- Lower approximations to `µ U`, from the even track. -/
noncomputable def lowerU (μ : ProbabilityMeasure X) (uv : Baire) (n : ℕ) : ℝ :=
  (μ.toMeasure (innerApprox P uv.evenPart n)).toReal

/-- Lower approximations to `µ V`, from the odd track. -/
noncomputable def lowerV (μ : ProbabilityMeasure X) (uv : Baire) (n : ℕ) : ℝ :=
  (μ.toMeasure (innerApprox P uv.oddPart n)).toReal

variable {P}

omit [BorelSpace X] in
/-- Both tracks converge, so the gap between the bounds closes. -/
theorem tendsto_gap {μ : ProbabilityMeasure X} {uv : Baire} (h : ContinuityOpenNames P μ uv) :
    Filter.Tendsto (fun n => (1 - lowerV P μ uv n) - lowerU P μ uv n) Filter.atTop (nhds 0) := by
  have hU : Filter.Tendsto (lowerU P μ uv) Filter.atTop
      (nhds (μ.toMeasure (openOf P uv.evenPart)).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_innerApprox P μ uv.evenPart)
  have hV : Filter.Tendsto (lowerV P μ uv) Filter.atTop
      (nhds (μ.toMeasure (openOf P uv.oddPart)).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_innerApprox P μ uv.oddPart)
  have hsum : (μ.toMeasure (openOf P uv.evenPart)).toReal
      + (μ.toMeasure (openOf P uv.oddPart)).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h.full, ENNReal.toReal_one]
  have hlim := ((tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℕ))).sub hV).sub hU
  have hzero : (1 : ℝ) - (μ.toMeasure (openOf P uv.oddPart)).toReal
      - (μ.toMeasure (openOf P uv.evenPart)).toReal = 0 := by linarith
  rw [hzero] at hlim
  exact hlim

end Bracket

/-! ### The certified bracket at coupled indices

The code never sees `µ` itself, only its atomic approximants, so the executable endpoints are
atomic masses of inner approximations minus the LP error. The two lemmas below are the two
halves of that bracket; their index-coupling hypotheses are exactly what the thickening
containments need. -/

omit [MeasurableSpace X] [BorelSpace X] in
/-- With the LP error no coarser than the shrink margin, the thickened inner approximation
still sits inside `U`. The hypothesis `n ≤ m` is the index coupling. -/
theorem thickening_innerApprox_subset (u : Baire) {m n : ℕ} (hnm : n ≤ m) :
    thickening ((2 : ℝ)⁻¹ ^ m) (innerApprox P u n) ⊆ openOf P u := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  simp only [innerApprox, Set.mem_iUnion, Finset.mem_range, mem_ball, exists_prop] at hy
  obtain ⟨k, _, hyk⟩ := hy
  have hpow : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
  have hdist : dist x (P.dense (u k).unpair.1) < ((ratOfCode (u k).unpair.2 : ℚ) : ℝ) := by
    have := dist_triangle x y (P.dense (u k).unpair.1)
    linarith
  rw [openOf]
  exact Set.mem_iUnion.mpr ⟨k, mem_ball.mpr hdist⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- The inner approximations thicken into each other, one level at a time: shrinking by
`2⁻⁽ⁿ⁺¹⁾` instead of `2⁻ⁿ` frees exactly `2⁻⁽ⁿ⁺¹⁾` of room, whence the strict coupling
`n < m`. -/
theorem thickening_innerApprox_subset_succ (u : Baire) {m n : ℕ} (hnm : n < m) :
    thickening ((2 : ℝ)⁻¹ ^ m) (innerApprox P u n) ⊆ innerApprox P u (n + 1) := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
  simp only [innerApprox, Set.mem_iUnion, Finset.mem_range, mem_ball, exists_prop] at hy ⊢
  obtain ⟨k, hk, hyk⟩ := hy
  have hpow : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hnm
  have hhalf : (2 : ℝ)⁻¹ ^ (n + 1) + (2 : ℝ)⁻¹ ^ (n + 1) = (2 : ℝ)⁻¹ ^ n := by
    rw [pow_succ]; ring
  refine ⟨k, Nat.lt_succ_of_lt hk, ?_⟩
  have := dist_triangle x y (P.dense (u k).unpair.1)
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- Membership in the stage-`n` inner approximation is a finite disjunction of strict ball
inequalities against dense points, so a presentation's `ltSemidec` can certify it. -/
theorem mem_innerApprox_iff (u : Baire) (n : ℕ) (x : X) :
    x ∈ innerApprox P u n ↔ ∃ k < n,
      dist x (P.dense (u k).unpair.1)
        < ((ratOfCode (u k).unpair.2 : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ n := by
  simp only [innerApprox, Set.mem_iUnion, Finset.mem_range, mem_ball, exists_prop]

omit [MeasurableSpace X] [BorelSpace X] in
theorem isOpen_innerApprox (u : Baire) (n : ℕ) : IsOpen (innerApprox P u n) :=
  isOpen_biUnion fun _ _ => isOpen_ball

theorem measurableSet_innerApprox (u : Baire) (n : ℕ) : MeasurableSet (innerApprox P u n) :=
  (isOpen_innerApprox u n).measurableSet

/-- **The upper half of the bracket.** Reading the level-`(m+1)` atomic approximant on the
stage-`n` inner approximation bounds `µ U` from below up to `2⁻ᵐ`, at coupled indices. -/
theorem atomic_le_of_weakName {μ : ProbabilityMeasure X} {p u : Baire}
    (hp : WeakMeasureNames P p μ) {m n : ℕ} (hnm : n ≤ m) :
    (atomic P (p (m + 1))).toMeasure (innerApprox P u n)
      ≤ μ.toMeasure (openOf P u) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) := by
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
  exact thickening_innerApprox_subset u hnm

/-- **The lower half of the bracket.** The approximant's mass on the next inner approximation
bounds `µ` on the previous one from below up to `2⁻ᵐ`; the level steps up because that is
what buys the thickening room, whence the strict coupling `n < m`. This is what makes the gap
close: exactness of the endpoints says nothing about how much mass they carry. -/
theorem le_atomic_of_weakName {μ : ProbabilityMeasure X} {p u : Baire}
    (hp : WeakMeasureNames P p μ) {m n : ℕ} (hnm : n < m) :
    μ.toMeasure (innerApprox P u n)
      ≤ (atomic P (p (m + 1))).toMeasure (innerApprox P u (n + 1))
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) := by
  have hfin : levyProkhorovEDist μ.toMeasure (atomic P (p (m + 1))).toMeasure ≠ ⊤ := by simp
  have hle : levyProkhorovEDist μ.toMeasure (atomic P (p (m + 1))).toMeasure
      ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (m + 1)) := by
    rw [← ENNReal.ofReal_toReal hfin]
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

end ContinuityOpen

end ComputableAnalysis
