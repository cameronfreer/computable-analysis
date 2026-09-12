/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.NullSphereRadius
import ComputableAnalysis.TypeTwo.Tracks

/-!
# The computed continuity basis

Ackerman–Freer–Roy condition on `µ`-continuity sets drawn from a *computed* `µ`-continuity
basis: about every dense point `tᵢ` and in every dyadic band `(2⁻⁽ᵏ⁺²⁾, 2⁻⁽ᵏ⁺¹⁾)`, a ball
whose sphere is `µ`-null. This module computes that basis from a weak name of `µ` and packages
it as one stream: entry `⟨i, k⟩ + 1` carries a fast Cauchy name of the selected radius together
with the two-track continuity-open name of the ball, and entry `0` is an inert sentinel naming
the empty set, so that every index is a valid entry.

A **right inverse** rides on the basis stream: from the basis and an arbitrary open named by a
stream, it enumerates basis entries (with the sentinel as filler) whose union is exactly that
open, so that opens can be refined by basis entries uniformly and totally. Its certificates
are staged strict-comparison tests read off the presentation; soundness (a firing certificate
names a genuine sub-entry) and completeness (every point of the open is covered by a firing
certificate, inside any prescribed ball) give the union identity.

## Main definitions and results

* `basisSet`, `exists_basisSet_subset` — the basis, semantically.
* `BasisEntrySpec`, `ContinuityBasisNames` — the contract of a basis stream: positivity of
  every radius within its band, the open named by every entry, and continuity of every entry's
  two-track name.
* `exists_continuityBasisCode` — one code computing a basis stream from a weak name.
* `certFires`, `basisChoiceAt`, `exists_certFires`, `exists_certFires_subset`,
  `openOf_eq_iUnion_basisOpen` — the refinement certificates, their soundness and completeness,
  and the union identity.
* `exists_rightInverseCode`, `exists_basisRightInverseCode` — the code enumerating the
  certificates, and the promise-free right-inverse contract: total on every pair of streams,
  and every output satisfies the union identity.
-/

open MeasureTheory Metric Encodable Denumerable
open scoped ENNReal NNReal

namespace ComputableAnalysis

open OracleCode

section ContinuityBasis

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

/-- The set named by basis entry `n`. -/
noncomputable def basisSet (ρ : ℕ → ℕ → ℝ) : ℕ → Set X
  | 0 => ∅
  | (n + 1) => ball (P.dense n.unpair.1) (ρ n.unpair.1 n.unpair.2)

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem basisSet_zero (ρ : ℕ → ℕ → ℝ) : basisSet P ρ 0 = (∅ : Set X) := rfl

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem basisSet_succ (ρ : ℕ → ℕ → ℝ) (n : ℕ) :
    basisSet P ρ (n + 1) = ball (P.dense n.unpair.1) (ρ n.unpair.1 n.unpair.2) := rfl

variable {P}

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Local refinement: the banded balls are a basis.** Every point of every open set lies in an
entry contained in that set. Both band bounds are used — the upper one to fit inside, the lower
one to have room for the density choice. -/
theorem exists_basisSet_subset {ρ : ℕ → ℕ → ℝ}
    (hlo : ∀ i k, (2 : ℝ)⁻¹ ^ (k + 2) < ρ i k)
    (hhi : ∀ i k, ρ i k < (2 : ℝ)⁻¹ ^ (k + 1))
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    ∃ n, x ∈ basisSet P ρ n ∧ basisSet P ρ n ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < ε / 2)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk1 : (2 : ℝ)⁻¹ ^ (k + 1) < ε / 2 := by
    refine lt_of_le_of_lt ?_ hk
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  obtain ⟨i, hi⟩ := P.denseRange.exists_dist_lt x (by positivity : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 2))
  refine ⟨Nat.pair i k + 1, ?_, ?_⟩
  · simp only [basisSet_succ, Nat.unpair_pair, mem_ball]
    exact lt_trans hi (hlo i k)
  · simp only [basisSet_succ, Nat.unpair_pair]
    refine subset_trans (fun y hy => ?_) hball
    have h1 : dist y (P.dense i) < ρ i k := mem_ball.mp hy
    have h2 : dist (P.dense i) x < (2 : ℝ)⁻¹ ^ (k + 2) := by rw [dist_comm]; exact hi
    have h3 : (2 : ℝ)⁻¹ ^ (k + 2) < (2 : ℝ)⁻¹ ^ (k + 1) := by
      have hpos : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 1) := by positivity
      rw [pow_succ]
      linarith
    refine mem_ball.mpr (lt_of_le_of_lt (dist_triangle y (P.dense i) x) ?_)
    have := hhi i k
    linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- A strict margin between centres certifies containment of balls. This is the shape the
right-inverse's certificate produces, and the only way it is consumed. -/
theorem ball_subset_ball_of_dist_add_lt {c c' : X} {r r' : ℝ} (h : dist c c' + r < r') :
    ball c r ⊆ ball c' r' := by
  intro y hy
  have h1 : dist y c < r := mem_ball.mp hy
  have h2 := dist_triangle y c c'
  exact mem_ball.mpr (by linarith)


omit [MeasurableSpace X] [BorelSpace X] in
theorem exists_basisSet_refines_openOf {ρ : ℕ → ℕ → ℝ}
    (hlo : ∀ i k, (2 : ℝ)⁻¹ ^ (k + 2) < ρ i k)
    (hhi : ∀ i k, ρ i k < (2 : ℝ)⁻¹ ^ (k + 1))
    {u : Baire} {x : X} (hx : x ∈ openOf P u) :
    ∃ i k j, x ∈ basisSet P ρ (Nat.pair i k + 1) ∧
      dist (P.dense i) (P.dense (u j).unpair.1) + ρ i k
        < ((ratOfCode (u j).unpair.2 : ℚ) : ℝ) := by
  rw [openOf] at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have hjd : dist x (P.dense (u j).unpair.1) < ((ratOfCode (u j).unpair.2 : ℚ) : ℝ) :=
    mem_ball.mp hj
  set m : ℝ := ((ratOfCode (u j).unpair.2 : ℚ) : ℝ) - dist x (P.dense (u j).unpair.1) with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < m / 2)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk1 : (2 : ℝ)⁻¹ ^ (k + 1) < m / 2 :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk
  obtain ⟨i, hi⟩ := P.denseRange.exists_dist_lt x (by positivity : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 2))
  have hk2 : (2 : ℝ)⁻¹ ^ (k + 2) < (2 : ℝ)⁻¹ ^ (k + 1) := by
    have hpos : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 1) := by positivity
    rw [pow_succ]; linarith
  refine ⟨i, k, j, ?_, ?_⟩
  · simp only [basisSet_succ, Nat.unpair_pair, mem_ball]
    exact lt_trans hi (hlo i k)
  · have htri := dist_triangle (P.dense i) x (P.dense (u j).unpair.1)
    have hix : dist (P.dense i) x < (2 : ℝ)⁻¹ ^ (k + 2) := by rw [dist_comm]; exact hi
    have := hhi i k
    rw [hm] at hk1
    linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Local refinement with a size bound.** The strengthening `exists_certFires_subset` — and
through it the refinement tail of a basis entry — needs the refining entry to be not merely
contained in the ambient open but arbitrarily small around `x`.  The construction already chooses
the level `k` freely, so it suffices to choose it small against `ε` as well as against the margin;
nothing else in the original argument changes. -/
theorem exists_basisSet_refines_openOf_subset {ρ : ℕ → ℕ → ℝ}
    (hlo : ∀ i k, (2 : ℝ)⁻¹ ^ (k + 2) < ρ i k)
    (hhi : ∀ i k, ρ i k < (2 : ℝ)⁻¹ ^ (k + 1))
    {u : Baire} {x : X} (hx : x ∈ openOf P u) {ε : ℝ} (hε : 0 < ε) :
    ∃ i k j, x ∈ basisSet P ρ (Nat.pair i k + 1) ∧
      dist (P.dense i) (P.dense (u j).unpair.1) + ρ i k
        < ((ratOfCode (u j).unpair.2 : ℚ) : ℝ) ∧
      basisSet P ρ (Nat.pair i k + 1) ⊆ ball x ε := by
  rw [openOf] at hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
  have hjd : dist x (P.dense (u j).unpair.1) < ((ratOfCode (u j).unpair.2 : ℚ) : ℝ) :=
    mem_ball.mp hj
  set m : ℝ := ((ratOfCode (u j).unpair.2 : ℚ) : ℝ) - dist x (P.dense (u j).unpair.1) with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (lt_min (by linarith : (0 : ℝ) < m / 2) (by linarith : (0 : ℝ) < ε / 4))
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk1 : (2 : ℝ)⁻¹ ^ (k + 1) < min (m / 2) (ε / 4) :=
    lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) hk
  have hkm : (2 : ℝ)⁻¹ ^ (k + 1) < m / 2 := lt_of_lt_of_le hk1 (min_le_left _ _)
  have hke : (2 : ℝ)⁻¹ ^ (k + 1) < ε / 4 := lt_of_lt_of_le hk1 (min_le_right _ _)
  obtain ⟨i, hi⟩ := P.denseRange.exists_dist_lt x (by positivity : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 2))
  have hk2 : (2 : ℝ)⁻¹ ^ (k + 2) < (2 : ℝ)⁻¹ ^ (k + 1) := by
    have hpos : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 1) := by positivity
    rw [pow_succ]; linarith
  have hix : dist (P.dense i) x < (2 : ℝ)⁻¹ ^ (k + 2) := by rw [dist_comm]; exact hi
  refine ⟨i, k, j, ?_, ?_, ?_⟩
  · simp only [basisSet_succ, Nat.unpair_pair, mem_ball]
    exact lt_trans hi (hlo i k)
  · have htri := dist_triangle (P.dense i) x (P.dense (u j).unpair.1)
    have := hhi i k
    rw [hm] at hkm
    linarith
  · simp only [basisSet_succ, Nat.unpair_pair]
    intro y hy
    have h1 : dist y (P.dense i) < ρ i k := mem_ball.mp hy
    have h3 := hhi i k
    refine mem_ball.mpr (lt_of_le_of_lt (dist_triangle y (P.dense i) x) ?_)
    linarith
variable (P)

/-- **The packed request family.** Track `⟨i, k⟩` asks the selector for a radius about `tᵢ` in
the band `(2⁻⁽ᵏ⁺²⁾, 2⁻⁽ᵏ⁺¹⁾)`. -/
private def basisRequests (p : Baire) : Baire := fun v =>
  radiusPack p v.unpair.1.unpair.1 (halfPowCode (v.unpair.1.unpair.2 + 2))
    (halfPowCode (v.unpair.1.unpair.2 + 1)) v.unpair.2

@[simp] private theorem track_basisRequests (p : Baire) (i k : ℕ) :
    Baire.track (Nat.pair i k) (basisRequests p)
      = radiusPack p i (halfPowCode (k + 2)) (halfPowCode (k + 1)) := by
  funext m
  simp [Baire.track, basisRequests]

theorem basisBand_nonneg (k : ℕ) : (0 : ℝ) ≤ ((ratOfCode (halfPowCode (k + 2)) : ℚ) : ℝ) := by
  rw [ratOfCode_halfPowCode]
  push_cast
  positivity

theorem basisBand_lt (k : ℕ) :
    ((ratOfCode (halfPowCode (k + 2)) : ℚ) : ℝ)
      < ((ratOfCode (halfPowCode (k + 1)) : ℚ) : ℝ) := by
  rw [ratOfCode_halfPowCode, ratOfCode_halfPowCode]
  push_cast
  have hpos : (0:ℝ) < (2 : ℝ)⁻¹ ^ (k + 1) := by positivity
  rw [pow_succ]
  linarith

/-- A name of the empty open: every enumerated ball has radius `0`. -/
def emptyOpenName : Baire := fun _ => Nat.pair 0 zeroCode

/-- A name of the whole space: unit balls about every dense point, which cover by density. -/
def univOpenName : Baire := fun k => Nat.pair k oneCode

variable {P}

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem openOf_emptyOpenName : openOf P emptyOpenName = (∅ : Set X) := by
  rw [openOf]
  refine Set.iUnion_eq_empty.mpr fun k => ?_
  simp [emptyOpenName, ratOfCode_zeroCode]

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem openOf_univOpenName : openOf P univOpenName = (Set.univ : Set X) := by
  rw [openOf]
  refine Set.eq_univ_iff_forall.mpr fun x => ?_
  obtain ⟨i, hi⟩ := P.denseRange.exists_dist_lt x (by norm_num : (0:ℝ) < 1)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  simp only [univOpenName, Nat.unpair_pair, ratOfCode_oneCode]
  simpa using hi

/-- **The sentinel entry's continuity-open name.** Its even track names `∅` and its odd track
names `univ`. The odd track must NOT be empty as well: `ContinuityOpenNames.full` demands the two
masses sum to `1`, so two empty tracks would not be a valid entry at all. -/
private def sentinelOpen : Baire := Baire.interleave emptyOpenName univOpenName

omit [BorelSpace X] in
private theorem contSetNames_sentinelOpen (μ : ProbabilityMeasure X) :
    ContinuityOpenNames P μ sentinelOpen := by
  constructor
  · simp only [sentinelOpen, Baire.evenPart_interleave, Baire.oddPart_interleave,
      openOf_emptyOpenName, openOf_univOpenName]
    exact Set.empty_disjoint _
  · simp only [sentinelOpen, Baire.evenPart_interleave, Baire.oddPart_interleave,
      openOf_emptyOpenName, openOf_univOpenName, measure_empty, measure_univ, zero_add]

/-- The sentinel basis entry: its radius track is inert, its continuity-open track is
`sentinelOpen`. -/
private def sentinelEntry : Baire := Baire.interleave (fun _ => zeroCode) sentinelOpen

@[simp] private theorem oddPart_sentinelEntry : (sentinelEntry : Baire).oddPart = sentinelOpen := by
  rw [sentinelEntry, Baire.oddPart_interleave]

/-- Prepend the sentinel as track `0`, shifting every raw track up by one. -/
def prependSentinel (raw : Baire) : Baire :=
  Baire.packTracks fun n =>
    match n with
    | 0 => sentinelEntry
    | (m + 1) => Baire.track m raw

@[simp] private theorem track_zero_prependSentinel (raw : Baire) :
    Baire.track 0 (prependSentinel raw) = sentinelEntry := by
  rw [prependSentinel, Baire.track_packTracks]

@[simp] private theorem track_succ_prependSentinel (raw : Baire) (n : ℕ) :
    Baire.track (n + 1) (prependSentinel raw) = Baire.track n raw := by
  rw [prependSentinel, Baire.track_packTracks]

variable (P)

theorem exists_radiusAndNameCode {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt)
    (hgtspec : ∀ i j thr, ((ratOfCode thr : ℚ) : ℝ) < dist (P.dense i) (P.dense j)
      ↔ ∃ t, gt (i, j, thr) t = true) :
    ∃ c : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure X) (i : ℕ) (ac bc : RatCode),
      WeakMeasureNames P p μ →
      0 ≤ ((ratOfCode ac : ℚ) : ℝ) →
      ((ratOfCode ac : ℚ) : ℝ) < ((ratOfCode bc : ℚ) : ℝ) →
      ∃ out ∈ c.evalStream (radiusPack p i ac bc), ∃ ρ : ℝ,
        realRep.Names out.evenPart ρ ∧
        ((ratOfCode ac : ℚ) : ℝ) < ρ ∧
        ρ < ((ratOfCode bc : ℚ) : ℝ) ∧
        openOf P out.oddPart.evenPart = ball (P.dense i) ρ ∧
        ContinuityOpenNames P μ out.oddPart := by
  classical
  obtain ⟨S, hS⟩ := exists_radiusSelectorCode P
  obtain ⟨A, hA⟩ := exists_afrRealEvalCode hgt
  refine ⟨OracleCode.pairCode S
      (OracleCode.comp (A.subst S)
        (OracleCode.pair
          (OracleCode.comp OracleCode.left
            (OracleCode.comp OracleCode.query (OracleCode.const 1)))
          OracleCode.id)),
    fun p μ i ac bc hp hac hlt => ?_⟩
  obtain ⟨r, hr, ρ, hnames, hlo, hhi, hsphere⟩ := hS p μ i ac bc hp hac hlt
  set F : Baire := radiusPack p i ac bc with hF
  have hF1 : F 1 = Nat.pair i (Nat.pair ac bc) := by
    rw [hF, radiusPack]; simp [Baire.interleave]
  -- the argument code, structurally
  have hiCode : ∀ n, (OracleCode.comp OracleCode.left
      (OracleCode.comp OracleCode.query (OracleCode.const 1))).eval F n = Part.some i := by
    intro n
    rw [eval_comp_some (eval_comp_some (OracleCode.eval_const F 1 n)), eval_left, hF1,
      Nat.unpair_pair]
  have harg : ∀ n, (OracleCode.pair
      (OracleCode.comp OracleCode.left
        (OracleCode.comp OracleCode.query (OracleCode.const 1))) OracleCode.id).eval F n
      = Part.some (Nat.pair i n) := fun n => eval_pair_some (hiCode n) (eval_id F n)
  -- the selected radius stream becomes the evaluator's oracle
  have hSeval : S.eval F = fun n => Part.some (r n) :=
    funext fun n => Part.eq_some_iff.mpr (OracleCode.mem_evalStream.mp hr n)
  have hafr : afrReal gt r i ∈ (OracleCode.comp (A.subst S)
      (OracleCode.pair
        (OracleCode.comp OracleCode.left
          (OracleCode.comp OracleCode.query (OracleCode.const 1)))
        OracleCode.id)).evalStream F := by
    refine OracleCode.mem_evalStream.mpr fun n => ?_
    rw [eval_comp_some (harg n), eval_subst_of_eval hSeval A, hA r i n]
    exact Part.mem_some _
  refine ⟨Baire.interleave r (afrReal gt r i), OracleCode.pairCode_spec hr hafr, ρ, ?_, hlo, hhi,
    ?_, ?_⟩
  · simpa using hnames
  · simp only [Baire.oddPart_interleave, afrReal, Baire.evenPart_interleave]
    exact openOf_afrEvenReal hnames i
  · simp only [Baire.oddPart_interleave]
    exact (contSetNames_afrReal (P := P) hgtspec hnames i hsphere).2

/-- The radius-approximation read: stage `s` of entry `b`'s radius name. -/
private theorem interleave_radius_read (B u : Baire) (b s : ℕ) :
    (Baire.track b B).evenPart s = Baire.interleave B u (2 * Nat.pair b (2 * s)) := by
  rw [Baire.interleave_even, Baire.evenPart_apply, Baire.track_apply]

/-- The constituent read: the `j`-th enumerated ball of `u`. -/
private theorem interleave_constituent_read (B u : Baire) (j : ℕ) :
    u j = Baire.interleave B u (2 * j + 1) := by
  rw [Baire.interleave_odd]

/-- **The radius-name bridge.** From a `realRep` name of `ρ`, stage `s` yields a coded upper bound
`rₛ + 2⁻ˢ` that brackets `ρ` from above by at most `2 · 2⁻ˢ`. Both inequalities are kept together
deliberately: soundness spends the left one, completeness the right one, and separating them would
duplicate the absolute-value manipulation.

There is no public `realRep`-specific unpacking lemma, so this goes through
`realPresentation.cauchyRep_names_iff`. -/
private theorem radiusUpper_bounds {r : Baire} {ρ : ℝ} (h : realRep.Names r ρ) (s : ℕ) :
    ρ ≤ ((ratOfCode (addCode (r s) (halfPowCode s)) : ℚ) : ℝ) ∧
      ((ratOfCode (addCode (r s) (halfPowCode s)) : ℚ) : ℝ) ≤ ρ + 2 * (2 : ℝ)⁻¹ ^ s := by
  have habs : |((ratOfCode (r s) : ℚ) : ℝ) - ρ| ≤ (2 : ℝ)⁻¹ ^ s := by
    have hd := realPresentation.cauchyRep_names_iff.mp h s
    rwa [Real.dist_eq] at hd
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  have hval : ((ratOfCode (addCode (r s) (halfPowCode s)) : ℚ) : ℝ)
      = ((ratOfCode (r s) : ℚ) : ℝ) + (2 : ℝ)⁻¹ ^ s := by
    rw [ratOfCode_addCode, ratOfCode_halfPowCode]
    push_cast
    ring
  rw [hval]
  exact ⟨by linarith, by linarith⟩

/-- The prefix length covering both reads. -/
private def certBound (b j s : ℕ) : ℕ := max (2 * Nat.pair b (2 * s) + 1) (2 * j + 2)

private theorem lt_certBound_radius (b j s : ℕ) : 2 * Nat.pair b (2 * s) < certBound b j s := by
  simp only [certBound]; omega

private theorem lt_certBound_constituent (b j s : ℕ) : 2 * j + 1 < certBound b j s := by
  simp only [certBound]; omega

/-- The open named by basis entry `b`'s continuity-open track. Track `0` is the sentinel, whose
even open is `∅`; nonzero tracks rewrite through the retained entry equations. -/
def basisOpen (B : Baire) (b : ℕ) : Set X := openOf P (Baire.track b B).oddPart.evenPart

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] theorem basisOpen_zero (raw : Baire) :
    basisOpen P (prependSentinel raw) 0 = (∅ : Set X) := by
  simp only [basisOpen, track_zero_prependSentinel, oddPart_sentinelEntry, sentinelOpen,
    Baire.evenPart_interleave, openOf_emptyOpenName]

/-- **The promise-free entry specification.** Everything certificate soundness, certificate
completeness and the union identity need to know about a basis stream — and nothing else. No
measure and no continuity data: the eventual `ContinuityBasisNames` adds the per-entry
`ContinuityOpenNames` clause on top of this, separately. -/
structure BasisEntrySpec (B : Baire) (ρ : ℕ → ℕ → ℝ) : Prop where
  /-- Track `0` is the sentinel, naming the empty open. -/
  zero : basisOpen P B 0 = (∅ : Set X)
  /-- Each nonzero entry retains a `realRep` name of its radius. -/
  names : ∀ i k, realRep.Names (Baire.track (Nat.pair i k + 1) B).evenPart (ρ i k)
  /-- The radius sits in its band, lower end. -/
  lower : ∀ i k, (2 : ℝ)⁻¹ ^ (k + 2) < ρ i k
  /-- The radius sits in its band, upper end. -/
  upper : ∀ i k, ρ i k < (2 : ℝ)⁻¹ ^ (k + 1)
  /-- Each nonzero entry names its ball. -/
  open_eq : ∀ i k, basisOpen P B (Nat.pair i k + 1) = ball (P.dense i) (ρ i k)

variable {P}

/-- Pack a certificate candidate. -/
private def packCert (b j s t : ℕ) : ℕ := Nat.pair b (Nat.pair j (Nat.pair s t))

/-- The entry index of a candidate. -/
def certB (w : ℕ) : ℕ := w.unpair.1
/-- The constituent index of a candidate. -/
def certJ (w : ℕ) : ℕ := w.unpair.2.unpair.1
/-- The radius-approximation stage of a candidate. -/
private def certS (w : ℕ) : ℕ := w.unpair.2.unpair.2.unpair.1
/-- The semidecision stage of a candidate. -/
private def certT (w : ℕ) : ℕ := w.unpair.2.unpair.2.unpair.2

@[simp] private theorem certB_packCert (b j s t : ℕ) : certB (packCert b j s t) = b := by
  simp [certB, packCert]
@[simp] private theorem certJ_packCert (b j s t : ℕ) : certJ (packCert b j s t) = j := by
  simp [certJ, packCert]
@[simp] private theorem certS_packCert (b j s t : ℕ) : certS (packCert b j s t) = s := by
  simp [certS, packCert]
@[simp] private theorem certT_packCert (b j s t : ℕ) : certT (packCert b j s t) = t := by
  simp [certT, packCert]

/-- **The decoding identity.** On the nonzero branch the decoded pair reconstitutes the entry
index, so no later proof ever sees `b - 1`. -/
theorem pair_decode_succ {b : ℕ} (hb : b ≠ 0) :
    Nat.pair (b - 1).unpair.1 (b - 1).unpair.2 + 1 = b := by
  rw [Nat.pair_unpair]
  omega

variable (P)

/-- The coded upper bound for the basis radius at stage `s`. -/
private def certUpperCode (radiusApprox s : ℕ) : RatCode := addCode radiusApprox (halfPowCode s)

/-- The coded threshold `ltSemidec` is asked about. -/
def certThresholdCode (constituentRadius radiusApprox s : ℕ) : RatCode :=
  subCode constituentRadius (certUpperCode radiusApprox s)

/-- The single denotation lemma the certificate layer needs. -/
theorem ratOfCode_certThresholdCode (cr ra s : ℕ) :
    ((ratOfCode (certThresholdCode cr ra s) : ℚ) : ℝ)
      = ((ratOfCode cr : ℚ) : ℝ) - (((ratOfCode ra : ℚ) : ℝ) + (2 : ℝ)⁻¹ ^ s) := by
  rw [certThresholdCode, certUpperCode, ratOfCode_subCode, ratOfCode_addCode,
    ratOfCode_halfPowCode]
  push_cast
  ring

variable {P}

/-- The full-stream certificate at candidate `w`. The `b = 0` branch is taken first. -/
def certFires (fires : ℕ × ℕ × RatCode → ℕ → Bool) (B u : Baire) (w : ℕ) : Bool :=
  if certB w = 0 then false
  else
    fires ((certB w - 1).unpair.1, (u (certJ w)).unpair.1,
      certThresholdCode (u (certJ w)).unpair.2
        ((Baire.track (certB w) B).evenPart (certS w)) (certS w)) (certT w)

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Soundness at a fixed stage.** A fired certificate certifies containment — an implication,
never an iff: a fixed `t` carries no completeness. -/
theorem certFires_sound {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hsound : ∀ (a : ℕ × ℕ × RatCode) (t : ℕ), fires a t = true →
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ))
    {B u : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) (w : ℕ)
    (hw : certFires fires B u w = true) :
    basisOpen P B (certB w)
      ⊆ ball (P.dense (u (certJ w)).unpair.1) ((ratOfCode (u (certJ w)).unpair.2 : ℚ) : ℝ) := by
  classical
  by_cases hb : certB w = 0
  · rw [certFires, ite_eq_left hb] at hw; exact absurd hw (by simp)
  rw [certFires, ite_eq_right hb] at hw
  set i := (certB w - 1).unpair.1 with hi
  set k := (certB w - 1).unpair.2 with hk
  have hbeq : Nat.pair i k + 1 = certB w := pair_decode_succ hb
  have hdist := hsound _ _ hw
  rw [ratOfCode_certThresholdCode] at hdist
  -- the retained radius name, read at the candidate's stage
  have hnames := hspec.names i k
  rw [hbeq] at hnames
  obtain ⟨hup, -⟩ := radiusUpper_bounds hnames (certS w)
  rw [ratOfCode_addCode, ratOfCode_halfPowCode] at hup
  push_cast at hup
  rw [← hbeq, hspec.open_eq i k]
  refine ball_subset_ball_of_dist_add_lt ?_
  linarith

/-- A fired certificate is never the sentinel: the `b = 0` branch of `certFires` returns `false`
outright.  This is what lets the refinement tail's zero fillers be excluded by a purely syntactic
test downstream. -/
theorem certB_ne_zero_of_certFires {fires : ℕ × ℕ × RatCode → ℕ → Bool} {B u : Baire} {w : ℕ}
    (hw : certFires fires B u w = true) : certB w ≠ 0 := by
  intro h
  rw [certFires, ite_eq_left h] at hw
  exact absurd hw (by simp)

omit [MeasurableSpace X] [BorelSpace X] in
omit [MeasurableSpace X] [BorelSpace X] in
/-- **Completeness, existential in BOTH stages.** The radius approximation forces an existential
in `s`, the semidecision one in `t`. -/
theorem exists_certFires {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true)
    {B u : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) {x : X}
    (hx : x ∈ openOf P u) :
    ∃ w, x ∈ basisOpen P B (certB w) ∧ certFires fires B u w = true := by
  classical
  obtain ⟨i, k, j, hmem, hmargin⟩ :=
    exists_basisSet_refines_openOf (P := P) hspec.lower hspec.upper hx
  have hnames := hspec.names i k
  -- a stage at which twice the approximation error fits inside the retained margin
  set m : ℝ := ((ratOfCode (u j).unpair.2 : ℚ) : ℝ)
    - (dist (P.dense i) (P.dense (u j).unpair.1) + ρ i k) with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < m / 2)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨-, hup⟩ := radiusUpper_bounds hnames s
  rw [ratOfCode_addCode, ratOfCode_halfPowCode] at hup
  push_cast at hup
  -- the coded threshold inequality, then the semidecision stage
  have hthr : dist (P.dense i) (P.dense (u j).unpair.1)
      < ((ratOfCode (certThresholdCode (u j).unpair.2
          ((Baire.track (Nat.pair i k + 1) B).evenPart s) s) : ℚ) : ℝ) := by
    rw [ratOfCode_certThresholdCode]
    rw [hm] at hs
    linarith
  obtain ⟨t, ht⟩ := hcomplete (i, (u j).unpair.1,
    certThresholdCode (u j).unpair.2 ((Baire.track (Nat.pair i k + 1) B).evenPart s) s) hthr
  refine ⟨packCert (Nat.pair i k + 1) j s t, ?_, ?_⟩
  · rw [certB_packCert, hspec.open_eq i k]
    simpa only [basisSet_succ, Nat.unpair_pair] using hmem
  · rw [certFires, certB_packCert, certJ_packCert, certS_packCert, certT_packCert,
      ite_eq_right (by omega), Nat.add_sub_cancel, Nat.unpair_pair]
    exact ht

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Completeness with a size bound.**  The strengthening of `exists_certFires` that the
refinement tail's local cofinality needs: the certified entry can additionally be demanded to sit
inside any prescribed ball about `x`.  Only the choice of level changes; the certificate,
its stages and the fired equation are as before. -/
theorem exists_certFires_subset {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true)
    {B u : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) {x : X}
    (hx : x ∈ openOf P u) {ε : ℝ} (hε : 0 < ε) :
    ∃ w, x ∈ basisOpen P B (certB w) ∧ certFires fires B u w = true ∧
      basisOpen P B (certB w) ⊆ ball x ε := by
  classical
  obtain ⟨i, k, j, hmem, hmargin, hsmall⟩ :=
    exists_basisSet_refines_openOf_subset (P := P) hspec.lower hspec.upper hx hε
  have hnames := hspec.names i k
  set m : ℝ := ((ratOfCode (u j).unpair.2 : ℚ) : ℝ)
    - (dist (P.dense i) (P.dense (u j).unpair.1) + ρ i k) with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < m / 2)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨-, hup⟩ := radiusUpper_bounds hnames s
  rw [ratOfCode_addCode, ratOfCode_halfPowCode] at hup
  push_cast at hup
  have hthr : dist (P.dense i) (P.dense (u j).unpair.1)
      < ((ratOfCode (certThresholdCode (u j).unpair.2
          ((Baire.track (Nat.pair i k + 1) B).evenPart s) s) : ℚ) : ℝ) := by
    rw [ratOfCode_certThresholdCode]
    rw [hm] at hs
    linarith
  obtain ⟨t, ht⟩ := hcomplete (i, (u j).unpair.1,
    certThresholdCode (u j).unpair.2 ((Baire.track (Nat.pair i k + 1) B).evenPart s) s) hthr
  refine ⟨packCert (Nat.pair i k + 1) j s t, ?_, ?_, ?_⟩
  · rw [certB_packCert, hspec.open_eq i k]
    simpa only [basisSet_succ, Nat.unpair_pair] using hmem
  · rw [certFires, certB_packCert, certJ_packCert, certS_packCert, certT_packCert,
      ite_eq_right (by omega), Nat.add_sub_cancel, Nat.unpair_pair]
    exact ht
  · rw [certB_packCert, hspec.open_eq i k]
    simpa only [basisSet_succ, Nat.unpair_pair] using hsmall

/-- **The total choice stream.** At every candidate it emits the certified entry, or the sentinel
index `0` when the certificate has not fired. Total by construction — this is what the empty entry
was introduced for. -/
def basisChoiceAt (fires : ℕ × ℕ × RatCode → ℕ → Bool) (B u : Baire) (w : ℕ) : ℕ :=
  if certFires fires B u w = true then certB w else 0


omit [MeasurableSpace X] [BorelSpace X] in
/-- **The promise-free union identity** — the right inverse's whole content, proved before any
encoding. `⊆` is certificate completeness; `⊇` is certificate soundness together with the
sentinel's empty entry. No measure, no continuity data, no code. -/
theorem openOf_eq_iUnion_basisOpen {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hsound : ∀ (a : ℕ × ℕ × RatCode) (t : ℕ), fires a t = true →
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ))
    (hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true)
    {B u : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) :
    openOf P u = ⋃ w, basisOpen P B (basisChoiceAt fires B u w) := by
  classical
  refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun w => ?_)
  · obtain ⟨w, hmem, hfire⟩ := exists_certFires hcomplete hspec hx
    refine Set.mem_iUnion.mpr ⟨w, ?_⟩
    rwa [basisChoiceAt, ite_eq_left hfire]
  · by_cases hfire : certFires fires B u w = true
    · rw [basisChoiceAt, ite_eq_left hfire]
      refine subset_trans (certFires_sound hsound hspec w hfire) ?_
      rw [openOf]
      exact Set.subset_iUnion
        (fun k => ball (P.dense (u k).unpair.1) (((ratOfCode (u k).unpair.2 : ℚ) : ℝ)))
        (certJ w)
    · rw [basisChoiceAt, ite_eq_right hfire, hspec.zero]
      exact Set.empty_subset _
/-- The certificate over a finite prefix of `Baire.interleave B u`, reading both
positions. -/
private def certFiresPre (fires : ℕ × ℕ × RatCode → ℕ → Bool) (pre : List ℕ) (w : ℕ) : Bool :=
  if certB w = 0 then false
  else
    fires ((certB w - 1).unpair.1, (pre.getD (2 * certJ w + 1) 0).unpair.1,
      certThresholdCode (pre.getD (2 * certJ w + 1) 0).unpair.2
        (pre.getD (2 * Nat.pair (certB w) (2 * certS w)) 0) (certS w)) (certT w)

/-- **Exact-prefix agreement**, from the two lookup inequalities and nothing else. -/
private theorem certFiresPre_eq (fires : ℕ × ℕ × RatCode → ℕ → Bool) (B u : Baire) (w L : ℕ)
    (h1 : 2 * Nat.pair (certB w) (2 * certS w) < L) (h2 : 2 * certJ w + 1 < L) :
    certFiresPre fires (streamTake (Baire.interleave B u) L) w = certFires fires B u w := by
  rw [certFiresPre, certFires]
  by_cases hb : certB w = 0
  · rw [ite_eq_left hb, ite_eq_left hb]
  · rw [ite_eq_right hb, ite_eq_right hb, streamTake_getD _ h1, streamTake_getD _ h2,
      ← interleave_radius_read B u (certB w) (certS w),
      ← interleave_constituent_read B u (certJ w)]

/-- The prefix mirror of the total choice stream. -/
private def basisChoicePre (fires : ℕ × ℕ × RatCode → ℕ → Bool) (pre : List ℕ) (w : ℕ) : ℕ :=
  if certFiresPre fires pre w = true then certB w else 0

private theorem basisChoicePre_eq (fires : ℕ × ℕ × RatCode → ℕ → Bool) (B u : Baire) (w L : ℕ)
    (h1 : 2 * Nat.pair (certB w) (2 * certS w) < L) (h2 : 2 * certJ w + 1 < L) :
    basisChoicePre fires (streamTake (Baire.interleave B u) L) w = basisChoiceAt fires B u w := by
  rw [basisChoicePre, basisChoiceAt, certFiresPre_eq fires B u w L h1 h2]

private theorem primrec_certB : Primrec certB := primrec_unpairFst
private theorem primrec_certJ : Primrec certJ := primrec_unpairFst.comp primrec_unpairSnd
private theorem primrec_certS : Primrec certS :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp primrec_unpairSnd)
private theorem primrec_certT : Primrec certT :=
  primrec_unpairSnd.comp (primrec_unpairSnd.comp primrec_unpairSnd)

private theorem primrec_certFiresPre {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hfires : Primrec₂ fires) :
    Primrec fun z : List ℕ × ℕ => certFiresPre fires z.1 z.2 := by
  have hw : Primrec fun z : List ℕ × ℕ => z.2 := Primrec.snd
  have hcon : Primrec fun z : List ℕ × ℕ => z.1.getD (2 * certJ z.2 + 1) 0 :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (primrec_certJ.comp hw)))
  have hrad : Primrec fun z : List ℕ × ℕ =>
      z.1.getD (2 * Nat.pair (certB z.2) (2 * certS z.2)) 0 :=
    (Primrec.list_getD 0).comp Primrec.fst
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (primrec_certB.comp hw)
          (Primrec.nat_mul.comp (Primrec.const 2) (primrec_certS.comp hw))))
  have hthr : Primrec fun z : List ℕ × ℕ =>
      certThresholdCode (z.1.getD (2 * certJ z.2 + 1) 0).unpair.2
        (z.1.getD (2 * Nat.pair (certB z.2) (2 * certS z.2)) 0) (certS z.2) :=
    primrec₂_subCode.comp (primrec_unpairSnd.comp hcon)
      (primrec₂_addCode.comp hrad (primrec_halfPowCode.comp (primrec_certS.comp hw)))
  have hfire : Primrec fun z : List ℕ × ℕ =>
      fires ((certB z.2 - 1).unpair.1, (z.1.getD (2 * certJ z.2 + 1) 0).unpair.1, _)
        (certT z.2) :=
    hfires.comp
      ((primrec_unpairFst.comp
          (Primrec.nat_sub.comp (primrec_certB.comp hw) (Primrec.const 1))).pair
        ((primrec_unpairFst.comp hcon).pair hthr))
      (primrec_certT.comp hw)
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (primrec_certB.comp hw) (Primrec.const 0))
    (Primrec.const false) hfire

private theorem primrec_basisChoicePre {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hfires : Primrec₂ fires) :
    Primrec fun z : List ℕ × ℕ => basisChoicePre fires z.1 z.2 :=
  Primrec.ite
    (PrimrecRel.comp Primrec.eq (primrec_certFiresPre hfires) (Primrec.const true))
    (primrec_certB.comp Primrec.snd) (Primrec.const 0)

variable (P)

structure ContinuityBasisNames (μ : ProbabilityMeasure X) (B : Baire) (ρ : ℕ → ℕ → ℝ)
    extends BasisEntrySpec P B ρ where
  /-- Every entry's continuity-open track is a valid effective µ-continuity open. -/
  continuity : ∀ b, ContinuityOpenNames P μ (Baire.track b B).oddPart

variable {P}

private def requestG (v : ℕ) : ℕ :=
  if v.unpair.1.unpair.2 % 2 = 0 then
    (Denumerable.ofNat (List ℕ) v.unpair.2).getD (v.unpair.1.unpair.2 / 2) 0
  else
    Nat.pair v.unpair.1.unpair.1.unpair.1
      (Nat.pair (halfPowCode (v.unpair.1.unpair.1.unpair.2 + 2))
        (halfPowCode (v.unpair.1.unpair.1.unpair.2 + 1)))

private theorem requestG_pack (p : Baire) (n : ℕ) :
    requestG (Nat.pair n (encode (streamTake p (n + 1)))) = basisRequests p n := by
  simp only [requestG, Nat.unpair_pair, Denumerable.ofNat_encode, basisRequests, radiusPack,
    Baire.interleave]
  have hle : n.unpair.2 ≤ n := Nat.unpair_right_le n
  by_cases h : n.unpair.2 % 2 = 0
  · rw [ite_eq_left h, ite_eq_left h, streamTake_getD p (by omega : n.unpair.2 / 2 < n + 1)]
  · rw [ite_eq_right h, ite_eq_right h]

private theorem primrec_requestG : Primrec requestG := by
  have hn : Primrec fun v : ℕ => v.unpair.1 := primrec_unpairFst
  have hw : Primrec fun v : ℕ => v.unpair.1.unpair.2 := primrec_unpairSnd.comp hn
  have hk : Primrec fun v : ℕ => v.unpair.1.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp (primrec_unpairFst.comp hn)
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp hw (Primrec.const 2)) (Primrec.const 0))
    ((Primrec.list_getD 0).comp ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd)
      (Primrec.nat_div.comp hw (Primrec.const 2)))
    (Primrec₂.natPair.comp (primrec_unpairFst.comp (primrec_unpairFst.comp hn))
      (Primrec₂.natPair.comp
        (primrec_halfPowCode.comp (Primrec.succ.comp (Primrec.succ.comp hk)))
        (primrec_halfPowCode.comp (Primrec.succ.comp hk))))

/-- **The request code**, with its total coordinate equation. -/
private theorem exists_requestCode :
    ∃ c : OracleCode, ∀ (p : Baire) (n : ℕ), c.eval p n = Part.some (basisRequests p n) := by
  obtain ⟨c, hc⟩ := exists_prefixPostCode (b := fun n _ => n + 1)
    (Primrec.succ.comp Primrec.fst) primrec_requestG
  exact ⟨c, fun p n => by rw [hc p n, requestG_pack p n]⟩

/-- The sentinel entry's values, in closed form. -/
private def sentinelValue (m : ℕ) : ℕ :=
  if m % 2 = 0 then zeroCode
  else if (m / 2) % 2 = 0 then Nat.pair 0 zeroCode else Nat.pair (m / 2 / 2) oneCode

private theorem sentinelEntry_apply (m : ℕ) : sentinelEntry m = sentinelValue m := by
  simp only [sentinelEntry, sentinelOpen, sentinelValue, Baire.interleave, emptyOpenName,
    univOpenName]

private theorem primrec_sentinelValue : Primrec sentinelValue := by
  have hhalf : Primrec fun m : ℕ => m / 2 := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0))
    (Primrec.const zeroCode)
    (Primrec.ite
      (PrimrecRel.comp Primrec.eq (Primrec.nat_mod.comp hhalf (Primrec.const 2))
        (Primrec.const 0))
      (Primrec.const (Nat.pair 0 zeroCode))
      (Primrec₂.natPair.comp (hhalf.comp hhalf) (Primrec.const oneCode)))

private def prependG (v : ℕ) : ℕ :=
  if v.unpair.1.unpair.1 = 0 then sentinelValue v.unpair.1.unpair.2
  else (Denumerable.ofNat (List ℕ) v.unpair.2).getD
    (Nat.pair (v.unpair.1.unpair.1 - 1) v.unpair.1.unpair.2) 0

private theorem prependG_pack (raw : Baire) (n : ℕ) :
    prependG (Nat.pair n (encode (streamTake raw (n + 1)))) = prependSentinel raw n := by
  simp only [prependG, Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h : n.unpair.1 = 0
  · rw [ite_eq_left h, ← sentinelEntry_apply, prependSentinel, Baire.packTracks, h]
  · rw [ite_eq_right h]
    have hlt : Nat.pair (n.unpair.1 - 1) n.unpair.2 < n + 1 := by
      have hp := Nat.pair_lt_pair_left n.unpair.2 (by omega : n.unpair.1 - 1 < n.unpair.1)
      rw [Nat.pair_unpair] at hp
      omega
    rw [streamTake_getD raw hlt, prependSentinel, Baire.packTracks]
    obtain ⟨m, hm⟩ : ∃ m, n.unpair.1 = m + 1 := ⟨n.unpair.1 - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel, Baire.track_apply]

private theorem primrec_prependG : Primrec prependG := by
  have hn : Primrec fun v : ℕ => v.unpair.1 := primrec_unpairFst
  have ha : Primrec fun v : ℕ => v.unpair.1.unpair.1 := primrec_unpairFst.comp hn
  have hb : Primrec fun v : ℕ => v.unpair.1.unpair.2 := primrec_unpairSnd.comp hn
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq ha (Primrec.const 0))
    (primrec_sentinelValue.comp hb)
    ((Primrec.list_getD 0).comp ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd)
      (Primrec₂.natPair.comp (Primrec.nat_sub.comp ha (Primrec.const 1)) hb))

/-- **The prepend code**, with its total coordinate equation. -/
private theorem exists_prependCode :
    ∃ c : OracleCode, ∀ (raw : Baire) (n : ℕ),
      c.eval raw n = Part.some (prependSentinel raw n) := by
  obtain ⟨c, hc⟩ := exists_prefixPostCode (b := fun n _ => n + 1)
    (Primrec.succ.comp Primrec.fst) primrec_prependG
  exact ⟨c, fun raw n => by rw [hc raw n, prependG_pack raw n]⟩

private theorem primrec₂_certBoundOf :
    Primrec₂ fun w _ : ℕ => certBound (certB w) (certJ w) (certS w) := by
  have hb : Primrec fun q : ℕ × ℕ => certB q.1 := primrec_certB.comp Primrec.fst
  have hj : Primrec fun q : ℕ × ℕ => certJ q.1 := primrec_certJ.comp Primrec.fst
  have hs : Primrec fun q : ℕ × ℕ => certS q.1 := primrec_certS.comp Primrec.fst
  have h := Primrec.nat_max.comp
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp hb (Primrec.nat_mul.comp (Primrec.const 2) hs))))
    (Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hj)))
  exact h.of_eq fun _ => rfl

private def rightInvG (fires : ℕ × ℕ × RatCode → ℕ → Bool) (v : ℕ) : ℕ :=
  basisChoicePre fires (Denumerable.ofNat (List ℕ) v.unpair.2) v.unpair.1

private theorem primrec_rightInvG {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hfires : Primrec₂ fires) : Primrec (rightInvG fires) := by
  have h := (primrec_basisChoicePre hfires).comp
    (((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd).pair primrec_unpairFst)
  exact h.of_eq fun _ => rfl

/-- **The right-inverse code and its evaluator equation**, on every raw pair of streams and at
every coordinate. Everything the contract needs follows from this one equation. -/
theorem exists_rightInverseCode {fires : ℕ × ℕ × RatCode → ℕ → Bool} (hfires : Primrec₂ fires) :
    ∃ c : OracleCode, ∀ (B u : Baire) (w : ℕ),
      c.eval (Baire.interleave B u) w = Part.some (basisChoiceAt fires B u w) := by
  obtain ⟨c, hc⟩ := exists_prefixPostCode primrec₂_certBoundOf (primrec_rightInvG hfires)
  refine ⟨c, fun B u w => ?_⟩
  have hval : rightInvG fires (Nat.pair w (encode (streamTake (Baire.interleave B u)
      (certBound (certB w) (certJ w) (certS w))))) = basisChoiceAt fires B u w := by
    simp only [rightInvG, Nat.unpair_pair, Denumerable.ofNat_encode]
    exact basisChoicePre_eq fires B u w _ (lt_certBound_radius _ _ _)
      (lt_certBound_constituent _ _ _)
  rw [hc (Baire.interleave B u) w, hval]

/-- **Global totality**, with no promise of any kind. -/
theorem rightInverse_dom {fires : ℕ × ℕ × RatCode → ℕ → Bool} {c : OracleCode}
    (hc : ∀ (B u : Baire) (w : ℕ),
      c.eval (Baire.interleave B u) w = Part.some (basisChoiceAt fires B u w))
    (B u : Baire) : (c.evalStream (Baire.interleave B u)).Dom :=
  Part.dom_iff_mem.mpr ⟨basisChoiceAt fires B u,
    OracleCode.mem_evalStream.mpr fun w => by rw [hc B u w]; exact Part.mem_some _⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Universal correctness**: every produced output — not merely some output — satisfies the
union identity, because `evalStream` values are unique. -/
theorem rightInverse_union {fires : ℕ × ℕ × RatCode → ℕ → Bool} {c : OracleCode}
    (hc : ∀ (B u : Baire) (w : ℕ),
      c.eval (Baire.interleave B u) w = Part.some (basisChoiceAt fires B u w))
    (hsound : ∀ (a : ℕ × ℕ × RatCode) (t : ℕ), fires a t = true →
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ))
    (hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true)
    {B : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) (u f : Baire)
    (hf : f ∈ c.evalStream (Baire.interleave B u)) :
    openOf P u = ⋃ n, basisOpen P B (f n) := by
  have hfeq : f = basisChoiceAt fires B u := by
    funext w
    have := OracleCode.mem_evalStream.mp hf w
    rw [hc B u w] at this
    exact Part.mem_some_iff.mp this
  rw [hfeq]
  exact openOf_eq_iUnion_basisOpen hsound hcomplete hspec

variable (P)
/-- **The basis compiler.** One code; every weak name. -/
theorem exists_continuityBasisCode :
    ∃ basisCode : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure X), WeakMeasureNames P p μ →
      ∃ B ∈ basisCode.evalStream p, ∃ ρ : ℕ → ℕ → ℝ, ContinuityBasisNames P μ B ρ := by
  classical
  obtain ⟨gt, hgtprim, hgtspec⟩ := exists_distGtCert P
  obtain ⟨radiusCode, hradius⟩ := exists_radiusAndNameCode P hgtprim hgtspec
  obtain ⟨requestCode, hrequest⟩ := exists_requestCode
  obtain ⟨prependCode, hprepend⟩ := exists_prependCode
  refine ⟨prependCode.subst ((OracleCode.mapTracks radiusCode).subst requestCode),
    fun p μ hp => ?_⟩
  -- the ONLY classical step: one valid output and radius per track
  choose out hout ρ hnames hlo hhi hball hcont using fun i k =>
    hradius p μ i (halfPowCode (k + 2)) (halfPowCode (k + 1)) hp
      (basisBand_nonneg k) (basisBand_lt k)
  set raw : Baire := Baire.packTracks fun v => out v.unpair.1 v.unpair.2 with hraw
  have htrack_raw : ∀ i k, Baire.track (Nat.pair i k) raw = out i k := by
    intro i k
    rw [hraw, Baire.track_packTracks, Nat.unpair_pair]
  -- transport, through memberships only
  have hreqmem : basisRequests p ∈ requestCode.evalStream p :=
    OracleCode.mem_evalStream.mpr fun n => by rw [hrequest p n]; exact Part.mem_some _
  have hrawmem : raw ∈ (OracleCode.mapTracks radiusCode).evalStream (basisRequests p) := by
    refine OracleCode.evalStream_mapTracks_iff.mpr fun t => ?_
    have ht : Nat.pair t.unpair.1 t.unpair.2 = t := Nat.pair_unpair t
    rw [← ht, htrack_raw, track_basisRequests]
    exact hout t.unpair.1 t.unpair.2
  have hrawmem' : raw ∈ ((OracleCode.mapTracks radiusCode).subst requestCode).evalStream p := by
    rw [OracleCode.evalStream_subst hreqmem]; exact hrawmem
  have hBmem : prependSentinel raw
      ∈ (prependCode.subst
        ((OracleCode.mapTracks radiusCode).subst requestCode)).evalStream p := by
    rw [OracleCode.evalStream_subst hrawmem']
    exact OracleCode.mem_evalStream.mpr fun n => by rw [hprepend raw n]; exact Part.mem_some _
  have hentry : ∀ i k, Baire.track (Nat.pair i k + 1) (prependSentinel raw) = out i k := by
    intro i k
    rw [track_succ_prependSentinel, htrack_raw]
  have hspec : BasisEntrySpec P (prependSentinel raw) ρ := by
    refine ⟨basisOpen_zero P raw, fun i k => ?_, fun i k => ?_, fun i k => ?_, fun i k => ?_⟩
    · rw [hentry i k]; exact hnames i k
    · have hb := hlo i k
      rw [ratOfCode_halfPowCode] at hb
      push_cast at hb
      exact hb
    · have hb := hhi i k
      rw [ratOfCode_halfPowCode] at hb
      push_cast at hb
      exact hb
    · rw [basisOpen, hentry i k]; exact hball i k
  refine ⟨prependSentinel raw, hBmem, ρ, hspec, fun b => ?_⟩
  match b with
  | 0 =>
    rw [track_zero_prependSentinel, oddPart_sentinelEntry]
    exact contSetNames_sentinelOpen μ
  | (n + 1) =>
    have ht : Nat.pair n.unpair.1 n.unpair.2 = n := Nat.pair_unpair n
    rw [track_succ_prependSentinel, ← ht, htrack_raw]
    exact hcont n.unpair.1 n.unpair.2


omit [MeasurableSpace X] [BorelSpace X] in
/-- **The right-inverse compiler.** It needs NO measure and NO `ContinuityBasisNames` — only
`BasisEntrySpec`. Totality holds for every raw pair of streams, with no promise at all. -/
theorem exists_basisRightInverseCode :
    ∃ H : OracleCode,
      (∀ B u : Baire, (H.evalStream (Baire.interleave B u)).Dom) ∧
      ∀ (B : Baire) (ρ : ℕ → ℕ → ℝ), BasisEntrySpec P B ρ →
        ∀ u f : Baire, f ∈ H.evalStream (Baire.interleave B u) →
          openOf P u = ⋃ n, basisOpen P B (f n) := by
  classical
  obtain ⟨fires, hfiresprim, hfiresiff⟩ := repred_exists_primrec_stages P.ltSemidec
  obtain ⟨H, hH⟩ := exists_rightInverseCode hfiresprim
  exact ⟨H, fun B u => rightInverse_dom hH B u, fun B ρ hspec u f hf =>
    rightInverse_union hH (fun a t hat => (hfiresiff a).mpr ⟨t, hat⟩)
      (fun a ha => (hfiresiff a).mp ha) hspec u f hf⟩

end ContinuityBasis

end ComputableAnalysis
