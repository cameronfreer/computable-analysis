/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.ContinuityOpenMass
import ComputableAnalysis.Measure.ContinuityOpenBall
import ComputableAnalysis.TypeTwo.Universal

/-!
# Radii with null spheres, effectively

Every probability measure on a metric space has, about every point and inside every interval
of radii, a radius whose sphere is null: the annuli between countably many radii are disjoint,
so all but countably many are null. This module makes that effective. From a weak name of `µ`,
a centre index and a coded interval, one fixed oracle code emits a fast Cauchy name of a radius
in the interval whose sphere is `µ`-null.

The construction is a nest of closed annuli: each step finds, inside the current interval, a
subinterval at most half as wide whose closed annulus has certified small mass, and the limit
radius has null sphere because the sphere sits inside every annulus of the nest. The step is a
search over candidate endpoint pairs, certifying the annulus mass from above through the
certified masks of the effective ball names; the nest iterates the step and the selector reads
the limit off the shrinking endpoints.

## Main definitions and results

* `annulus`, `exists_thin_annulus`, `exists_subinterval`, `exists_interiorSubinterval` — the
  counting engine and the subdivision step.
* `nest_exists_limit`, `nest_sphere_null`, `nest_names` — the nest's invariants.
* `ThinClosedAnnulusStep`, `exists_stepCode` — the single-step search, one code for every
  measure and request.
* `IsNestRun`, `exists_nestCode` — the iterator.
* `exists_radiusSelectorCode` — the selector: one code, every measure, centre and coded
  interval, one `realRep` name out.

## Implementation notes

Requests and witnesses are packed naturals with named projections, and every rational the
search compares is a code, so the tests are primitive recursive. The upper-bound sequence the
search consults is not required to be monotone: it needs only soundness of every computed
value and eventual certification below any slack.
-/

open MeasureTheory Metric Encodable Denumerable
open scoped ENNReal NNReal

set_option linter.style.longFile 1800

namespace ComputableAnalysis

open OracleCode

section NullSphereRadius

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The half-open annulus about `t` between two radii. -/
def annulus (t : X) (a b : ℝ) : Set X := {x | a ≤ dist x t ∧ dist x t < b}

theorem measurableSet_annulus (t : X) (a b : ℝ) : MeasurableSet (annulus t a b) := by
  have hcont : Continuous fun x : X => dist x t := continuous_id.dist continuous_const
  exact (measurableSet_le measurable_const hcont.measurable).inter
    (measurableSet_lt hcont.measurable measurable_const)

omit [MeasurableSpace X] [BorelSpace X] in
theorem annulus_disjoint {t : X} {ρ : ℕ → ℝ} (hmono : Monotone ρ) {j k : ℕ} (hjk : j < k) :
    Disjoint (annulus t (ρ j) (ρ (j + 1))) (annulus t (ρ k) (ρ (k + 1))) := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have h1 : dist x t < ρ (j + 1) := hx.2
  have h2 : ρ k ≤ dist x t := hx'.1
  have h3 : ρ (j + 1) ≤ ρ k := hmono (by omega)
  exact absurd h1 (not_lt.mpr (le_trans h3 h2))

/-- **The counting lemma.** Among `N` consecutive annuli about a common centre, one has mass at
most `1 / N`: the annuli are disjoint, so their masses sum to at most the total mass. Stated on
real-valued masses, since `ℝ≥0∞` is not cancellative and the pigeonhole step needs that. -/
theorem exists_thin_annulus (μ : ProbabilityMeasure X) (t : X) {ρ : ℕ → ℝ}
    (hmono : Monotone ρ) {N : ℕ} (hN : 0 < N) :
    ∃ j < N, (μ.toMeasure (annulus t (ρ j) (ρ (j + 1)))).toReal ≤ (N : ℝ)⁻¹ := by
  have hsumE : ∑ j ∈ Finset.range N, μ.toMeasure (annulus t (ρ j) (ρ (j + 1))) ≤ 1 := by
    rw [← measure_biUnion_finset
      (fun j _ k _ hjk => by
        rcases lt_or_gt_of_ne hjk with h | h
        · exact annulus_disjoint hmono h
        · exact (annulus_disjoint hmono h).symm)
      (fun j _ => measurableSet_annulus t (ρ j) (ρ (j + 1)))]
    exact prob_le_one
  have hsumR : ∑ j ∈ Finset.range N,
      (μ.toMeasure (annulus t (ρ j) (ρ (j + 1)))).toReal ≤ 1 := by
    rw [← ENNReal.toReal_sum fun j _ => measure_ne_top _ _]
    simpa using ENNReal.toReal_mono (by simp) hsumE
  have hconst : ∑ _j ∈ Finset.range N, (N : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_inv_cancel₀ (by positivity : (N : ℝ) ≠ 0)]
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr hN.ne') (hsumR.trans hconst.ge)
  exact ⟨j, Finset.mem_range.mp hj, hle⟩

/-- A modulus always exists: some `N` beats any positive slack. -/
theorem exists_nat_inv_lt {ε : ℝ} (hε : 0 < ε) : ∃ N : ℕ, 0 < N ∧ (N : ℝ)⁻¹ < ε := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  exact ⟨N + 1, Nat.succ_pos N, by simpa [one_div] using hN⟩

/-- **The searchable form.** With slack, the pigeonhole bound becomes a strict inequality —
the shape an effective search can actually test. -/
theorem exists_thin_annulus_lt (μ : ProbabilityMeasure X) (t : X) {ρ : ℕ → ℝ}
    (hmono : Monotone ρ) {ε : ℝ} {N : ℕ} (hN : 0 < N) (hNε : (N : ℝ)⁻¹ < ε) :
    ∃ j < N, (μ.toMeasure (annulus t (ρ j) (ρ (j + 1)))).toReal < ε := by
  obtain ⟨j, hj, hle⟩ := exists_thin_annulus μ t hmono hN
  exact ⟨j, hj, lt_of_le_of_lt hle hNε⟩

variable (P : ComputableMetricPresentation X)
/-- **One subdivision step.** Inside any interval of radii there is a strictly smaller
subinterval, at most half as wide, whose annulus is strictly thin. This is the step the nest
iterates; the halving gives the shrinking modulus the nest needs. -/
theorem exists_subinterval (μ : ProbabilityMeasure X) (t : X) {a b : ℝ} (hab : a < b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a' b', a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ b' - a' ≤ (b - a) / 2 ∧
      (μ.toMeasure (annulus t a' b')).toReal < ε := by
  obtain ⟨N₀, hN₀pos, hN₀⟩ := exists_nat_inv_lt hε
  set N := max N₀ 2 with hN
  have hNpos : 0 < N := lt_of_lt_of_le hN₀pos (le_max_left _ _)
  have hN2 : 2 ≤ N := le_max_right _ _
  have hN₀r : (0 : ℝ) < N₀ := by exact_mod_cast hN₀pos
  have hNle : (N₀ : ℝ) ≤ N := by exact_mod_cast le_max_left _ _
  have hNε : (N : ℝ)⁻¹ < ε := by
    refine lt_of_le_of_lt ?_ hN₀
    gcongr
  have hwidth : 0 < (b - a) / N := by
    have : (0 : ℝ) < N := by exact_mod_cast hNpos
    positivity
  set ρ : ℕ → ℝ := fun j => a + j * ((b - a) / N) with hρ
  have hmono : Monotone ρ := fun i j hij => by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only [hρ]
    nlinarith [hwidth]
  obtain ⟨j, hjN, hthin⟩ := exists_thin_annulus_lt μ t hmono hNpos hNε
  refine ⟨ρ j, ρ (j + 1), ?_, ?_, ?_, ?_, hthin⟩
  · have : ρ 0 ≤ ρ j := hmono (Nat.zero_le j)
    simpa [hρ] using this
  · have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    simp only [hρ, hcast]
    nlinarith [hwidth]
  · have hle : ρ (j + 1) ≤ ρ N := hmono hjN
    have hNr0 : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hρN : ρ N = b := by
      simp only [hρ]
      rw [mul_div_cancel₀ _ (ne_of_gt hNr0)]
      ring
    rwa [hρN] at hle
  · have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hstep : (b - a) / (N : ℝ) ≤ (b - a) / 2 := by gcongr
    simp only [hρ, hcast]
    nlinarith [hstep]

/-- The closed annulus: what the nest certifies, and what traps the limiting sphere. -/
def closedAnnulus (t : X) (a b : ℝ) : Set X := {x | a ≤ dist x t ∧ dist x t ≤ b}

omit [MeasurableSpace X] [BorelSpace X] in
/-- A strictly interior closed annulus sits inside its half-open parent — the bridge that lets
the counting lemma, stated for half-open annuli, certify closed ones. -/
theorem closedAnnulus_subset_annulus {t : X} {a a' b b' : ℝ} (hle : a ≤ a') (hlt : b' < b) :
    closedAnnulus t a' b' ⊆ annulus t a b :=
  fun _ hx => ⟨le_trans hle hx.1, lt_of_le_of_lt hx.2 hlt⟩

omit [MeasurableSpace X] [BorelSpace X] in
theorem closedAnnulus_eq_compl_union (t : X) (a b : ℝ) :
    closedAnnulus t a b = (ball t a ∪ {x | b < dist x t})ᶜ := by
  ext x
  simp only [closedAnnulus, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, mem_ball,
    not_or, not_lt]

/-- **The one-complement mass formula.** The quantity the single-step search must bound is a
single complement of a sum of two OPEN-set masses — both lower semicomputable from a weak name,
so the bound decreases and the strict test needs no negative information. Stated on `toReal` and
as one subtraction, deliberately: two nested `ℝ≥0∞` subtractions would carry `tsub`
associativity obligations that buy nothing. -/
theorem toReal_measure_closedAnnulus (μ : ProbabilityMeasure X) (t : X) {a b : ℝ} (hab : a ≤ b) :
    (μ.toMeasure (closedAnnulus t a b)).toReal
      = 1 - ((μ.toMeasure (ball t a)).toReal
        + (μ.toMeasure {x : X | b < dist x t}).toReal) := by
  have hVopen : IsOpen {x : X | b < dist x t} :=
    isOpen_lt continuous_const (continuous_id.dist continuous_const)
  have hdisj : Disjoint (ball t a) {x : X | b < dist x t} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : dist x t < a := mem_ball.mp hx
    have h2 : b < dist x t := hx'
    linarith
  have hsum : μ.toMeasure (ball t a ∪ {x : X | b < dist x t})
      + μ.toMeasure (ball t a ∪ {x : X | b < dist x t})ᶜ = 1 := by
    rw [measure_add_measure_compl (isOpen_ball.union hVopen).measurableSet, measure_univ]
  rw [measure_union hdisj hVopen.measurableSet] at hsum
  have h := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ENNReal.toReal_one] at h
  rw [closedAnnulus_eq_compl_union]
  linarith

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Invariant: the limiting sphere lies in every selected annulus.** -/
theorem sphere_subset_closedAnnulus {t : X} {a b ρ : ℝ} (h1 : a ≤ ρ) (h2 : ρ ≤ b) :
    sphere t ρ ⊆ closedAnnulus t a b :=
  fun x hx => ⟨by rw [show dist x t = ρ from hx]; exact h1,
    by rw [show dist x t = ρ from hx]; exact h2⟩

/-- **The strictly interior thin step — the TERMINATION ingredient, and the only classical one.**
Inside any interval there is a strictly interior subinterval, at most half as wide, whose CLOSED
annulus is strictly thin. The index it selects never reaches the executable path: the layers
below take the resulting sequence as a parameter rather than building it from this theorem. -/
theorem exists_interiorSubinterval (μ : ProbabilityMeasure X) (t : X) {a b : ℝ} (hab : a < b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a' b', a < a' ∧ a' < b' ∧ b' < b ∧ b' - a' ≤ (b - a) / 2 ∧
      (μ.toMeasure (closedAnnulus t a' b')).toReal < ε := by
  obtain ⟨a₀, b₀, ha₀, hab₀, hb₀, hw, hthin⟩ := exists_subinterval μ t hab hε
  have hw₀ : 0 < b₀ - a₀ := by linarith
  refine ⟨a₀ + (b₀ - a₀) / 4, b₀ - (b₀ - a₀) / 4, by linarith, by linarith, by linarith,
    by linarith, ?_⟩
  refine lt_of_le_of_lt ?_ hthin
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  exact closedAnnulus_subset_annulus (by linarith) (by linarith)

variable {P}

/-- **Invariant: nested containment and strict nonemptiness give a limit radius**, interior to
the original interval. Nothing here mentions a measure or a selector. -/
theorem nest_exists_limit {a b : ℕ → ℝ} (hstepa : ∀ n, a n < a (n + 1))
    (hstepb : ∀ n, b (n + 1) < b n) (hlt : ∀ n, a n < b n) :
    ∃ ρ : ℝ, (∀ n, a n ≤ ρ) ∧ (∀ n, ρ ≤ b n) ∧ a 0 < ρ ∧ ρ < b 0 := by
  have hamono : Monotone a := monotone_nat_of_le_succ fun n => (hstepa n).le
  have hbanti : Antitone b := antitone_nat_of_succ_le fun n => (hstepb n).le
  have hab : ∀ m n : ℕ, a m ≤ b n := by
    intro m n
    rcases le_total m n with h | h
    · exact le_trans (hamono h) (hlt n).le
    · exact le_trans (hlt m).le (hbanti h)
  have hbdd : BddAbove (Set.range a) := ⟨b 0, by rintro x ⟨n, rfl⟩; exact hab n 0⟩
  refine ⟨sSup (Set.range a), fun n => le_csSup hbdd ⟨n, rfl⟩, fun n => ?_, ?_, ?_⟩
  · exact csSup_le (Set.range_nonempty a) (by rintro x ⟨m, rfl⟩; exact hab m n)
  · exact lt_of_lt_of_le (hstepa 0) (le_csSup hbdd ⟨1, rfl⟩)
  · exact lt_of_le_of_lt (csSup_le (Set.range_nonempty a) (by rintro x ⟨m, rfl⟩; exact hab m 1))
      (hstepb 0)

omit [BorelSpace X] in
/-- **Invariant: the mass of the limiting sphere is zero**, because the certified annulus bounds
tend to zero. The only measure-theoretic content of the nest. -/
theorem nest_sphere_null {μ : ProbabilityMeasure X} {t : X} {a b : ℕ → ℝ} {ε : ℕ → ℝ} {ρ : ℝ}
    (hρa : ∀ n, a n ≤ ρ) (hρb : ∀ n, ρ ≤ b n)
    (hthin : ∀ n, (μ.toMeasure (closedAnnulus t (a n) (b n))).toReal ≤ ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    μ.toMeasure (sphere t ρ) = 0 := by
  have hle : ∀ n, (μ.toMeasure (sphere t ρ)).toReal ≤ ε n := fun n =>
    le_trans (ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (sphere_subset_closedAnnulus (hρa n) (hρb n)))) (hthin n)
  have hzero : (μ.toMeasure (sphere t ρ)).toReal ≤ 0 :=
    ge_of_tendsto' hε hle
  have hnonneg : (0 : ℝ) ≤ (μ.toMeasure (sphere t ρ)).toReal := ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hzero hnonneg) with h | h
  · exact h
  · exact absurd h (measure_ne_top _ _)

/-- **Invariant: the approximants satisfy the fast-Cauchy naming rate.** The left endpoints ARE
the `realRep` name once the widths beat `2⁻ⁿ`; no extra approximation step is needed. -/
theorem nest_names {r : Baire} {a b : ℕ → ℝ} {ρ : ℝ}
    (hr : ∀ n, ((ratOfCode (r n) : ℚ) : ℝ) = a n)
    (hρa : ∀ n, a n ≤ ρ) (hρb : ∀ n, ρ ≤ b n)
    (hwidth : ∀ n, b n - a n ≤ (2 : ℝ)⁻¹ ^ n) :
    realRep.Names r ρ := by
  refine realPresentation.cauchyRep_names_iff.mpr fun n => ?_
  have hval : realPresentation.dense (r n) = a n := hr n
  rw [show dist (realPresentation.dense (r n)) ρ = |a n - ρ| by rw [Real.dist_eq, hval]]
  rw [abs_of_nonpos (by linarith [hρa n])]
  linarith [hρb n, hwidth n]

variable (P)

/-- The selector's input packing: the weak measure name on the even track, the centre and the
two coded interval endpoints on every odd coordinate. -/
def radiusPack (p : Baire) (i : ℕ) (ac bc : RatCode) : Baire :=
  Baire.interleave p fun _ => Nat.pair i (Nat.pair ac bc)

/-- The centre index of a request. -/
def reqCentre (r : ℕ) : ℕ := r.unpair.1

/-- The coded lower endpoint of a request. -/
def reqLo (r : ℕ) : RatCode := r.unpair.2.unpair.1

/-- The coded upper endpoint of a request. -/
def reqHi (r : ℕ) : RatCode := r.unpair.2.unpair.2.unpair.1

/-- The coded target error of a request. -/
def reqErr (r : ℕ) : RatCode := r.unpair.2.unpair.2.unpair.2

/-- The coded lower endpoint of a result. -/
def resLo (v : ℕ) : RatCode := v.unpair.1

/-- The coded upper endpoint of a result. -/
def resHi (v : ℕ) : RatCode := v.unpair.2

/-- A request is valid when its interval is nonempty and its target error is positive. Both are
promises on the INPUT; neither is a side condition on any definition. -/
def ValidIntervalRequest (r : ℕ) : Prop :=
  ((ratOfCode (reqLo r) : ℚ) : ℝ) < ((ratOfCode (reqHi r) : ℚ) : ℝ) ∧
    (0 : ℝ) < ((ratOfCode (reqErr r) : ℚ) : ℝ)

/-- **The step contract.** Strict interior containment, width reduction, and the certified
closed-annulus mass bound. Deliberately silent about how the result was found. -/
def ThinClosedAnnulusStep (μ : ProbabilityMeasure X) (request result : ℕ) : Prop :=
  ((ratOfCode (reqLo request) : ℚ) : ℝ) < ((ratOfCode (resLo result) : ℚ) : ℝ) ∧
    ((ratOfCode (resLo result) : ℚ) : ℝ) < ((ratOfCode (resHi result) : ℚ) : ℝ) ∧
    ((ratOfCode (resHi result) : ℚ) : ℝ) < ((ratOfCode (reqHi request) : ℚ) : ℝ) ∧
    ((ratOfCode (resHi result) : ℚ) : ℝ) - ((ratOfCode (resLo result) : ℚ) : ℝ)
      ≤ (((ratOfCode (reqHi request) : ℚ) : ℝ) - ((ratOfCode (reqLo request) : ℚ) : ℝ)) / 2 ∧
    (μ.toMeasure (closedAnnulus (P.dense (reqCentre request))
        ((ratOfCode (resLo result) : ℚ) : ℝ)
        ((ratOfCode (resHi result) : ℚ) : ℝ))).toReal
      < ((ratOfCode (reqErr request) : ℚ) : ℝ)

/-- **The stagewise certified lower bound** for the mass of the open set named by `u`: the
level-`(m+1)` atomic approximant read on the stage-`n` inner approximation, less `2⁻ᵐ`. -/
noncomputable def openLower (p u : Baire) (n m : ℕ) : ℝ :=
  ((atomic P (p (m + 1))).toMeasure (innerApprox P u n)).toReal - (2 : ℝ)⁻¹ ^ m

variable {P}

/-- **Soundness of the lower bound.** Every computed value really is below the mass. -/
theorem openLower_le {μ : ProbabilityMeasure X} {p u : Baire} (hp : WeakMeasureNames P p μ)
    {n m : ℕ} (hnm : n ≤ m) :
    openLower P p u n m ≤ (μ.toMeasure (openOf P u)).toReal := by
  have h := atomic_le_of_weakName hp (u := u) hnm
  have h' := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) h
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2 : ℝ)⁻¹ ^ m)] at h'
  simp only [openLower]
  linarith

/-- **Eventual slack.** For every slack above the true mass, some stage's bound falls within it.
No monotonicity is claimed or used. -/
theorem exists_openLower_gt {μ : ProbabilityMeasure X} {p : Baire} (hp : WeakMeasureNames P p μ)
    (u : Baire) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n m : ℕ, n ≤ m ∧ (μ.toMeasure (openOf P u)).toReal - δ < openLower P p u n m := by
  have hR : Filter.Tendsto (fun n => (μ.toMeasure (innerApprox P u n)).toReal) Filter.atTop
      (nhds (μ.toMeasure (openOf P u)).toReal) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_innerApprox P μ u)
  obtain ⟨N, hN⟩ := ((tendsto_order.1 hR).1 _
    (show (μ.toMeasure (openOf P u)).toReal - δ / 2 < (μ.toMeasure (openOf P u)).toReal by
      linarith)).exists
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < δ / 4)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N + 1, max m₀ (N + 1), by omega, ?_⟩
  set m := max m₀ (N + 1) with hm
  have hpow : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ m₀ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have hstep := le_atomic_of_weakName hp (u := u) (m := m) (n := N) (by omega)
  have hstep' := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩) hstep
  rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2 : ℝ)⁻¹ ^ m)] at hstep'
  simp only [openLower]
  linarith

variable (P)

/-- **The stagewise upper bound for the closed annulus**: one complement of a sum of two
lower bounds, with independent stages on the two tracks. -/
noncomputable def annulusUpper (p uin ufar : Baire) (n₁ m₁ n₂ m₂ : ℕ) : ℝ :=
  1 - (openLower P p uin n₁ m₁ + openLower P p ufar n₂ m₂)

variable {P}

/-- **Soundness of the upper bound.** The closed-annulus mass is at most every computed value. -/
theorem annulusUpper_sound {μ : ProbabilityMeasure X} {p uin ufar : Baire} {t : X} {a b : ℝ}
    (hp : WeakMeasureNames P p μ) (hin : openOf P uin = ball t a)
    (hfar : openOf P ufar = {x : X | b < dist x t}) (hab : a ≤ b)
    {n₁ m₁ n₂ m₂ : ℕ} (h₁ : n₁ ≤ m₁) (h₂ : n₂ ≤ m₂) :
    (μ.toMeasure (closedAnnulus t a b)).toReal ≤ annulusUpper P p uin ufar n₁ m₁ n₂ m₂ := by
  have hL1 := openLower_le hp (u := uin) h₁
  have hL2 := openLower_le hp (u := ufar) h₂
  rw [hin] at hL1
  rw [hfar] at hL2
  rw [toReal_measure_closedAnnulus μ t hab]
  simp only [annulusUpper]
  linarith

/-- **Eventual slack for the upper bound.** If the true mass is below `ε`, some stage certifies
it. The two tracks are given independent stages, so nothing has to be synchronized. -/
theorem exists_annulusUpper_lt {μ : ProbabilityMeasure X} {p uin ufar : Baire} {t : X} {a b : ℝ}
    (hp : WeakMeasureNames P p μ) (hin : openOf P uin = ball t a)
    (hfar : openOf P ufar = {x : X | b < dist x t}) (hab : a ≤ b) {ε : ℝ}
    (hlt : (μ.toMeasure (closedAnnulus t a b)).toReal < ε) :
    ∃ n₁ m₁ n₂ m₂ : ℕ, n₁ ≤ m₁ ∧ n₂ ≤ m₂ ∧
      annulusUpper P p uin ufar n₁ m₁ n₂ m₂ < ε := by
  set δ := (ε - (μ.toMeasure (closedAnnulus t a b)).toReal) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  obtain ⟨n₁, m₁, h₁, hb₁⟩ := exists_openLower_gt hp uin hδ
  obtain ⟨n₂, m₂, h₂, hb₂⟩ := exists_openLower_gt hp ufar hδ
  rw [hin] at hb₁
  rw [hfar] at hb₂
  refine ⟨n₁, m₁, n₂, m₂, h₁, h₂, ?_⟩
  have hmass := toReal_measure_closedAnnulus μ t hab
  simp only [annulusUpper]
  rw [hδdef] at hb₁ hb₂
  linarith

variable (P)

/-- The candidate's lower endpoint code. -/
def witLo (w : ℕ) : RatCode := w.unpair.1.unpair.1

/-- The candidate's upper endpoint code. -/
def witHi (w : ℕ) : RatCode := w.unpair.1.unpair.2

/-- Inner-approximation stage for the inner track. -/
def witN₁ (w : ℕ) : ℕ := w.unpair.2.unpair.1.unpair.1

/-- Weak-name level for the inner track. -/
def witM₁ (w : ℕ) : ℕ := w.unpair.2.unpair.1.unpair.2.unpair.1

/-- Mask fuel for the inner track. -/
def witT₁ (w : ℕ) : ℕ := w.unpair.2.unpair.1.unpair.2.unpair.2

/-- Inner-approximation stage for the far track. -/
def witN₂ (w : ℕ) : ℕ := w.unpair.2.unpair.2.unpair.1

/-- Weak-name level for the far track. -/
def witM₂ (w : ℕ) : ℕ := w.unpair.2.unpair.2.unpair.2.unpair.1

/-- Mask fuel for the far track. -/
def witT₂ (w : ℕ) : ℕ := w.unpair.2.unpair.2.unpair.2.unpair.2

/-- **The witness with its bookkeeping discarded** — what the step actually returns. -/
def witResult (w : ℕ) : ℕ := Nat.pair (witLo w) (witHi w)

@[simp] theorem resLo_witResult (w : ℕ) : resLo (witResult w) = witLo w := by
  simp [resLo, witResult]

@[simp] theorem resHi_witResult (w : ℕ) : resHi (witResult w) = witHi w := by
  simp [resHi, witResult]

/-- The witness packer. -/
def packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) : ℕ :=
  Nat.pair (Nat.pair lo hi)
    (Nat.pair (Nat.pair n₁ (Nat.pair m₁ t₁)) (Nat.pair n₂ (Nat.pair m₂ t₂)))

@[simp] theorem witLo_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witLo (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = lo := by simp [witLo, packWit]

@[simp] theorem witHi_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witHi (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = hi := by simp [witHi, packWit]

@[simp] theorem witN₁_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witN₁ (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = n₁ := by simp [witN₁, packWit]

@[simp] theorem witM₁_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witM₁ (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = m₁ := by simp [witM₁, packWit]

@[simp] theorem witT₁_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witT₁ (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = t₁ := by simp [witT₁, packWit]

@[simp] theorem witN₂_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witN₂ (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = n₂ := by simp [witN₂, packWit]

@[simp] theorem witM₂_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witM₂ (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = m₂ := by simp [witM₂, packWit]

@[simp] theorem witT₂_packWit (lo hi n₁ m₁ t₁ n₂ m₂ t₂ : ℕ) :
    witT₂ (packWit lo hi n₁ m₁ t₁ n₂ m₂ t₂) = t₂ := by simp [witT₂, packWit]

/-- Clause 1: the request's lower endpoint is strictly below the result's. -/
def stepLoB (request w : ℕ) : Bool :=
  decide (ratOfCode (reqLo request) < ratOfCode (witLo w))

/-- Clause 2: the result's endpoints are strictly ordered. -/
def stepOrderB (w : ℕ) : Bool :=
  decide (ratOfCode (witLo w) < ratOfCode (witHi w))

/-- Clause 3: the result's upper endpoint is strictly below the request's. -/
def stepHiB (request w : ℕ) : Bool :=
  decide (ratOfCode (witHi w) < ratOfCode (reqHi request))

/-- Clause 4: the result's width is at most half the request's. -/
def stepWidthB (request w : ℕ) : Bool :=
  !decide (ratOfCode (subCode (reqHi request) (reqLo request))
    < ratOfCode (addCode (subCode (witHi w) (witLo w)) (subCode (witHi w) (witLo w))))

theorem stepLoB_eq_true_iff (request w : ℕ) :
    stepLoB request w = true ↔
      ((ratOfCode (reqLo request) : ℚ) : ℝ) < ((ratOfCode (witLo w) : ℚ) : ℝ) := by
  simp only [stepLoB, decide_eq_true_eq]
  exact (Rat.cast_lt (K := ℝ)).symm

theorem stepOrderB_eq_true_iff (w : ℕ) :
    stepOrderB w = true ↔
      ((ratOfCode (witLo w) : ℚ) : ℝ) < ((ratOfCode (witHi w) : ℚ) : ℝ) := by
  simp only [stepOrderB, decide_eq_true_eq]
  exact (Rat.cast_lt (K := ℝ)).symm

theorem stepHiB_eq_true_iff (request w : ℕ) :
    stepHiB request w = true ↔
      ((ratOfCode (witHi w) : ℚ) : ℝ) < ((ratOfCode (reqHi request) : ℚ) : ℝ) := by
  simp only [stepHiB, decide_eq_true_eq]
  exact (Rat.cast_lt (K := ℝ)).symm

theorem stepWidthB_eq_true_iff (request w : ℕ) :
    stepWidthB request w = true ↔
      ((ratOfCode (witHi w) : ℚ) : ℝ) - ((ratOfCode (witLo w) : ℚ) : ℝ)
        ≤ (((ratOfCode (reqHi request) : ℚ) : ℝ)
            - ((ratOfCode (reqLo request) : ℚ) : ℝ)) / 2 := by
  simp only [stepWidthB, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
    ratOfCode_subCode, ratOfCode_addCode]
  constructor
  · intro h
    have h' := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at h'
    linarith
  · intro h
    refine (Rat.cast_le (K := ℝ)).mp ?_
    push_cast
    linarith

/-- The coded lower bound: the accumulator on the certified mask, less `2⁻ᵐ`. -/
def codedOpenLower (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p u : Baire) (n m t : ℕ) : RatCode :=
  subCode (acc (p (m + 1)) (mac (atoms (p (m + 1))) (streamTake u n) n t)) (halfPowCode m)

variable {P}

/-- **Soundness of the coded bound, at EVERY fuel.** Mask soundness certifies that the masked
atoms really lie in the inner approximation; accumulator soundness then bounds their weight by
the approximant's mass there. Note `n ≤ m` is NOT needed here — that hypothesis belongs to
`openLower_le`, one layer further out. -/
theorem codedOpenLower_le {p u : Baire} {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (haccsound : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake v n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n)
    (n m t : ℕ) :
    ((ratOfCode (codedOpenLower atoms acc mac p u n m t) : ℚ) : ℝ) ≤ openLower P p u n m := by
  have hcert := haccsound (p (m + 1)) (mac (atoms (p (m + 1))) (streamTake u n) n t)
    (innerApprox P u n) (measurableSet_innerApprox u n)
    (fun i hi hb => hmacsound (atoms (p (m + 1))) u n t i hi hb)
  have h := ENNReal.toReal_mono (measure_ne_top _ _) hcert
  rw [ENNReal.toReal_ofReal (hnonneg _ _)] at h
  simp only [codedOpenLower, openLower, ratOfCode_subCode, ratOfCode_halfPowCode]
  push_cast
  linarith

/-- **Eventual exactness.** At a fuel certifying every atom that lies in the inner approximation,
the mask becomes an exact membership test, and the accumulator's exactness clause turns the coded
bound into `openLower` on the nose. -/
theorem exists_codedOpenLower_eq {p u : Baire} {atoms : ℕ → List (ℕ × ℕ)}
    {acc : ℕ → ℕ → RatCode} {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (hexact : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length →
        (mask.testBit i = true ↔ P.dense ((atoms m).getD i (0, 0)).1 ∈ A)) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) = (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake v n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n)
    (hmaccomp : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n : ℕ), ∃ t, ∀ i, i < l.length →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n →
      (mac l (streamTake v n) n t).testBit i = true)
    (n m : ℕ) :
    ∃ t, ((ratOfCode (codedOpenLower atoms acc mac p u n m t) : ℚ) : ℝ) = openLower P p u n m := by
  obtain ⟨t, ht⟩ := hmaccomp (atoms (p (m + 1))) u n
  refine ⟨t, ?_⟩
  have hiff : ∀ i, i < (atoms (p (m + 1))).length →
      ((mac (atoms (p (m + 1))) (streamTake u n) n t).testBit i = true ↔
        P.dense ((atoms (p (m + 1))).getD i (0, 0)).1 ∈ innerApprox P u n) :=
    fun i hi => ⟨fun hb => hmacsound (atoms (p (m + 1))) u n t i hi hb, fun hmem => ht i hi hmem⟩
  have hcert := hexact (p (m + 1)) (mac (atoms (p (m + 1))) (streamTake u n) n t)
    (innerApprox P u n) (measurableSet_innerApprox u n) hiff
  have h := congrArg ENNReal.toReal hcert
  rw [ENNReal.toReal_ofReal (hnonneg _ _)] at h
  simp only [codedOpenLower, openLower, ratOfCode_subCode, ratOfCode_halfPowCode]
  push_cast
  linarith

variable (P)

/-- The coded upper bound: one complement of a sum, matching `annulusUpper` clause for clause. -/
def codedAnnulusUpper (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p : Baire) (uin ufar : ℕ → RatCode → Baire)
    (request w : ℕ) : RatCode :=
  subCode oneCode
    (addCode (codedOpenLower atoms acc mac p (uin (reqCentre request) (witLo w))
        (witN₁ w) (witM₁ w) (witT₁ w))
      (codedOpenLower atoms acc mac p (ufar (reqCentre request) (witHi w))
        (witN₂ w) (witM₂ w) (witT₂ w)))

/-- **Clause 5**, with the two `n ≤ m` guards folded in as VALIDITY CONDITIONS of the mass
clause — they are what `openLower_le` needs, not new geometric requirements. -/
def stepMassB (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p : Baire) (uin ufar : ℕ → RatCode → Baire)
    (request w : ℕ) : Bool :=
  decide (witN₁ w ≤ witM₁ w) && decide (witN₂ w ≤ witM₂ w) &&
    decide (ratOfCode (codedAnnulusUpper atoms acc mac p uin ufar request w)
      < ratOfCode (reqErr request))

variable {P}

/-- **Clause 5's characterization, forward direction**: firing implies the two guards and the
SEMANTIC bound. Soundness of the coded layer is what makes the implication go this way. -/
theorem stepMassB_sound {p : Baire} {uin ufar : ℕ → RatCode → Baire} {atoms : ℕ → List (ℕ × ℕ)}
    {acc : ℕ → ℕ → RatCode} {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (haccsound : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake v n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n)
    (request w : ℕ) (h : stepMassB atoms acc mac p uin ufar request w = true) :
    witN₁ w ≤ witM₁ w ∧ witN₂ w ≤ witM₂ w ∧
      annulusUpper P p (uin (reqCentre request) (witLo w)) (ufar (reqCentre request) (witHi w))
        (witN₁ w) (witM₁ w) (witN₂ w) (witM₂ w)
        < ((ratOfCode (reqErr request) : ℚ) : ℝ) := by
  simp only [stepMassB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  refine ⟨h₁, h₂, ?_⟩
  have hR : ((ratOfCode (codedAnnulusUpper atoms acc mac p uin ufar request w) : ℚ) : ℝ)
      < ((ratOfCode (reqErr request) : ℚ) : ℝ) := by exact_mod_cast h₃
  have hl₁ := codedOpenLower_le (P := P) (p := p) (u := uin (reqCentre request) (witLo w))
    hnonneg haccsound hmacsound (witN₁ w) (witM₁ w) (witT₁ w)
  have hl₂ := codedOpenLower_le (P := P) (p := p) (u := ufar (reqCentre request) (witHi w))
    hnonneg haccsound hmacsound (witN₂ w) (witM₂ w) (witT₂ w)
  simp only [codedAnnulusUpper, ratOfCode_subCode, ratOfCode_addCode, ratOfCode_oneCode] at hR
  push_cast at hR
  simp only [annulusUpper]
  linarith

/-- The five clauses combined. -/
def stepSuccessB (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p : Baire) (uin ufar : ℕ → RatCode → Baire)
    (request w : ℕ) : Bool :=
  stepLoB request w && stepOrderB w && stepHiB request w && stepWidthB request w &&
    stepMassB atoms acc mac p uin ufar request w

omit [MeasurableSpace X] [BorelSpace X] in
/-- Closed annuli shrink with their endpoints — how thinness transfers inward under
rationalization. -/
theorem closedAnnulus_mono {t : X} {a a' b b' : ℝ} (h1 : a ≤ a') (h2 : b' ≤ b) :
    closedAnnulus t a' b' ⊆ closedAnnulus t a b :=
  fun _ hx => ⟨le_trans h1 hx.1, le_trans hx.2 h2⟩

/-- **Boundary theorem 1: success implies the contract.** Combines the four geometric
characterizations, `stepMassB_sound`, and `annulusUpper_sound`. -/
theorem stepSuccess_sound {μ : ProbabilityMeasure X} {p : Baire}
    {uin ufar : ℕ → RatCode → Baire}
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (haccsound : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake v n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n)
    (hp : WeakMeasureNames P p μ) {request : ℕ}
    (hin : ∀ i c, openOf P (uin i c) = ball (P.dense i) ((ratOfCode c : ℚ) : ℝ))
    (hfar : ∀ i c, openOf P (ufar i c)
      = {x : X | ((ratOfCode c : ℚ) : ℝ) < dist x (P.dense i)})
    (w : ℕ) (h : stepSuccessB atoms acc mac p uin ufar request w = true) :
    ThinClosedAnnulusStep P μ request (witResult w) := by
  simp only [stepSuccessB, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hlo, horder⟩, hhi⟩, hwidth⟩, hmass⟩ := h
  rw [stepLoB_eq_true_iff] at hlo
  rw [stepOrderB_eq_true_iff] at horder
  rw [stepHiB_eq_true_iff] at hhi
  rw [stepWidthB_eq_true_iff] at hwidth
  obtain ⟨h₁, h₂, hupper⟩ := stepMassB_sound hnonneg haccsound hmacsound request w hmass
  have hbound := annulusUpper_sound (P := P) (μ := μ) hp
    (hin (reqCentre request) (witLo w)) (hfar (reqCentre request) (witHi w)) horder.le h₁ h₂
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [resLo_witResult, resHi_witResult]
  · exact hlo
  · exact horder
  · exact hhi
  · exact hwidth
  · exact lt_of_le_of_lt hbound hupper

/-- **Boundary theorem 2: some witness succeeds.** Combines rationalization of
`exists_interiorSubinterval`'s real endpoints, `exists_annulusUpper_lt`, and eventual coded
exactness. The only place the classical counting lemma is used. -/
theorem exists_stepSuccess {μ : ProbabilityMeasure X} {p : Baire}
    {uin ufar : ℕ → RatCode → Baire}
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (hexact : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length →
        (mask.testBit i = true ↔ P.dense ((atoms m).getD i (0, 0)).1 ∈ A)) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) = (atomic P m).toMeasure A)
    (hmacsound : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake v n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n)
    (hmaccomp : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n : ℕ), ∃ t, ∀ i, i < l.length →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n →
      (mac l (streamTake v n) n t).testBit i = true)
    (hp : WeakMeasureNames P p μ) {request : ℕ}
    (hin : ∀ i c, openOf P (uin i c) = ball (P.dense i) ((ratOfCode c : ℚ) : ℝ))
    (hfar : ∀ i c, openOf P (ufar i c)
      = {x : X | ((ratOfCode c : ℚ) : ℝ) < dist x (P.dense i)})
    (hreq : ValidIntervalRequest request) :
    ∃ w, stepSuccessB atoms acc mac p uin ufar request w = true := by
  obtain ⟨hlohi, herr⟩ := hreq
  obtain ⟨a', b', ha', hab', hb', hwidth', hthin'⟩ :=
    exists_interiorSubinterval μ (P.dense (reqCentre request)) hlohi herr
  obtain ⟨q₁, hq₁a, hq₁m⟩ := exists_rat_btwn (show a' < (a' + b') / 2 by linarith)
  obtain ⟨q₂, hq₂m, hq₂b⟩ := exists_rat_btwn (show (a' + b') / 2 < b' by linarith)
  obtain ⟨c₁, hc₁⟩ := ratOfCode_surjective q₁
  obtain ⟨c₂, hc₂⟩ := ratOfCode_surjective q₂
  have hv₁ : ((ratOfCode c₁ : ℚ) : ℝ) = (q₁ : ℝ) := by rw [hc₁]
  have hv₂ : ((ratOfCode c₂ : ℚ) : ℝ) = (q₂ : ℝ) := by rw [hc₂]
  have hthin : (μ.toMeasure (closedAnnulus (P.dense (reqCentre request))
      ((ratOfCode c₁ : ℚ) : ℝ) ((ratOfCode c₂ : ℚ) : ℝ))).toReal
      < ((ratOfCode (reqErr request) : ℚ) : ℝ) := by
    refine lt_of_le_of_lt ?_ hthin'
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
    exact closedAnnulus_mono (by rw [hv₁]; linarith) (by rw [hv₂]; linarith)
  obtain ⟨n₁, m₁, n₂, m₂, h₁, h₂, hupper⟩ := exists_annulusUpper_lt (P := P) hp
    (hin (reqCentre request) c₁) (hfar (reqCentre request) c₂)
    (by rw [hv₁, hv₂]; linarith) hthin
  obtain ⟨t₁, ht₁⟩ := exists_codedOpenLower_eq (P := P) (p := p)
    (u := uin (reqCentre request) c₁) hnonneg hexact hmacsound hmaccomp n₁ m₁
  obtain ⟨t₂, ht₂⟩ := exists_codedOpenLower_eq (P := P) (p := p)
    (u := ufar (reqCentre request) c₂) hnonneg hexact hmacsound hmaccomp n₂ m₂
  refine ⟨packWit c₁ c₂ n₁ m₁ t₁ n₂ m₂ t₂, ?_⟩
  have hval : ((ratOfCode (codedAnnulusUpper atoms acc mac p uin ufar request
      (packWit c₁ c₂ n₁ m₁ t₁ n₂ m₂ t₂)) : ℚ) : ℝ)
      = annulusUpper P p (uin (reqCentre request) c₁) (ufar (reqCentre request) c₂)
        n₁ m₁ n₂ m₂ := by
    simp only [codedAnnulusUpper, annulusUpper, ratOfCode_subCode, ratOfCode_addCode,
      ratOfCode_oneCode, witLo_packWit, witHi_packWit, witN₁_packWit, witM₁_packWit,
      witT₁_packWit, witN₂_packWit, witM₂_packWit, witT₂_packWit]
    push_cast
    rw [ht₁, ht₂]
  simp only [stepSuccessB, stepMassB, Bool.and_eq_true, decide_eq_true_eq,
    witN₁_packWit, witM₁_packWit, witN₂_packWit, witM₂_packWit]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ⟨h₁, h₂⟩, ?_⟩
  · rw [stepLoB_eq_true_iff, witLo_packWit, hv₁]; linarith
  · rw [stepOrderB_eq_true_iff, witLo_packWit, witHi_packWit, hv₁, hv₂]; linarith
  · rw [stepHiB_eq_true_iff, witHi_packWit, hv₂]; linarith
  · rw [stepWidthB_eq_true_iff, witLo_packWit, witHi_packWit, hv₁, hv₂]; linarith
  · refine (Rat.cast_lt (K := ℝ)).mp ?_
    rw [hval]
    exact hupper

theorem streamTake_eq_map {α : Type*} (p : ℕ → α) (n : ℕ) :
    streamTake p n = (List.range n).map p := by
  apply List.ext_getElem
  · simp [length_streamTake]
  · intro i h1 h2
    simp [getElem_streamTake]

/-- **The prefix bound.** It need only cover the two weak-name reads `p (m₁ + 1)` and
`p (m₂ + 1)`; `+ 2` is what makes each read STRICTLY inside the prefix. -/
def stepBound (v : ℕ) (_head : ℕ) : ℕ :=
  max (witM₁ v.unpair.2 + 2) (witM₂ v.unpair.2 + 2)

/-- Lookup inequality, inner track. -/
theorem lt_stepBound_inner (request w head : ℕ) :
    witM₁ w + 1 < stepBound (Nat.pair request w) head := by
  simp only [stepBound, Nat.unpair_pair]
  omega

/-- Lookup inequality, far track. -/
theorem lt_stepBound_far (request w head : ℕ) :
    witM₂ w + 1 < stepBound (Nat.pair request w) head := by
  simp only [stepBound, Nat.unpair_pair]
  omega

/-- The coded lower bound, read off a prefix instead of the oracle. -/
def codedOpenLowerPre (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (u : Baire) (n m t : ℕ) :
    RatCode :=
  subCode (acc (pre.getD (m + 1) 0)
    (mac (atoms (pre.getD (m + 1) 0)) (streamTake u n) n t)) (halfPowCode m)

theorem codedOpenLowerPre_eq {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (p u : Baire) {n m t L : ℕ} (h : m + 1 < L) :
    codedOpenLowerPre atoms acc mac (streamTake p L) u n m t
      = codedOpenLower atoms acc mac p u n m t := by
  simp only [codedOpenLowerPre, codedOpenLower, streamTake_getD p h]

/-- The coded upper bound over a prefix. -/
def codedAnnulusUpperPre (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (uin ufar : ℕ → RatCode → Baire)
    (request w : ℕ) : RatCode :=
  subCode oneCode
    (addCode (codedOpenLowerPre atoms acc mac pre (uin (reqCentre request) (witLo w))
        (witN₁ w) (witM₁ w) (witT₁ w))
      (codedOpenLowerPre atoms acc mac pre (ufar (reqCentre request) (witHi w))
        (witN₂ w) (witM₂ w) (witT₂ w)))

/-- Clause 5 over a prefix. -/
def stepMassBPre (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (uin ufar : ℕ → RatCode → Baire)
    (request w : ℕ) : Bool :=
  decide (witN₁ w ≤ witM₁ w) && decide (witN₂ w ≤ witM₂ w) &&
    decide (ratOfCode (codedAnnulusUpperPre atoms acc mac pre uin ufar request w)
      < ratOfCode (reqErr request))

/-- The five clauses over a prefix. -/
def stepSuccessBPre (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (uin ufar : ℕ → RatCode → Baire)
    (request w : ℕ) : Bool :=
  stepLoB request w && stepOrderB w && stepHiB request w && stepWidthB request w &&
    stepMassBPre atoms acc mac pre uin ufar request w

/-- **Exact-prefix agreement.** On a prefix long enough for both weak-name reads, the
prefix-parameterized test is the oracle test — pointwise, before any packing. -/
theorem stepSuccessBPre_eq {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (p : Baire) (uin ufar : ℕ → RatCode → Baire)
    (request w L : ℕ) (h₁ : witM₁ w + 1 < L) (h₂ : witM₂ w + 1 < L) :
    stepSuccessBPre atoms acc mac (streamTake p L) uin ufar request w
      = stepSuccessB atoms acc mac p uin ufar request w := by
  simp only [stepSuccessBPre, stepSuccessB, stepMassBPre, stepMassB, codedAnnulusUpperPre,
    codedAnnulusUpper, codedOpenLowerPre_eq p (uin (reqCentre request) (witLo w)) h₁,
    codedOpenLowerPre_eq p (ufar (reqCentre request) (witHi w)) h₂]
  rfl

/-- **Prefixes of a computed stream are primitive recursive in the stream's index.** Two
consumers, one per track, so the inner and far Primrec proofs stay symmetric. Proved through
`streamTake_eq_map`, so it is ordinary list construction rather than new machine machinery. -/
private theorem primrec_streamTake_comp {γ : Type*} [Primcodable γ] {f : ℕ → ℕ → ℕ}
    {g h : γ → ℕ} (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) :
    Primrec fun z : γ => streamTake (f (g z)) (h z) := by
  have hmap : Primrec fun z : γ => (List.range (h z)).map (f (g z)) :=
    Primrec.list_map (Primrec.list_range.comp hh)
      (hf.comp (hg.comp Primrec.fst) Primrec.snd).to₂
  exact hmap.of_eq fun z => (streamTake_eq_map _ _).symm

/-- **The machine wire format for a stream family.** The semantic API stays curried, `u i c`; the
machine layer consumes `packedStreamFamily u ⟨i, c⟩` so the stream-prefix helper is used at its
reliable `ℕ`-indexed shape. The packing never appears above this line. -/
private def packedStreamFamily (u : ℕ → RatCode → Baire) (q : ℕ) : Baire :=
  u q.unpair.1 q.unpair.2

@[simp] private theorem packedStreamFamily_pair (u : ℕ → RatCode → Baire) (i c : ℕ) :
    packedStreamFamily u (Nat.pair i c) = u i c := by
  simp [packedStreamFamily]

private theorem primrec_packedStreamFamily {u : ℕ → RatCode → Baire}
    (hu : Primrec fun z : (ℕ × RatCode) × ℕ => u z.1.1 z.1.2 z.2) :
    Primrec fun z : ℕ × ℕ => packedStreamFamily u z.1 z.2 := by
  simp only [packedStreamFamily]
  exact hu.comp
    (((primrec_unpairFst.comp Primrec.fst).pair (primrec_unpairSnd.comp Primrec.fst)).pair
      Primrec.snd)

private theorem primrec_reqCentre : Primrec reqCentre := primrec_unpairFst
private theorem primrec_reqLo : Primrec reqLo := primrec_unpairFst.comp primrec_unpairSnd
private theorem primrec_reqHi : Primrec reqHi :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp primrec_unpairSnd)
private theorem primrec_reqErr : Primrec reqErr :=
  primrec_unpairSnd.comp (primrec_unpairSnd.comp primrec_unpairSnd)
private theorem primrec_witLo : Primrec witLo := primrec_unpairFst.comp primrec_unpairFst
private theorem primrec_witHi : Primrec witHi := primrec_unpairSnd.comp primrec_unpairFst
private theorem primrec_witN₁ : Primrec witN₁ :=
  primrec_unpairFst.comp (primrec_unpairFst.comp primrec_unpairSnd)
private theorem primrec_witM₁ : Primrec witM₁ :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp (primrec_unpairFst.comp primrec_unpairSnd))
private theorem primrec_witT₁ : Primrec witT₁ :=
  primrec_unpairSnd.comp (primrec_unpairSnd.comp (primrec_unpairFst.comp primrec_unpairSnd))
private theorem primrec_witN₂ : Primrec witN₂ :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp primrec_unpairSnd)
private theorem primrec_witM₂ : Primrec witM₂ :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp (primrec_unpairSnd.comp primrec_unpairSnd))
private theorem primrec_witT₂ : Primrec witT₂ :=
  primrec_unpairSnd.comp (primrec_unpairSnd.comp (primrec_unpairSnd.comp primrec_unpairSnd))

private theorem primrec_stepLoB : Primrec fun z : ℕ × ℕ => stepLoB z.1 z.2 :=
  PrimrecPred.decide
    (primrecPred_ratLt (primrec_reqLo.comp Primrec.fst) (primrec_witLo.comp Primrec.snd))

private theorem primrec_stepOrderB : Primrec fun z : ℕ × ℕ => stepOrderB z.2 :=
  PrimrecPred.decide
    (primrecPred_ratLt (primrec_witLo.comp Primrec.snd) (primrec_witHi.comp Primrec.snd))

private theorem primrec_stepHiB : Primrec fun z : ℕ × ℕ => stepHiB z.1 z.2 :=
  PrimrecPred.decide
    (primrecPred_ratLt (primrec_witHi.comp Primrec.snd) (primrec_reqHi.comp Primrec.fst))

private theorem primrec_stepWidthB : Primrec fun z : ℕ × ℕ => stepWidthB z.1 z.2 := by
  have h := PrimrecPred.decide (PrimrecPred.not
    (primrecPred_ratLt
      (primrec₂_subCode.comp (primrec_reqHi.comp Primrec.fst) (primrec_reqLo.comp Primrec.fst))
      (primrec₂_addCode.comp
        (primrec₂_subCode.comp (primrec_witHi.comp Primrec.snd) (primrec_witLo.comp Primrec.snd))
        (primrec₂_subCode.comp (primrec_witHi.comp Primrec.snd)
          (primrec_witLo.comp Primrec.snd)))))
  exact h.of_eq fun z => by rw [decide_not]; rfl

attribute [local irreducible] subCode addCode halfPowCode

section MachinePrimrec

variable {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
  {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {uin ufar : ℕ → RatCode → Baire}
  (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
  (hmac : Primrec fun q : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac q.1.1 q.1.2 q.2.1 q.2.2)
  (huin : Primrec fun z : (ℕ × RatCode) × ℕ => uin z.1.1 z.1.2 z.2)
  (hufar : Primrec fun z : (ℕ × RatCode) × ℕ => ufar z.1.1 z.1.2 z.2)

include hatoms hacc hmac in
private theorem primrec_innerLowerPre
    (huin : Primrec fun z : (ℕ × RatCode) × ℕ => uin z.1.1 z.1.2 z.2) :
    Primrec fun z : List ℕ × ℕ × ℕ => codedOpenLowerPre atoms acc mac z.1
      (uin (reqCentre z.2.1) (witLo z.2.2)) (witN₁ z.2.2) (witM₁ z.2.2) (witT₁ z.2.2) := by
  have hw : Primrec fun z : List ℕ × ℕ × ℕ => z.2.2 := Primrec.snd.comp Primrec.snd
  have hr : Primrec fun z : List ℕ × ℕ × ℕ => z.2.1 := Primrec.fst.comp Primrec.snd
  have hidx : Primrec fun z : List ℕ × ℕ × ℕ => z.1.getD (witM₁ z.2.2 + 1) 0 :=
    (Primrec.list_getD 0).comp Primrec.fst (Primrec.succ.comp (primrec_witM₁.comp hw))
  have htakeP : Primrec fun z : List ℕ × ℕ × ℕ =>
      streamTake (packedStreamFamily uin (Nat.pair (reqCentre z.2.1) (witLo z.2.2)))
        (witN₁ z.2.2) :=
    primrec_streamTake_comp (f := fun a b => packedStreamFamily uin a b)
      (primrec_packedStreamFamily huin)
      (Primrec₂.natPair.comp (primrec_reqCentre.comp hr) (primrec_witLo.comp hw))
      (primrec_witN₁.comp hw)
  have htake : Primrec fun z : List ℕ × ℕ × ℕ =>
      streamTake (uin (reqCentre z.2.1) (witLo z.2.2)) (witN₁ z.2.2) :=
    htakeP.of_eq fun z => by rw [packedStreamFamily_pair]
  have hp₁ : Primrec fun z : List ℕ × ℕ × ℕ =>
      (atoms (z.1.getD (witM₁ z.2.2 + 1) 0),
        streamTake (uin (reqCentre z.2.1) (witLo z.2.2)) (witN₁ z.2.2)) :=
    (hatoms.comp hidx).pair htake
  have hp₂ : Primrec fun z : List ℕ × ℕ × ℕ => ((witN₁ z.2.2 : ℕ), (witT₁ z.2.2 : ℕ)) :=
    (primrec_witN₁.comp hw).pair (primrec_witT₁.comp hw)
  have hmask : Primrec fun z : List ℕ × ℕ × ℕ =>
      mac (atoms (z.1.getD (witM₁ z.2.2 + 1) 0))
        (streamTake (uin (reqCentre z.2.1) (witLo z.2.2)) (witN₁ z.2.2))
        (witN₁ z.2.2) (witT₁ z.2.2) :=
    hmac.comp (hp₁.pair hp₂)
  simp only [codedOpenLowerPre]
  exact primrec₂_subCode.comp (hacc.comp hidx hmask)
    (primrec_halfPowCode.comp (primrec_witM₁.comp hw))

include hatoms hacc hmac in
private theorem primrec_farLowerPre
    (hufar : Primrec fun z : (ℕ × RatCode) × ℕ => ufar z.1.1 z.1.2 z.2) :
    Primrec fun z : List ℕ × ℕ × ℕ => codedOpenLowerPre atoms acc mac z.1
      (ufar (reqCentre z.2.1) (witHi z.2.2)) (witN₂ z.2.2) (witM₂ z.2.2) (witT₂ z.2.2) := by
  have hw : Primrec fun z : List ℕ × ℕ × ℕ => z.2.2 := Primrec.snd.comp Primrec.snd
  have hr : Primrec fun z : List ℕ × ℕ × ℕ => z.2.1 := Primrec.fst.comp Primrec.snd
  have hidx : Primrec fun z : List ℕ × ℕ × ℕ => z.1.getD (witM₂ z.2.2 + 1) 0 :=
    (Primrec.list_getD 0).comp Primrec.fst (Primrec.succ.comp (primrec_witM₂.comp hw))
  have htakeP : Primrec fun z : List ℕ × ℕ × ℕ =>
      streamTake (packedStreamFamily ufar (Nat.pair (reqCentre z.2.1) (witHi z.2.2)))
        (witN₂ z.2.2) :=
    primrec_streamTake_comp (f := fun a b => packedStreamFamily ufar a b)
      (primrec_packedStreamFamily hufar)
      (Primrec₂.natPair.comp (primrec_reqCentre.comp hr) (primrec_witHi.comp hw))
      (primrec_witN₂.comp hw)
  have htake : Primrec fun z : List ℕ × ℕ × ℕ =>
      streamTake (ufar (reqCentre z.2.1) (witHi z.2.2)) (witN₂ z.2.2) :=
    htakeP.of_eq fun z => by rw [packedStreamFamily_pair]
  have hp₁ : Primrec fun z : List ℕ × ℕ × ℕ =>
      (atoms (z.1.getD (witM₂ z.2.2 + 1) 0),
        streamTake (ufar (reqCentre z.2.1) (witHi z.2.2)) (witN₂ z.2.2)) :=
    (hatoms.comp hidx).pair htake
  have hp₂ : Primrec fun z : List ℕ × ℕ × ℕ => ((witN₂ z.2.2 : ℕ), (witT₂ z.2.2 : ℕ)) :=
    (primrec_witN₂.comp hw).pair (primrec_witT₂.comp hw)
  have hmask : Primrec fun z : List ℕ × ℕ × ℕ =>
      mac (atoms (z.1.getD (witM₂ z.2.2 + 1) 0))
        (streamTake (ufar (reqCentre z.2.1) (witHi z.2.2)) (witN₂ z.2.2))
        (witN₂ z.2.2) (witT₂ z.2.2) :=
    hmac.comp (hp₁.pair hp₂)
  simp only [codedOpenLowerPre]
  exact primrec₂_subCode.comp (hacc.comp hidx hmask)
    (primrec_halfPowCode.comp (primrec_witM₂.comp hw))

include hatoms hacc hmac huin hufar in
private theorem primrec_upperPre :
    Primrec fun z : List ℕ × ℕ × ℕ =>
      codedAnnulusUpperPre atoms acc mac z.1 uin ufar z.2.1 z.2.2 := by
  simp only [codedAnnulusUpperPre]
  exact primrec₂_subCode.comp (Primrec.const oneCode)
    (primrec₂_addCode.comp (primrec_innerLowerPre hatoms hacc hmac huin)
      (primrec_farLowerPre hatoms hacc hmac hufar))

include hatoms hacc hmac huin hufar in
private theorem primrec_stepMassBPre :
    Primrec fun z : List ℕ × ℕ × ℕ =>
      stepMassBPre atoms acc mac z.1 uin ufar z.2.1 z.2.2 := by
  have hw : Primrec fun z : List ℕ × ℕ × ℕ => z.2.2 := Primrec.snd.comp Primrec.snd
  have h1 : Primrec fun z : List ℕ × ℕ × ℕ => decide (witN₁ z.2.2 ≤ witM₁ z.2.2) :=
    PrimrecPred.decide
      (PrimrecRel.comp Primrec.nat_le (primrec_witN₁.comp hw) (primrec_witM₁.comp hw))
  have h2 : Primrec fun z : List ℕ × ℕ × ℕ => decide (witN₂ z.2.2 ≤ witM₂ z.2.2) :=
    PrimrecPred.decide
      (PrimrecRel.comp Primrec.nat_le (primrec_witN₂.comp hw) (primrec_witM₂.comp hw))
  have h3 : Primrec fun z : List ℕ × ℕ × ℕ =>
      decide (ratOfCode (codedAnnulusUpperPre atoms acc mac z.1 uin ufar z.2.1 z.2.2)
        < ratOfCode (reqErr z.2.1)) :=
    PrimrecPred.decide
      (primrecPred_ratLt (primrec_upperPre hatoms hacc hmac huin hufar)
        (primrec_reqErr.comp (Primrec.fst.comp Primrec.snd)))
  simp only [stepMassBPre]
  exact Primrec.and.comp (Primrec.and.comp h1 h2) h3

include hatoms hacc hmac huin hufar in
private theorem primrec_stepSuccessBPre :
    Primrec fun z : List ℕ × ℕ × ℕ =>
      stepSuccessBPre atoms acc mac z.1 uin ufar z.2.1 z.2.2 := by
  have hrw : Primrec fun z : List ℕ × ℕ × ℕ => (z.2.1, z.2.2) :=
    (Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)
  simp only [stepSuccessBPre]
  exact Primrec.and.comp (Primrec.and.comp (Primrec.and.comp
    (Primrec.and.comp (primrec_stepLoB.comp hrw) (primrec_stepOrderB.comp hrw))
    (primrec_stepHiB.comp hrw)) (primrec_stepWidthB.comp hrw))
    (primrec_stepMassBPre hatoms hacc hmac huin hufar)

end MachinePrimrec

/-- The packed test: zero exactly on success. -/
def stepG (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (uin ufar : ℕ → RatCode → Baire) (v : ℕ) : ℕ :=
  if stepSuccessBPre atoms acc mac (Denumerable.ofNat (List ℕ) v.unpair.2) uin ufar
      v.unpair.1.unpair.1 v.unpair.1.unpair.2 = true then 0 else 1

/-- **The zero characterization**, rewriting directly to `stepSuccessB` through exact-prefix
agreement — so the search theorem never sees the prefix layer. -/
theorem stepG_eq_zero_iff {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (uin ufar : ℕ → RatCode → Baire) (p : Baire)
    (request w : ℕ) :
    stepG atoms acc mac uin ufar (Nat.pair (Nat.pair request w)
        (encode (streamTake p (stepBound (Nat.pair request w) (p 0))))) = 0
      ↔ stepSuccessB atoms acc mac p uin ufar request w = true := by
  have hagree : stepSuccessBPre atoms acc mac
      (streamTake p (stepBound (Nat.pair request w) (p 0))) uin ufar request w
      = stepSuccessB atoms acc mac p uin ufar request w :=
    stepSuccessBPre_eq p uin ufar request w _
      (lt_stepBound_inner request w (p 0)) (lt_stepBound_far request w (p 0))
  simp only [stepG, Nat.unpair_pair, Denumerable.ofNat_encode, hagree]
  constructor
  · intro h
    by_contra hb
    rw [ite_eq_right hb] at h
    exact absurd h (by norm_num)
  · intro h
    rw [ite_eq_left h]

attribute [local irreducible] codedOpenLowerPre codedAnnulusUpperPre stepMassBPre stepSuccessBPre

private theorem primrec_stepG {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {uin ufar : ℕ → RatCode → Baire}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun q : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac q.1.1 q.1.2 q.2.1 q.2.2)
    (huin : Primrec fun z : (ℕ × RatCode) × ℕ => uin z.1.1 z.1.2 z.2)
    (hufar : Primrec fun z : (ℕ × RatCode) × ℕ => ufar z.1.1 z.1.2 z.2) :
    Primrec (stepG atoms acc mac uin ufar) := by
  have hdec : Primrec fun v : ℕ =>
      ((Denumerable.ofNat (List ℕ) v.unpair.2), (v.unpair.1.unpair.1, v.unpair.1.unpair.2)) :=
    ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd).pair
      ((primrec_unpairFst.comp primrec_unpairFst).pair
        (primrec_unpairSnd.comp primrec_unpairFst))
  have hb : Primrec fun v : ℕ => stepSuccessBPre atoms acc mac
      (Denumerable.ofNat (List ℕ) v.unpair.2) uin ufar
      v.unpair.1.unpair.1 v.unpair.1.unpair.2 :=
    (primrec_stepSuccessBPre hatoms hacc hmac huin hufar).comp hdec
  exact (Primrec.ite (PrimrecRel.comp Primrec.eq hb (Primrec.const true))
    (Primrec.const 0) (Primrec.const 1)).of_eq fun _ => rfl

variable (P)

/-- **The single-step search.** One code, every measure and every valid request.

Its proof exposes neither of its two inputs: the continuity-open engine constructs sound
convergent upper bounds for the candidate's closed-annulus mass, `exists_interiorSubinterval`
proves that some candidate is eventually certified, and `rfind` selects the first certified one —
so no classical witness enters the code.

The search index is a candidate endpoint PAIR together with two independent triples
`(n, m, t)` — inner-approximation stage, weak-name level, mask fuel — one per track; see the
witness layout above. Its result is `witResult`, so the two triples never reach the
contract.

The upper-bound sequence is NOT required to be monotone. The search needs only that every
computed value is a sound upper bound and that for every slack above the true mass some stage
falls below it. -/
theorem exists_thinStepCode :
    ∃ stepCode : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure X) (request : ℕ),
      WeakMeasureNames P p μ → ValidIntervalRequest request →
      ∃ result ∈ stepCode.eval p request, ThinClosedAnnulusStep P μ request result := by
  classical
  -- the accumulator/mask package, and the apartness certificate for the far track
  obtain ⟨atoms, acc, hatoms, haccprim, hnonneg, haccsound, hexact⟩ :=
    exists_completeCertifiedWeightCode P
  obtain ⟨mac, hmacprim, hmacspec⟩ := exists_maskAtCode (P := P)
  obtain ⟨fires, hfprim, hfsound, hfcomplete⟩ := exists_afrOddCert P
  have hmacsound : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake v n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n :=
    fun l v n t i hi hb => (hmacspec l v n).1 t i hi hb
  have hmaccomp : ∀ (l : List (ℕ × ℕ)) (v : Baire) (n : ℕ), ∃ t, ∀ i, i < l.length →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P v n →
      (mac l (streamTake v n) n t).testBit i = true :=
    fun l v n => (hmacspec l v n).2.2
  -- the two stream families, from the effective AFR tracks
  set uin : ℕ → RatCode → Baire := fun i c => afrEvenEffective c i with huindef
  set ufar : ℕ → RatCode → Baire := fun i c => afrOddEffective fires c i with hufardef
  have hin : ∀ i c, openOf P (uin i c) = ball (P.dense i) ((ratOfCode c : ℚ) : ℝ) := by
    intro i c
    rw [huindef]
    simp only [afrEvenEffective_eq]
    exact openOf_afrEven i _
  have hfar : ∀ i c, openOf P (ufar i c)
      = {x : X | ((ratOfCode c : ℚ) : ℝ) < dist x (P.dense i)} := by
    intro i c
    rw [hufardef]
    simp only
    rw [openOf_afrOddEffective (ρ := ((ratOfCode c : ℚ) : ℝ)) c i
      (fun k t hk => hfsound i k c t hk) (fun k hk => hfcomplete i k c hk), openOf_afrOdd]
  have huin : Primrec fun z : (ℕ × RatCode) × ℕ => uin z.1.1 z.1.2 z.2 :=
    primrec_afrEvenEffective_uniform.comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
  have hufar : Primrec fun z : (ℕ × RatCode) × ℕ => ufar z.1.1 z.1.2 z.2 :=
    (primrec_afrOddEffective_uniform hfprim).comp
      (((Primrec.snd.comp Primrec.fst).pair (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)
  -- the search, and the total post-processor discarding the bookkeeping
  have hbound : Primrec₂ stepBound :=
    Primrec.nat_max.comp
      (Primrec.succ.comp (Primrec.succ.comp (primrec_witM₁.comp
        (primrec_unpairSnd.comp Primrec.fst))))
      (Primrec.succ.comp (Primrec.succ.comp (primrec_witM₂.comp
        (primrec_unpairSnd.comp Primrec.fst))))
  obtain ⟨searchCode, hsearchmem, hsearchdom⟩ := exists_prefixSearchCode hbound
    (primrec_stepG hatoms haccprim hmacprim huin hufar)
  obtain ⟨witCode, hwitCode⟩ := exists_ofNatFnCode
    (g := witResult) (Primrec₂.natPair.comp primrec_witLo primrec_witHi).to_comp
  refine ⟨OracleCode.comp witCode searchCode, fun p μ request hp hreq => ?_⟩
  -- convergence, from the semantic boundary theorem
  obtain ⟨w₀, hw₀⟩ := exists_stepSuccess (P := P) (μ := μ) (uin := uin) (ufar := ufar)
    hnonneg hexact hmacsound hmaccomp hp hin hfar hreq
  have hex : ∃ k, SearchSuccess stepBound (stepG atoms acc mac uin ufar) p request k :=
    ⟨w₀, (stepG_eq_zero_iff uin ufar p request w₀).mpr hw₀⟩
  obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp ((hsearchdom p request).mpr hex)
  have hsucc : stepSuccessB atoms acc mac p uin ufar request w :=
    (stepG_eq_zero_iff uin ufar p request w).mp ((hsearchmem p request w).mp hw).1
  refine ⟨witResult w, ?_, stepSuccess_sound (P := P) (μ := μ) hnonneg haccsound hmacsound hp
    hin hfar w hsucc⟩
  rw [eval_comp_some (Part.eq_some_iff.mpr hw), hwitCode p w]
  exact Part.mem_some _

/-- The coded `1/4`. -/
def quarterCode : RatCode := fracCode 1 4

/-- The coded `1/2`. -/
def halfCode : RatCode := fracCode 1 2

/-- Coded minimum — a decidable comparison of two rational codes. -/
def minCode (x y : RatCode) : RatCode := if ratOfCode x < ratOfCode y then x else y

/-- The midpoint of a coded interval. -/
def midCode (ac bc : RatCode) : RatCode := mulCode (addCode ac bc) halfCode

/-- The normalized half-width: a quarter of the interval, capped at a quarter. -/
def deltaCode (ac bc : RatCode) : RatCode :=
  minCode (mulCode (subCode bc ac) quarterCode) quarterCode

/-- The normalized lower endpoint. -/
def normLo (ac bc : RatCode) : RatCode := subCode (midCode ac bc) (deltaCode ac bc)

/-- The normalized upper endpoint. -/
def normHi (ac bc : RatCode) : RatCode := addCode (midCode ac bc) (deltaCode ac bc)

theorem ratOfCode_quarterCode : ratOfCode quarterCode = 1 / 4 := by
  rw [quarterCode, ratOfCode_fracCode (by norm_num : (4 : ℕ) ≠ 0) 1]
  norm_num

theorem ratOfCode_halfCode : ratOfCode halfCode = 1 / 2 := by
  rw [halfCode, ratOfCode_fracCode (by norm_num : (2 : ℕ) ≠ 0) 1]
  norm_num

theorem ratOfCode_minCode (x y : RatCode) :
    ratOfCode (minCode x y) = min (ratOfCode x) (ratOfCode y) := by
  rw [minCode]
  split_ifs with h
  · exact (min_eq_left h.le).symm
  · exact (min_eq_right (not_lt.mp h)).symm

theorem ratOfCode_deltaCode (ac bc : RatCode) :
    ratOfCode (deltaCode ac bc)
      = min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) := by
  rw [deltaCode, ratOfCode_minCode, ratOfCode_mulCode, ratOfCode_subCode, ratOfCode_quarterCode]
  ring_nf

theorem ratOfCode_normLo (ac bc : RatCode) :
    ratOfCode (normLo ac bc)
      = (ratOfCode ac + ratOfCode bc) / 2 - min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) := by
  rw [normLo, ratOfCode_subCode, ratOfCode_deltaCode, midCode, ratOfCode_mulCode,
    ratOfCode_addCode, ratOfCode_halfCode]
  ring_nf

theorem ratOfCode_normHi (ac bc : RatCode) :
    ratOfCode (normHi ac bc)
      = (ratOfCode ac + ratOfCode bc) / 2 + min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) := by
  rw [normHi, ratOfCode_addCode, ratOfCode_deltaCode, midCode, ratOfCode_mulCode,
    ratOfCode_addCode, ratOfCode_halfCode]
  ring_nf

section NormProps

variable {ac bc : RatCode}
  (h : ((ratOfCode ac : ℚ) : ℝ) < ((ratOfCode bc : ℚ) : ℝ))

include h

/-- The normalized interval starts strictly inside. -/
theorem lt_normLo : ((ratOfCode ac : ℚ) : ℝ) < ((ratOfCode (normLo ac bc) : ℚ) : ℝ) := by
  have hq : (ratOfCode ac : ℚ) < ratOfCode bc := by exact_mod_cast h
  have hd : min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) ≤ (ratOfCode bc - ratOfCode ac) / 4 :=
    min_le_left _ _
  have : (ratOfCode ac : ℚ) < ratOfCode (normLo ac bc) := by
    rw [ratOfCode_normLo]; linarith
  exact_mod_cast this

/-- It is nonempty. -/
theorem normLo_lt_normHi :
    ((ratOfCode (normLo ac bc) : ℚ) : ℝ) < ((ratOfCode (normHi ac bc) : ℚ) : ℝ) := by
  have hq : (ratOfCode ac : ℚ) < ratOfCode bc := by exact_mod_cast h
  have hpos : (0 : ℚ) < min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) :=
    lt_min (by linarith) (by norm_num)
  have : (ratOfCode (normLo ac bc) : ℚ) < ratOfCode (normHi ac bc) := by
    rw [ratOfCode_normLo, ratOfCode_normHi]; linarith
  exact_mod_cast this

/-- It ends strictly inside. -/
theorem normHi_lt : ((ratOfCode (normHi ac bc) : ℚ) : ℝ) < ((ratOfCode bc : ℚ) : ℝ) := by
  have hq : (ratOfCode ac : ℚ) < ratOfCode bc := by exact_mod_cast h
  have hd : min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) ≤ (ratOfCode bc - ratOfCode ac) / 4 :=
    min_le_left _ _
  have : (ratOfCode (normHi ac bc) : ℚ) < ratOfCode bc := by
    rw [ratOfCode_normHi]; linarith
  exact_mod_cast this

omit h in
/-- **The width bound the nest needs**: at most `1/2`, hence at most `2⁻⁰`, whatever the request. -/
theorem normHi_sub_normLo_le :
    ((ratOfCode (normHi ac bc) : ℚ) : ℝ) - ((ratOfCode (normLo ac bc) : ℚ) : ℝ) ≤ 1 / 2 := by
  have hd : min ((ratOfCode bc - ratOfCode ac) / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hQ : (ratOfCode (normHi ac bc) : ℚ) - ratOfCode (normLo ac bc) ≤ 1 / 2 := by
    rw [ratOfCode_normLo, ratOfCode_normHi]; linarith
  have h' := (Rat.cast_le (K := ℝ)).mpr hQ
  push_cast at h'
  exact h'

end NormProps

/-- A request, assembled. -/
def mkRequest (i lo hi err : ℕ) : ℕ := Nat.pair i (Nat.pair lo (Nat.pair hi err))

@[simp] theorem reqCentre_mkRequest (i lo hi err : ℕ) :
    reqCentre (mkRequest i lo hi err) = i := by simp [reqCentre, mkRequest]
@[simp] theorem reqLo_mkRequest (i lo hi err : ℕ) :
    reqLo (mkRequest i lo hi err) = lo := by simp [reqLo, mkRequest]
@[simp] theorem reqHi_mkRequest (i lo hi err : ℕ) :
    reqHi (mkRequest i lo hi err) = hi := by simp [reqHi, mkRequest]
@[simp] theorem reqErr_mkRequest (i lo hi err : ℕ) :
    reqErr (mkRequest i lo hi err) = err := by simp [reqErr, mkRequest]

/-- **The indexing convention.** -/
def IsNestRun (μ : ProbabilityMeasure X) (i : ℕ) (state : ℕ → ℕ) : Prop :=
  ∀ n, ThinClosedAnnulusStep P μ
    (mkRequest i (resLo (state n)) (resHi (state n)) (halfPowCode n)) (state (n + 1))

section NestRun

variable {P}
variable {μ : ProbabilityMeasure X} {i : ℕ} {state : ℕ → ℕ} (h : IsNestRun P μ i state)

include h

omit [BorelSpace X] in
theorem nestRun_lo_lt (n : ℕ) :
    ((ratOfCode (resLo (state n)) : ℚ) : ℝ)
      < ((ratOfCode (resLo (state (n + 1))) : ℚ) : ℝ) := by
  have := (h n).1; simpa using this

omit [BorelSpace X] in
theorem nestRun_lo_lt_hi (n : ℕ) :
    ((ratOfCode (resLo (state (n + 1))) : ℚ) : ℝ)
      < ((ratOfCode (resHi (state (n + 1))) : ℚ) : ℝ) := (h n).2.1

omit [BorelSpace X] in
theorem nestRun_hi_lt (n : ℕ) :
    ((ratOfCode (resHi (state (n + 1))) : ℚ) : ℝ)
      < ((ratOfCode (resHi (state n)) : ℚ) : ℝ) := by
  have := (h n).2.2.1; simpa using this

omit [BorelSpace X] in
theorem nestRun_width_step (n : ℕ) :
    ((ratOfCode (resHi (state (n + 1))) : ℚ) : ℝ)
        - ((ratOfCode (resLo (state (n + 1))) : ℚ) : ℝ)
      ≤ (((ratOfCode (resHi (state n)) : ℚ) : ℝ)
          - ((ratOfCode (resLo (state n)) : ℚ) : ℝ)) / 2 := by
  have := (h n).2.2.2.1; simpa using this

omit [BorelSpace X] in
/-- Every SELECTED interval is certified thin at its own dyadic error. -/
theorem nestRun_mass (n : ℕ) :
    (μ.toMeasure (closedAnnulus (P.dense i)
        ((ratOfCode (resLo (state (n + 1))) : ℚ) : ℝ)
        ((ratOfCode (resHi (state (n + 1))) : ℚ) : ℝ))).toReal < (2 : ℝ)⁻¹ ^ n := by
  have hm := (h n).2.2.2.2
  simp only [reqCentre_mkRequest, reqErr_mkRequest, ratOfCode_halfPowCode] at hm
  have hcast : ((((2 : ℚ)⁻¹ ^ n : ℚ)) : ℝ) = (2 : ℝ)⁻¹ ^ n := by push_cast; ring
  rwa [hcast] at hm

omit [BorelSpace X] in
/-- The dyadic width bound, from normalization plus halving. -/
theorem nestRun_width (hw₀ : ((ratOfCode (resHi (state 0)) : ℚ) : ℝ)
      - ((ratOfCode (resLo (state 0)) : ℚ) : ℝ) ≤ 1 / 2) (n : ℕ) :
    ((ratOfCode (resHi (state n)) : ℚ) : ℝ) - ((ratOfCode (resLo (state n)) : ℚ) : ℝ)
      ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  induction n with
  | zero => simpa using hw₀
  | succ k ih =>
    have hstep := nestRun_width_step h k
    have : (2 : ℝ)⁻¹ ^ (k + 1) / 2 = (2 : ℝ)⁻¹ ^ (k + 2) := by ring
    linarith [hstep, ih]

omit [BorelSpace X] in
/-- **The iterator's specification**, assembled from the three abstract nest theorems. -/
theorem nestRun_spec (hw₀ : ((ratOfCode (resHi (state 0)) : ℚ) : ℝ)
      - ((ratOfCode (resLo (state 0)) : ℚ) : ℝ) ≤ 1 / 2) :
    ∃ ρ : ℝ, realRep.Names (fun n => resLo (state (n + 1))) ρ ∧
      ((ratOfCode (resLo (state 0)) : ℚ) : ℝ) < ρ ∧
      ρ < ((ratOfCode (resHi (state 0)) : ℚ) : ℝ) ∧
      μ.toMeasure (sphere (P.dense i) ρ) = 0 := by
  obtain ⟨ρ, hρa, hρb, hρ0a, hρ0b⟩ := nest_exists_limit
    (a := fun n => ((ratOfCode (resLo (state (n + 1))) : ℚ) : ℝ))
    (b := fun n => ((ratOfCode (resHi (state (n + 1))) : ℚ) : ℝ))
    (fun n => nestRun_lo_lt h (n + 1)) (fun n => nestRun_hi_lt h (n + 1))
    (fun n => nestRun_lo_lt_hi h n)
  refine ⟨ρ, ?_, ?_, ?_, ?_⟩
  · refine nest_names (fun n => rfl) hρa hρb fun n => ?_
    have hw := nestRun_width h hw₀ (n + 1)
    have hpow : (2 : ℝ)⁻¹ ^ (n + 2) ≤ (2 : ℝ)⁻¹ ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  · exact lt_trans (nestRun_lo_lt h 0) hρ0a
  · exact lt_trans hρ0b (nestRun_hi_lt h 0)
  · refine nest_sphere_null hρa hρb (ε := fun n => (2 : ℝ)⁻¹ ^ n)
      (fun n => (nestRun_mass h n).le) ?_
    simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)
      (by norm_num : (2:ℝ)⁻¹ < 1)

end NestRun

/-- The centre carried by an iterator argument. -/
def argCentre (a : ℕ) : ℕ := a.unpair.1
/-- The requested lower endpoint carried by an iterator argument. -/
def argLo (a : ℕ) : RatCode := a.unpair.2.unpair.1
/-- The requested upper endpoint carried by an iterator argument. -/
def argHi (a : ℕ) : RatCode := a.unpair.2.unpair.2

@[simp] theorem argCentre_pair (i ac bc : ℕ) :
    argCentre (Nat.pair i (Nat.pair ac bc)) = i := by simp [argCentre]
@[simp] theorem argLo_pair (i ac bc : ℕ) :
    argLo (Nat.pair i (Nat.pair ac bc)) = ac := by simp [argLo]
@[simp] theorem argHi_pair (i ac bc : ℕ) :
    argHi (Nat.pair i (Nat.pair ac bc)) = bc := by simp [argHi]

/-- The normalized initial state. -/
def initFn (a : ℕ) : ℕ := Nat.pair (normLo (argLo a) (argHi a)) (normHi (argLo a) (argHi a))

/-- The request posed at stage `k` from the running state. -/
def requestFn (v : ℕ) : ℕ :=
  mkRequest (argCentre v.unpair.1) (resLo v.unpair.2.unpair.2) (resHi v.unpair.2.unpair.2)
    (halfPowCode v.unpair.2.unpair.1)

theorem primrec₂_minCode : Primrec₂ minCode :=
  Primrec.ite (primrecPred_ratLt Primrec.fst Primrec.snd) Primrec.fst Primrec.snd

private theorem primrec_argCentre : Primrec argCentre := primrec_unpairFst
private theorem primrec_argLo : Primrec argLo := primrec_unpairFst.comp primrec_unpairSnd
private theorem primrec_argHi : Primrec argHi := primrec_unpairSnd.comp primrec_unpairSnd
private theorem primrec_resLo : Primrec resLo := primrec_unpairFst
private theorem primrec_resHi : Primrec resHi := primrec_unpairSnd

private theorem primrec₂_midCode : Primrec₂ midCode :=
  primrec₂_mulCode.comp (primrec₂_addCode.comp Primrec.fst Primrec.snd)
    (Primrec.const halfCode)

private theorem primrec₂_deltaCode : Primrec₂ deltaCode :=
  primrec₂_minCode.comp
    (primrec₂_mulCode.comp (primrec₂_subCode.comp Primrec.snd Primrec.fst)
      (Primrec.const quarterCode))
    (Primrec.const quarterCode)

private theorem primrec₂_normLo : Primrec₂ normLo :=
  primrec₂_subCode.comp primrec₂_midCode primrec₂_deltaCode

private theorem primrec₂_normHi : Primrec₂ normHi :=
  primrec₂_addCode.comp primrec₂_midCode primrec₂_deltaCode

private theorem primrec_initFn : Primrec initFn :=
  Primrec₂.natPair.comp (primrec₂_normLo.comp primrec_argLo primrec_argHi)
    (primrec₂_normHi.comp primrec_argLo primrec_argHi)

private theorem primrec_requestFn : Primrec requestFn := by
  have hst : Primrec fun v : ℕ => v.unpair.2.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairSnd
  have hk : Primrec fun v : ℕ => v.unpair.2.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairSnd
  exact Primrec₂.natPair.comp (primrec_argCentre.comp primrec_unpairFst)
    (Primrec₂.natPair.comp (primrec_resLo.comp hst)
      (Primrec₂.natPair.comp (primrec_resHi.comp hst) (primrec_halfPowCode.comp hk)))

/-- **The iterator, with its evaluation recurrence and its specification.** Totality is a plain
induction on the stage: normalization orders the initial endpoints, and each transition's own
contract orders the next ones, so the next request is always valid.

Stated relative to the RAW weak-name oracle: no packing, no substitution. Both belong to the
wrapper. -/
theorem exists_iterCode :
    ∃ iterCode : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure X) (i ac bc : ℕ),
      WeakMeasureNames P p μ →
      ((ratOfCode ac : ℚ) : ℝ) < ((ratOfCode bc : ℚ) : ℝ) →
      ∃ state : ℕ → ℕ,
        (∀ k, iterCode.eval p (Nat.pair (Nat.pair i (Nat.pair ac bc)) k)
          = Part.some (state k)) ∧
        state 0 = Nat.pair (normLo ac bc) (normHi ac bc) ∧
        IsNestRun P μ i state := by
  classical
  obtain ⟨stepCode, hstep⟩ := exists_thinStepCode P
  obtain ⟨initCode, hinit⟩ := exists_ofNatFnCode primrec_initFn.to_comp
  obtain ⟨reqCode, hreqCode⟩ := exists_ofNatFnCode primrec_requestFn.to_comp
  refine ⟨OracleCode.prec initCode (OracleCode.comp stepCode reqCode),
    fun p μ i ac bc hp hlt => ?_⟩
  set a : ℕ := Nat.pair i (Nat.pair ac bc) with hadef
  set iter : OracleCode := OracleCode.prec initCode (OracleCode.comp stepCode reqCode) with hiter
  -- the successor equation, once
  have hsucc : ∀ (k s : ℕ), iter.eval p (Nat.pair a k) = Part.some s →
      ∀ r, r ∈ stepCode.eval p (mkRequest i (resLo s) (resHi s) (halfPowCode k)) →
      iter.eval p (Nat.pair a (k + 1)) = Part.some r := by
    intro k s hs r hr
    rw [hiter, eval_prec_succ, hs, Part.bind_eq_bind, Part.bind_some,
      eval_comp_some (hreqCode p (Nat.pair a (Nat.pair k s)))]
    simpa only [requestFn, Nat.unpair_pair, hadef, argCentre_pair] using Part.eq_some_iff.mpr hr
  -- validity of the request posed from an ordered state
  have hvalid : ∀ (k s : ℕ), ((ratOfCode (resLo s) : ℚ) : ℝ) < ((ratOfCode (resHi s) : ℚ) : ℝ) →
      ValidIntervalRequest (mkRequest i (resLo s) (resHi s) (halfPowCode k)) := by
    intro k s hord
    refine ⟨by simpa using hord, ?_⟩
    simp only [reqErr_mkRequest, ratOfCode_halfPowCode]
    positivity
  -- totality, together with the endpoint order the next request needs
  have key : ∀ k, ∃ s, iter.eval p (Nat.pair a k) = Part.some s ∧
      ((ratOfCode (resLo s) : ℚ) : ℝ) < ((ratOfCode (resHi s) : ℚ) : ℝ) := by
    intro k
    induction k with
    | zero =>
      refine ⟨initFn a, by rw [hiter, eval_prec_zero, hinit p a], ?_⟩
      simp only [initFn, resLo, resHi, Nat.unpair_pair, hadef, argLo_pair, argHi_pair]
      exact normLo_lt_normHi hlt
    | succ k ih =>
      obtain ⟨s, hs, hord⟩ := ih
      obtain ⟨r, hr, hcontract⟩ := hstep p μ _ hp (hvalid k s hord)
      exact ⟨r, hsucc k s hs r hr, hcontract.2.1⟩
  choose state hstate hord using key
  refine ⟨state, hstate, ?_, ?_⟩
  · have h0 : iter.eval p (Nat.pair a 0) = Part.some (initFn a) := by
      rw [hiter, eval_prec_zero, hinit p a]
    have := Part.some_injective ((hstate 0).symm.trans h0)
    simpa only [initFn, hadef, argLo_pair, argHi_pair] using this
  · intro k
    obtain ⟨r, hr, hcontract⟩ := hstep p μ _ hp (hvalid k (state k) (hord k))
    have : state (k + 1) = r :=
      Part.some_injective ((hstate (k + 1)).symm.trans (hsucc k (state k) (hstate k) r hr))
    rw [this]
    exact hcontract

private theorem computes_evenCode : OracleCode.evenCode.Computes Baire.evenPart := by
  intro q n
  refine Part.eq_some_iff.mpr ?_
  exact (OracleCode.mem_evalStream.mp
    (by rw [OracleCode.evalStream_evenCode]; exact Part.mem_some _)) n

/-- **The interval selector**: one code, every measure, centre and coded interval, one
`realRep` name out. -/
theorem exists_radiusSelectorCode :
    ∃ c : OracleCode,
      ∀ (p : Baire) (μ : ProbabilityMeasure X) (i : ℕ) (ac bc : RatCode),
        WeakMeasureNames P p μ →
        0 ≤ ((ratOfCode ac : ℚ) : ℝ) →
        ((ratOfCode ac : ℚ) : ℝ) < ((ratOfCode bc : ℚ) : ℝ) →
        ∃ r ∈ c.evalStream (radiusPack p i ac bc),
          ∃ ρ : ℝ,
            realRep.Names r ρ ∧
            ((ratOfCode ac : ℚ) : ℝ) < ρ ∧
            ρ < ((ratOfCode bc : ℚ) : ℝ) ∧
            μ.toMeasure (sphere (P.dense i) ρ) = 0 := by
  classical
  obtain ⟨iterCode, hiter⟩ := exists_iterCode P
  obtain ⟨argCode, hargCode⟩ := exists_prefixPostCode (b := fun _ _ => 2)
    (Primrec.const 2)
    (g := fun v => Nat.pair ((Denumerable.ofNat (List ℕ) v.unpair.2).getD 1 0) (v.unpair.1 + 1))
    (Primrec₂.natPair.comp
      ((Primrec.list_getD 0).comp ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd)
        (Primrec.const 1))
      (Primrec.succ.comp primrec_unpairFst))
  refine ⟨OracleCode.comp OracleCode.left
      (OracleCode.comp (iterCode.subst OracleCode.evenCode) argCode),
    fun p μ i ac bc hp _ hlt => ?_⟩
  obtain ⟨state, hstate, hstate0, hrun⟩ := hiter p μ i ac bc hp hlt
  set F : Baire := radiusPack p i ac bc with hF
  have hFeven : F.evenPart = p := by rw [hF, radiusPack, Baire.evenPart_interleave]
  have hF1 : F 1 = Nat.pair i (Nat.pair ac bc) := by
    rw [hF, radiusPack]; simp [Baire.interleave]
  have heval : ∀ n, (OracleCode.comp OracleCode.left
      (OracleCode.comp (iterCode.subst OracleCode.evenCode) argCode)).eval F n
      = Part.some (resLo (state (n + 1))) := by
    intro n
    have harg : argCode.eval F n
        = Part.some (Nat.pair (Nat.pair i (Nat.pair ac bc)) (n + 1)) := by
      rw [hargCode F n]
      congr 1
      simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
      rw [streamTake_getD F (by omega : 1 < 2), hF1]
    have hinner : (OracleCode.comp (iterCode.subst OracleCode.evenCode) argCode).eval F n
        = Part.some (state (n + 1)) := by
      rw [eval_comp_some harg, eval_subst computes_evenCode, hFeven, hstate (n + 1)]
    rw [eval_comp_some hinner, eval_left]
    rfl
  refine ⟨fun n => resLo (state (n + 1)), OracleCode.mem_evalStream.mpr fun n => ?_, ?_⟩
  · rw [heval n]; exact Part.mem_some _
  have hw₀ : ((ratOfCode (resHi (state 0)) : ℚ) : ℝ)
      - ((ratOfCode (resLo (state 0)) : ℚ) : ℝ) ≤ 1 / 2 := by
    rw [hstate0]
    simpa only [resLo, resHi, Nat.unpair_pair] using normHi_sub_normLo_le
  obtain ⟨ρ, hnames, hlo, hhi, hsphere⟩ := nestRun_spec hrun hw₀
  refine ⟨ρ, hnames, ?_, ?_, hsphere⟩
  · refine lt_trans (lt_normLo hlt) ?_
    rw [hstate0] at hlo
    simpa only [resLo, Nat.unpair_pair] using hlo
  · refine lt_trans ?_ (normHi_lt hlt)
    rw [hstate0] at hhi
    simpa only [resHi, Nat.unpair_pair] using hhi

/-! ### The basis, semantically -/

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

end NullSphereRadius

end ComputableAnalysis
