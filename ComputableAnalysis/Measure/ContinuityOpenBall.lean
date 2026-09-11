/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.REPredStages
import ComputableAnalysis.Measure.ContinuityOpen
import ComputableAnalysis.Metric.Real

/-!
# Continuity-open names of presented balls

A presented ball `B(tᵢ, ρ)` whose sphere is `µ`-null is an effective `µ`-continuity open, and
its two-track name can be *computed*: the even track enumerates the ball's rational sub-balls,
the odd track the presented balls certified apart from it by `ρ + r' < d(tᵢ, tⱼ)`
(Ackerman–Freer–Roy, (3.7)). Two effective versions are provided, both free of real-number
tests: one for a coded rational radius, where the apartness test is a staged certificate read
off the presentation's `gtSemidec`, and one for a real radius given by a fast Cauchy name,
where each track consults the name's stage-`s` approximant with its error subtracted or added.

## Main definitions and results

* `afrEven`, `afrOdd`, `contSetNames_afr` — the semantic streams and their certification from
  a null sphere.
* `exists_afrOddCert`, `afrOddEffective`, `afrEvenEffective` — the rational-radius effective
  tracks, with `openOf_afrOddEffective` and the uniform `Primrec` facts.
* `exists_distGtCert` — the raw staged apartness semidecider at an arbitrary threshold code.
* `afrReal`, `contSetNames_afrReal`, `exists_afrRealEvalCode` — the real-radius name and the
  code evaluating it uniformly from the centre index and the radius name.

## Implementation notes

The streams are built with no measure-theoretic input; the null-sphere and positive-radius
promises enter only in the certification theorems. `gtSemidec` is uniform in all of its
coordinates, which is what keeps the quantifier order `∃ code, ∀ radius` that every downstream
realizer needs.
-/

open MeasureTheory Metric Encodable Denumerable

namespace ComputableAnalysis

open OracleCode

section ContinuityOpenBall

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {P : ComputableMetricPresentation X}

/-- The even track: the ball as the union of its rational sub-balls. Presentation-free — it
names the centre by index and the radii by code. -/
noncomputable def afrEven (i : ℕ) (ρ : ℝ) : Baire := fun k =>
  if ((ratOfCode k : ℚ) : ℝ) < ρ then Nat.pair i k else Nat.pair i zeroCode

variable (P)

/-- **AFR's odd track (3.7).** The presented balls certified apart from `B(tᵢ, ρ)` by
`ρ + r' < d(tᵢ, tⱼ)`. Entries failing the test are neutralised to a radius-`0` ball, so the
union is exactly over the certified ones. -/
noncomputable def afrOdd (i : ℕ) (ρ : ℝ) : Baire := fun k =>
  if ((ratOfCode k.unpair.2 : ℚ) : ℝ) + ρ < dist (P.dense i) (P.dense k.unpair.1)
  then k else Nat.pair 0 zeroCode

variable {P}

omit [MeasurableSpace X] [BorelSpace X] in
theorem openOf_afrEven (i : ℕ) (ρ : ℝ) :
    openOf P (afrEven i ρ) = ball (P.dense i) ρ := by
  classical
  rw [openOf]
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => ?_) fun x hx => ?_
  · by_cases hk : ((ratOfCode k : ℚ) : ℝ) < ρ
    · simp only [afrEven, ite_eq_left hk, Nat.unpair_pair]
      exact ball_subset_ball hk.le
    · simp only [afrEven, ite_eq_right hk, Nat.unpair_pair, ratOfCode_zeroCode, Rat.cast_zero,
        ball_zero, Set.empty_subset]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (mem_ball.mp hx)
    obtain ⟨c, hc⟩ := ratOfCode_surjective q
    have hcr : ((ratOfCode c : ℚ) : ℝ) < ρ := by rw [hc]; exact_mod_cast hq2
    refine Set.mem_iUnion.mpr ⟨c, ?_⟩
    simp only [afrEven, ite_eq_left hcr, Nat.unpair_pair]
    exact mem_ball.mpr (by rw [hc]; exact_mod_cast hq1)

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The odd track names exactly the far region.** An equality, not merely an inclusion — which
is what makes the uncovered set exactly the sphere. -/
theorem openOf_afrOdd (i : ℕ) (ρ : ℝ) :
    openOf P (afrOdd P i ρ) = {x : X | ρ < dist x (P.dense i)} := by
  classical
  rw [openOf]
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => ?_) fun x hx => ?_
  · by_cases hk : ((ratOfCode k.unpair.2 : ℚ) : ℝ) + ρ < dist (P.dense i) (P.dense k.unpair.1)
    · simp only [afrOdd, ite_eq_left hk]
      intro y hy
      have h1 : dist y (P.dense k.unpair.1) < ((ratOfCode k.unpair.2 : ℚ) : ℝ) := mem_ball.mp hy
      -- the middle point must be `y`: it is `d(tᵢ,tⱼ) ≤ d(tᵢ,y) + d(y,tⱼ)` that is needed
      have h2 := dist_triangle (P.dense i) y (P.dense k.unpair.1)
      refine Set.mem_ofPred.mpr ?_
      rw [dist_comm]
      linarith
    · simp only [afrOdd, ite_eq_right hk, Nat.unpair_pair, ratOfCode_zeroCode, Rat.cast_zero,
        ball_zero, Set.empty_subset]
  · -- a point strictly beyond `ρ` is certified by a nearby dense point with a small radius
    have hx' : ρ < dist x (P.dense i) := hx
    obtain ⟨j, hj⟩ := P.denseRange.exists_dist_lt x
      (by linarith : (0 : ℝ) < (dist x (P.dense i) - ρ) / 3)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn
      (show (dist x (P.dense i) - ρ) / 3 < (dist x (P.dense i) - ρ) / 2 by linarith)
    obtain ⟨c, hc⟩ := ratOfCode_surjective q
    have hqc : ((ratOfCode c : ℚ) : ℝ) = (q : ℝ) := by rw [hc]
    -- stated in reduced form, so `ite_eq_left` matches the goal after `Nat.unpair_pair`
    have hcert : (q : ℝ) + ρ < dist (P.dense i) (P.dense j) := by
      have h2 := dist_triangle (P.dense i) (P.dense j) x
      rw [dist_comm (P.dense i) x, dist_comm (P.dense j) x] at h2
      have hq2' : (q : ℝ) < (dist x (P.dense i) - ρ) / 2 := hq2
      linarith [hj, hx']
    refine Set.mem_iUnion.mpr ⟨Nat.pair j c, ?_⟩
    simp only [afrOdd, Nat.unpair_pair, hqc, ite_eq_left hcert]
    exact mem_ball.mpr (by linarith [hj, hq1])

omit [MeasurableSpace X] [BorelSpace X] in
/-- The ball and the far region cover everything but the sphere — an equality, so nothing is
lost and the sphere is exactly the set that must be null. -/
theorem ball_union_far (i : ℕ) (ρ : ℝ) :
    ball (P.dense i) ρ ∪ {x : X | ρ < dist x (P.dense i)}
      = (Metric.sphere (P.dense i) ρ)ᶜ := by
  ext x
  simp only [Set.mem_union, mem_ball, Set.mem_ofPred_eq, Set.mem_compl_iff, Metric.mem_sphere]
  constructor
  · rintro (hlt | hgt)
    · exact ne_of_lt hlt
    · exact (ne_of_lt hgt).symm
  · exact fun hne => lt_or_gt_of_ne hne

/-- **The ball's continuity-open name, for the explicit stream.** Not `∃ uv`: this is the named
AFR stream, so a realizer can compute it and then certify it.

Note the division of labour the hypothesis buys — the stream is built with no measure-theoretic
input at all, and `hsphere` is used only to certify that what was built is a valid
continuity-open name. -/
theorem contSetNames_afr {μ : ProbabilityMeasure X} (i : ℕ) {ρ : ℝ}
    (hsphere : μ.toMeasure (Metric.sphere (P.dense i) ρ) = 0) :
    openOf P (Baire.interleave (afrEven i ρ) (afrOdd P i ρ)).evenPart = ball (P.dense i) ρ ∧
      ContinuityOpenNames P μ (Baire.interleave (afrEven i ρ) (afrOdd P i ρ)) := by
  have hVopen : IsOpen {x : X | ρ < dist x (P.dense i)} := by
    rw [← openOf_afrOdd (P := P) i ρ]
    exact isOpen_openOf P _
  have hdisj : Disjoint (ball (P.dense i) ρ) {x : X | ρ < dist x (P.dense i)} := by
    rw [Set.disjoint_left]
    intro y hy hy2
    exact absurd (mem_ball.mp hy) (not_lt.mpr (le_of_lt hy2))
  refine ⟨by simpa using openOf_afrEven i ρ, ?_, ?_⟩
  · simp only [Baire.evenPart_interleave, Baire.oddPart_interleave,
      openOf_afrEven i ρ, openOf_afrOdd]
    exact hdisj
  · simp only [Baire.evenPart_interleave, Baire.oddPart_interleave,
      openOf_afrEven i ρ, openOf_afrOdd]
    rw [← measure_union hdisj hVopen.measurableSet, ball_union_far]
    have hc := measure_add_measure_compl (μ := μ.toMeasure)
      (Metric.isClosed_sphere (x := P.dense i) (ε := ρ)).measurableSet
    rw [measure_univ, hsphere, zero_add] at hc
    exact hc

variable (P)
omit [MeasurableSpace X] [BorelSpace X] in
/-- **The staged apartness certificate.** Primitive recursive in the centre index `i`, the packed
candidate ball `k = ⟨j, c⟩`, the radius code `rc` and a stage `t`; sound for the strict apartness
`ρ + r' < d(tᵢ, tⱼ)` and eventually firing whenever that strict inequality holds.

Uniform in `rc` as well as `i`: `gtSemidec` is uniform in all of its coordinates, so fixing a
radius here would buy nothing and would break the quantifier order every downstream code needs
(`∃ c, ∀ … rc`, never `∀ rc, ∃ c`).

No persistence clause, deliberately: the enumeration below reads `(k, t)` pairs, so a certificate
firing at one stage is already enumerated and monotonicity would buy nothing. -/
theorem exists_afrOddCert :
    ∃ fires : ℕ × ℕ × RatCode → ℕ → Bool, Primrec₂ fires ∧
      (∀ i k rc t, fires (i, k, rc) t = true →
        ((ratOfCode rc : ℚ) : ℝ) + ((ratOfCode k.unpair.2 : ℚ) : ℝ)
          < dist (P.dense i) (P.dense k.unpair.1)) ∧
      (∀ i k rc, ((ratOfCode rc : ℚ) : ℝ) + ((ratOfCode k.unpair.2 : ℚ) : ℝ)
          < dist (P.dense i) (P.dense k.unpair.1) → ∃ t, fires (i, k, rc) t = true) := by
  obtain ⟨f, hfprim, hfiff⟩ := repred_exists_primrec_stages P.gtSemidec
  -- the sole arithmetic bridge: the coded threshold decodes to the sum of the two radii
  have hbridge : ∀ rc c : RatCode, ((ratOfCode (addCode rc c) : ℚ) : ℝ)
      = ((ratOfCode rc : ℚ) : ℝ) + ((ratOfCode c : ℚ) : ℝ) := by
    intro rc c
    rw [ratOfCode_addCode]
    push_cast
    ring
  refine ⟨fun w t => f (w.1, w.2.1.unpair.1, addCode w.2.2 w.2.1.unpair.2) t, ?_, ?_, ?_⟩
  · exact hfprim.comp ((Primrec.fst.comp Primrec.fst).pair
      ((primrec_unpairFst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))).pair
        (primrec₂_addCode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
          (primrec_unpairSnd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))))
      Primrec.snd
  · intro i k rc t ht
    have := (hfiff (i, k.unpair.1, addCode rc k.unpair.2)).mpr ⟨t, ht⟩
    rwa [hbridge] at this
  · intro i k rc hk
    refine (hfiff (i, k.unpair.1, addCode rc k.unpair.2)).mp ?_
    rwa [hbridge]

variable {P}

/-- **The effective odd track.** The stream index is a pair `n = ⟨k, t⟩`: emit the presented ball
`k` when the certificate fires at stage `t`, and the inert radius-`0` ball otherwise. Total, and
free of any real-number test. -/
def afrOddEffective (fires : ℕ × ℕ × RatCode → ℕ → Bool) (rc : RatCode) (i : ℕ) : Baire :=
  fun n => if fires (i, n.unpair.1, rc) n.unpair.2 = true then n.unpair.1 else Nat.pair 0 zeroCode

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The shared far-region anchor.** Any stream that emits only certified-far balls (or empty
ones) and emits every certified-far ball names exactly the set the classical odd track names.
No measure, no positivity, no coding: the two clauses below are the whole content of a dovetail.

This is the helper the two odd-track consumers turned out to share — the rational-radius track
below and the real-radius track further down instantiate it with different tests and different
dovetail shapes, which is why it abstracts over the emitted stream rather than over a Boolean
family. -/
theorem openOf_eq_openOf_afrOdd {u : Baire} {ρ : ℝ} (i : ℕ)
    (hsound : ∀ n, ρ + ((ratOfCode (u n).unpair.2 : ℚ) : ℝ)
        < dist (P.dense i) (P.dense (u n).unpair.1)
      ∨ ((ratOfCode (u n).unpair.2 : ℚ) : ℝ) ≤ 0)
    (hcomp : ∀ k, ρ + ((ratOfCode k.unpair.2 : ℚ) : ℝ)
        < dist (P.dense i) (P.dense k.unpair.1) → ∃ n, u n = k) :
    openOf P u = openOf P (afrOdd P i ρ) := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · rw [openOf, openOf]
    refine Set.iUnion_subset fun n => ?_
    rcases hsound n with hfar | hzero
    · have hk : afrOdd P i ρ (u n) = u n := by
        simp only [afrOdd]
        exact ite_eq_left (by linarith)
      exact Set.subset_iUnion_of_subset (u n) (by rw [hk])
    · have hempty : ball (P.dense (u n).unpair.1) ((ratOfCode (u n).unpair.2 : ℚ) : ℝ) = ∅ :=
        ball_eq_empty.mpr hzero
      rw [hempty]
      exact Set.empty_subset _
  · rw [openOf, openOf]
    refine Set.iUnion_subset fun k => ?_
    by_cases hk : ((ratOfCode k.unpair.2 : ℚ) : ℝ) + ρ < dist (P.dense i) (P.dense k.unpair.1)
    · obtain ⟨n, hn⟩ := hcomp k (by linarith)
      refine Set.subset_iUnion_of_subset n ?_
      rw [hn]
      simp only [afrOdd, ite_eq_left hk]
      exact subset_rfl
    · simp only [afrOdd, ite_eq_right hk, Nat.unpair_pair, ratOfCode_zeroCode, Rat.cast_zero,
        ball_zero, Set.empty_subset]

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The promise-free anchor for the rational-radius track**, now a short instantiation of the
shared one: soundness keeps every emitted ball inside, completeness reaches every ball the
classical track emits, and the inert entry contributes the empty ball. -/
theorem openOf_afrOddEffective {fires : ℕ × ℕ × RatCode → ℕ → Bool} {ρ : ℝ} (rc : RatCode)
    (i : ℕ)
    (hsound : ∀ k t, fires (i, k, rc) t = true →
      ρ + ((ratOfCode k.unpair.2 : ℚ) : ℝ) < dist (P.dense i) (P.dense k.unpair.1))
    (hcomplete : ∀ k, ρ + ((ratOfCode k.unpair.2 : ℚ) : ℝ)
        < dist (P.dense i) (P.dense k.unpair.1) → ∃ t, fires (i, k, rc) t = true) :
    openOf P (afrOddEffective fires rc i) = openOf P (afrOdd P i ρ) := by
  classical
  refine openOf_eq_openOf_afrOdd i (fun n => ?_) (fun k hk => ?_)
  · by_cases hn : fires (i, n.unpair.1, rc) n.unpair.2 = true
    · exact Or.inl (by
        rw [show afrOddEffective fires rc i n = n.unpair.1 from by
          simp only [afrOddEffective, ite_eq_left hn]]
        exact hsound n.unpair.1 n.unpair.2 hn)
    · refine Or.inr ?_
      rw [show afrOddEffective fires rc i n = Nat.pair 0 zeroCode from by
        simp only [afrOddEffective, ite_eq_right hn]]
      simp [ratOfCode_zeroCode]
  · obtain ⟨t, ht⟩ := hcomplete k hk
    exact ⟨Nat.pair k t, by simp only [afrOddEffective, Nat.unpair_pair]; exact ite_eq_left ht⟩

/-- **The effective even track.** The radius test is now a comparison of two rational *codes*,
decidable outright — no semidecision and no stage parameter, because the even track never
compares a code against a distance. -/
def afrEvenEffective (rc : RatCode) (i : ℕ) : Baire := fun k =>
  if ratOfCode k < ratOfCode rc then Nat.pair i k else Nat.pair i zeroCode

/-- The even anchor. The two tracks are equal on the nose: the coded comparison and the real
comparison are the same test, so nothing but the cast separates them. -/
theorem afrEvenEffective_eq (rc : RatCode) (i : ℕ) :
    afrEvenEffective rc i = afrEven i ((ratOfCode rc : ℚ) : ℝ) := by
  funext k
  simp only [afrEvenEffective, afrEven]
  by_cases h : ratOfCode k < ratOfCode rc
  · rw [ite_eq_left h, ite_eq_left (by exact_mod_cast h :
      ((ratOfCode k : ℚ) : ℝ) < ((ratOfCode rc : ℚ) : ℝ))]
  · rw [ite_eq_right h, ite_eq_right (by exact_mod_cast h :
      ¬ ((ratOfCode k : ℚ) : ℝ) < ((ratOfCode rc : ℚ) : ℝ))]

theorem primrec_afrEvenEffective_uniform :
    Primrec fun t : (RatCode × ℕ) × ℕ => afrEvenEffective t.1.1 t.1.2 t.2 :=
  Primrec.ite (primrecPred_ratLt Primrec.snd (Primrec.fst.comp Primrec.fst))
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.const zeroCode))

theorem primrec_afrOddEffective_uniform {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hfires : Primrec₂ fires) :
    Primrec fun t : (RatCode × ℕ) × ℕ => afrOddEffective fires t.1.1 t.1.2 t.2 := by
  have hg : Primrec fun t : (RatCode × ℕ) × ℕ =>
      fires (t.1.2, t.2.unpair.1, t.1.1) t.2.unpair.2 :=
    hfires.comp ((Primrec.snd.comp Primrec.fst).pair
      ((primrec_unpairFst.comp Primrec.snd).pair (Primrec.fst.comp Primrec.fst)))
      (primrec_unpairSnd.comp Primrec.snd)
  exact Primrec.ite (PrimrecRel.comp Primrec.eq hg (Primrec.const true))
    (primrec_unpairFst.comp Primrec.snd) (Primrec.const (Nat.pair 0 zeroCode))

attribute [local irreducible] afrEvenEffective afrOddEffective

variable (P)

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The raw staged apartness semidecider**, at an arbitrary threshold code. This is the shared
primitive: `exists_afrOddCert` is its rational-radius specialization (threshold `addCode rc c`),
and the real-radius track below composes it with the upper approximation instead. -/
theorem exists_distGtCert :
    ∃ gt : ℕ × ℕ × RatCode → ℕ → Bool, Primrec₂ gt ∧
      ∀ i j thr, ((ratOfCode thr : ℚ) : ℝ) < dist (P.dense i) (P.dense j)
        ↔ ∃ t, gt (i, j, thr) t = true := by
  obtain ⟨f, hfprim, hfiff⟩ := repred_exists_primrec_stages P.gtSemidec
  exact ⟨f, hfprim, fun i j thr => hfiff (i, j, thr)⟩

variable {P}

/-- The certified bounds a fast Cauchy name supplies at stage `s`. -/
private theorem realName_bounds {r : Baire} {ρ : ℝ} (hr : realRep.Names r ρ) (s : ℕ) :
    ((ratOfCode (r s) : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ s ≤ ρ ∧
      ρ ≤ ((ratOfCode (r s) : ℚ) : ℝ) + (2 : ℝ)⁻¹ ^ s := by
  have h : |((ratOfCode (r s) : ℚ) : ℝ) - ρ| ≤ (2 : ℝ)⁻¹ ^ s := by
    have := realPresentation.cauchyRep_names_iff.mp hr s
    rwa [Real.dist_eq] at this
  obtain ⟨h1, h2⟩ := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

/-- **The effective even track over a real radius.** Index `n = ⟨c, s⟩`: emit the ball of coded
radius `c` once `c` is certified below `ℓₛ`. -/
def afrEvenReal (r : Baire) (i : ℕ) : Baire := fun n =>
  if ratOfCode (addCode n.unpair.1 (halfPowCode n.unpair.2)) < ratOfCode (r n.unpair.2)
  then Nat.pair i n.unpair.1 else Nat.pair i zeroCode

private theorem evenTest_iff (r : Baire) (c s : ℕ) :
    ratOfCode (addCode c (halfPowCode s)) < ratOfCode (r s)
      ↔ ((ratOfCode c : ℚ) : ℝ) + (2 : ℝ)⁻¹ ^ s < ((ratOfCode (r s) : ℚ) : ℝ) := by
  rw [ratOfCode_addCode, ratOfCode_halfPowCode]
  constructor
  · intro h
    have h' := (Rat.cast_lt (K := ℝ)).mpr h
    push_cast at h'
    exact h'
  · intro h
    refine (Rat.cast_lt (K := ℝ)).mp ?_
    push_cast
    exact h

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The even anchor, promise-free.** The dovetail over the approximation stage names exactly
the open ball — for every real `ρ`, positive or not. -/
theorem openOf_afrEvenReal {r : Baire} {ρ : ℝ} (hr : realRep.Names r ρ) (i : ℕ) :
    openOf P (afrEvenReal r i) = ball (P.dense i) ρ := by
  classical
  rw [openOf]
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => ?_) fun x hx => ?_
  · by_cases h : ratOfCode (addCode n.unpair.1 (halfPowCode n.unpair.2)) < ratOfCode (r n.unpair.2)
    · simp only [afrEvenReal, ite_eq_left h, Nat.unpair_pair]
      refine ball_subset_ball ?_
      have h' := (evenTest_iff r n.unpair.1 n.unpair.2).mp h
      have hb := (realName_bounds hr n.unpair.2).1
      linarith
    · simp only [afrEvenReal, ite_eq_right h, Nat.unpair_pair, ratOfCode_zeroCode, Rat.cast_zero,
        ball_zero, Set.empty_subset]
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (mem_ball.mp hx)
    obtain ⟨c, hc⟩ := ratOfCode_surjective q
    obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one (by linarith : (0 : ℝ) < (ρ - (q : ℝ)) / 2)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have htest : ratOfCode (addCode c (halfPowCode s)) < ratOfCode (r s) := by
      refine (evenTest_iff r c s).mpr ?_
      have hb := (realName_bounds hr s).2
      rw [hc]
      linarith
    refine Set.mem_iUnion.mpr ⟨Nat.pair c s, ?_⟩
    simp only [afrEvenReal, Nat.unpair_pair, ite_eq_left htest]
    exact mem_ball.mpr (by rw [hc]; exact_mod_cast hq1)

/-- **The effective odd track over a real radius.** Index `n = ⟨k, ⟨s, t⟩⟩`: the ball `k = ⟨j, c⟩`
is emitted once the semidecider certifies `uₛ + ratOfCode c < d(tᵢ, tⱼ)` at stage `t`. The
coordinate carries both stages because both searches are unbounded. -/
def afrOddReal (gt : ℕ × ℕ × RatCode → ℕ → Bool) (r : Baire) (i : ℕ) : Baire := fun n =>
  if gt (i, n.unpair.1.unpair.1,
      addCode (addCode (r n.unpair.2.unpair.1) (halfPowCode n.unpair.2.unpair.1))
        n.unpair.1.unpair.2) n.unpair.2.unpair.2 = true
  then n.unpair.1 else Nat.pair 0 zeroCode

private theorem oddThreshold_val (r : Baire) (s c : ℕ) :
    ((ratOfCode (addCode (addCode (r s) (halfPowCode s)) c) : ℚ) : ℝ)
      = ((ratOfCode (r s) : ℚ) : ℝ) + (2 : ℝ)⁻¹ ^ s + ((ratOfCode c : ℚ) : ℝ) := by
  rw [ratOfCode_addCode, ratOfCode_addCode, ratOfCode_halfPowCode]
  push_cast
  ring

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The odd anchor, promise-free**, through the shared far-region lemma. Soundness needs only
`ρ ≤ uₛ`; completeness picks a stage at which `uₛ` has descended far enough, then the
semidecider's own stage. -/
theorem openOf_afrOddReal {gt : ℕ × ℕ × RatCode → ℕ → Bool} {r : Baire} {ρ : ℝ}
    (hgt : ∀ i j thr, ((ratOfCode thr : ℚ) : ℝ) < dist (P.dense i) (P.dense j)
      ↔ ∃ t, gt (i, j, thr) t = true)
    (hr : realRep.Names r ρ) (i : ℕ) :
    openOf P (afrOddReal gt r i) = openOf P (afrOdd P i ρ) := by
  classical
  refine openOf_eq_openOf_afrOdd i (fun n => ?_) (fun k hk => ?_)
  · by_cases hn : gt (i, n.unpair.1.unpair.1,
        addCode (addCode (r n.unpair.2.unpair.1) (halfPowCode n.unpair.2.unpair.1))
          n.unpair.1.unpair.2) n.unpair.2.unpair.2 = true
    · refine Or.inl ?_
      rw [show afrOddReal gt r i n = n.unpair.1 from by simp only [afrOddReal, ite_eq_left hn]]
      have hcert := (hgt i n.unpair.1.unpair.1 _).mpr ⟨_, hn⟩
      rw [oddThreshold_val] at hcert
      have hb := (realName_bounds hr n.unpair.2.unpair.1).2
      linarith
    · refine Or.inr ?_
      rw [show afrOddReal gt r i n = Nat.pair 0 zeroCode from by
        simp only [afrOddReal, ite_eq_right hn]]
      simp [ratOfCode_zeroCode]
  · obtain ⟨s, hs⟩ := exists_pow_lt_of_lt_one
      (by linarith : (0 : ℝ) < (dist (P.dense i) (P.dense k.unpair.1)
        - ρ - ((ratOfCode k.unpair.2 : ℚ) : ℝ)) / 2)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have hb := (realName_bounds hr s).1
    have hthr : ((ratOfCode (addCode (addCode (r s) (halfPowCode s)) k.unpair.2) : ℚ) : ℝ)
        < dist (P.dense i) (P.dense k.unpair.1) := by
      rw [oddThreshold_val]
      linarith
    obtain ⟨t, ht⟩ := (hgt i k.unpair.1 _).mp hthr
    refine ⟨Nat.pair k (Nat.pair s t), ?_⟩
    simp only [afrOddReal, Nat.unpair_pair]
    exact ite_eq_left ht

/-- **The AFR stream over a real radius.** -/
def afrReal (gt : ℕ × ℕ × RatCode → ℕ → Bool) (r : Baire) (i : ℕ) : Baire :=
  Baire.interleave (afrEvenReal r i) (afrOddReal gt r i)

variable (P)

/-- **The ball's continuity-open name, for a real radius.** The null-sphere promise enters here
and nowhere else: the construction above consults neither the measure nor the sign of `ρ`. -/
theorem contSetNames_afrReal {μ : ProbabilityMeasure X} {gt : ℕ × ℕ × RatCode → ℕ → Bool}
    {r : Baire} {ρ : ℝ}
    (hgt : ∀ i j thr, ((ratOfCode thr : ℚ) : ℝ) < dist (P.dense i) (P.dense j)
      ↔ ∃ t, gt (i, j, thr) t = true)
    (hr : realRep.Names r ρ) (i : ℕ)
    (hsphere : μ.toMeasure (Metric.sphere (P.dense i) ρ) = 0) :
    openOf P (afrReal gt r i).evenPart = ball (P.dense i) ρ ∧
      ContinuityOpenNames P μ (afrReal gt r i) := by
  have hE : openOf P (afrReal gt r i).evenPart
      = openOf P (Baire.interleave (afrEven i ρ) (afrOdd P i ρ)).evenPart := by
    simp only [afrReal, Baire.evenPart_interleave]
    rw [openOf_afrEvenReal hr i, openOf_afrEven i ρ]
  have hO : openOf P (afrReal gt r i).oddPart
      = openOf P (Baire.interleave (afrEven i ρ) (afrOdd P i ρ)).oddPart := by
    simp only [afrReal, Baire.oddPart_interleave]
    exact openOf_afrOddReal hgt hr i
  obtain ⟨hball, hcont⟩ := contSetNames_afr (P := P) (μ := μ) i hsphere
  exact ⟨hE.trans hball, ⟨by rw [hE, hO]; exact hcont.disjoint, by rw [hE, hO]; exact hcont.full⟩⟩

variable {P}

private def afrRealG (gt : ℕ × ℕ × RatCode → ℕ → Bool) (i : ℕ) (v : ℕ) : ℕ :=
  if v.unpair.1 % 2 = 0 then
    (if ratOfCode (addCode (v.unpair.1 / 2).unpair.1 (halfPowCode (v.unpair.1 / 2).unpair.2))
        < ratOfCode ((Denumerable.ofNat (List ℕ) v.unpair.2).getD (v.unpair.1 / 2).unpair.2 0)
      then Nat.pair i (v.unpair.1 / 2).unpair.1 else Nat.pair i zeroCode)
  else
    (if gt (i, (v.unpair.1 / 2).unpair.1.unpair.1,
        addCode (addCode ((Denumerable.ofNat (List ℕ) v.unpair.2).getD
            (v.unpair.1 / 2).unpair.2.unpair.1 0)
          (halfPowCode (v.unpair.1 / 2).unpair.2.unpair.1))
          (v.unpair.1 / 2).unpair.1.unpair.2) (v.unpair.1 / 2).unpair.2.unpair.2 = true
      then (v.unpair.1 / 2).unpair.1 else Nat.pair 0 zeroCode)

private theorem afrRealG_pack (gt : ℕ × ℕ × RatCode → ℕ → Bool) (i : ℕ) (r : Baire) (n : ℕ) :
    afrRealG gt i (Nat.pair n (encode (streamTake r (n + 1)))) = afrReal gt r i n := by
  have hhalf : n / 2 ≤ n := Nat.div_le_self n 2
  simp only [afrRealG, Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h : n % 2 = 0
  · have hs : (n / 2).unpair.2 < n + 1 :=
      lt_of_le_of_lt (le_trans (Nat.unpair_right_le _) hhalf) (Nat.lt_succ_self n)
    rw [ite_eq_left h, streamTake_getD _ hs]
    simp only [afrReal, Baire.interleave, ite_eq_left h, afrEvenReal]
  · have hs : (n / 2).unpair.2.unpair.1 < n + 1 :=
      lt_of_le_of_lt (le_trans (le_trans (Nat.unpair_left_le _) (Nat.unpair_right_le _)) hhalf)
        (Nat.lt_succ_self n)
    rw [ite_eq_right h, streamTake_getD _ hs]
    simp only [afrReal, Baire.interleave, ite_eq_right h, afrOddReal]

attribute [local irreducible] addCode subCode halfPowCode

private theorem primrec_evenBranch :
    Primrec fun q : ℕ × ℕ =>
      if ratOfCode (addCode (q.2.unpair.1 / 2).unpair.1 (halfPowCode (q.2.unpair.1 / 2).unpair.2))
          < ratOfCode ((Denumerable.ofNat (List ℕ) q.2.unpair.2).getD
              (q.2.unpair.1 / 2).unpair.2 0)
        then Nat.pair q.1 (q.2.unpair.1 / 2).unpair.1 else Nat.pair q.1 zeroCode := by
  have hL : Primrec fun q : ℕ × ℕ => (Denumerable.ofNat (List ℕ) q.2.unpair.2) :=
    (Primrec.ofNat (List ℕ)).comp (primrec_unpairSnd.comp Primrec.snd)
  have hm : Primrec fun q : ℕ × ℕ => q.2.unpair.1 / 2 :=
    Primrec.nat_div.comp (primrec_unpairFst.comp Primrec.snd) (Primrec.const 2)
  exact Primrec.ite
    (primrecPred_ratLt
      (primrec₂_addCode.comp (primrec_unpairFst.comp hm)
        (primrec_halfPowCode.comp (primrec_unpairSnd.comp hm)))
      ((Primrec.list_getD 0).comp hL (primrec_unpairSnd.comp hm)))
    (Primrec₂.natPair.comp Primrec.fst (primrec_unpairFst.comp hm))
    (Primrec₂.natPair.comp Primrec.fst (Primrec.const zeroCode))

private theorem primrec_oddBranch {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    Primrec fun q : ℕ × ℕ =>
      if gt (q.1, (q.2.unpair.1 / 2).unpair.1.unpair.1,
          addCode (addCode ((Denumerable.ofNat (List ℕ) q.2.unpair.2).getD
              (q.2.unpair.1 / 2).unpair.2.unpair.1 0)
            (halfPowCode (q.2.unpair.1 / 2).unpair.2.unpair.1))
            (q.2.unpair.1 / 2).unpair.1.unpair.2) (q.2.unpair.1 / 2).unpair.2.unpair.2 = true
        then (q.2.unpair.1 / 2).unpair.1 else Nat.pair 0 zeroCode := by
  have hL : Primrec fun q : ℕ × ℕ => (Denumerable.ofNat (List ℕ) q.2.unpair.2) :=
    (Primrec.ofNat (List ℕ)).comp (primrec_unpairSnd.comp Primrec.snd)
  have hm : Primrec fun q : ℕ × ℕ => q.2.unpair.1 / 2 :=
    Primrec.nat_div.comp (primrec_unpairFst.comp Primrec.snd) (Primrec.const 2)
  have hthr : Primrec fun q : ℕ × ℕ =>
      addCode (addCode ((Denumerable.ofNat (List ℕ) q.2.unpair.2).getD
          (q.2.unpair.1 / 2).unpair.2.unpair.1 0)
        (halfPowCode (q.2.unpair.1 / 2).unpair.2.unpair.1))
        (q.2.unpair.1 / 2).unpair.1.unpair.2 :=
    primrec₂_addCode.comp
      (primrec₂_addCode.comp
        ((Primrec.list_getD 0).comp hL (primrec_unpairFst.comp (primrec_unpairSnd.comp hm)))
        (primrec_halfPowCode.comp (primrec_unpairFst.comp (primrec_unpairSnd.comp hm))))
      (primrec_unpairSnd.comp (primrec_unpairFst.comp hm))
  have hg : Primrec fun q : ℕ × ℕ =>
      gt (q.1, (q.2.unpair.1 / 2).unpair.1.unpair.1, _) (q.2.unpair.1 / 2).unpair.2.unpair.2 :=
    hgt.comp (Primrec.fst.pair
      ((primrec_unpairFst.comp (primrec_unpairFst.comp hm)).pair hthr))
      (primrec_unpairSnd.comp (primrec_unpairSnd.comp hm))
  exact Primrec.ite (PrimrecRel.comp Primrec.eq hg (Primrec.const true))
    (primrec_unpairFst.comp hm) (Primrec.const (Nat.pair 0 zeroCode))

private theorem primrec_afrRealG_uniform {gt : ℕ × ℕ × RatCode → ℕ → Bool}
    (hgt : Primrec₂ gt) : Primrec fun q : ℕ × ℕ => afrRealG gt q.1 q.2 := by
  have hparity : PrimrecPred fun q : ℕ × ℕ => q.2.unpair.1 % 2 = 0 :=
    PrimrecRel.comp Primrec.eq
      (Primrec.nat_mod.comp (primrec_unpairFst.comp Primrec.snd) (Primrec.const 2))
      (Primrec.const 0)
  exact Primrec.ite hparity primrec_evenBranch (primrec_oddBranch hgt)

/-- The uniform postprocessor: the output coordinate now carries the centre, `⟨i, n⟩`. -/
private def afrRealGU (gt : ℕ × ℕ × RatCode → ℕ → Bool) (v : ℕ) : ℕ :=
  afrRealG gt v.unpair.1.unpair.1 (Nat.pair v.unpair.1.unpair.2 v.unpair.2)

private theorem primrec_afrRealGU {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    Primrec (afrRealGU gt) := by
  have h := (primrec_afrRealG_uniform hgt).comp
    ((primrec_unpairFst.comp primrec_unpairFst).pair
      (Primrec₂.natPair.comp (primrec_unpairSnd.comp primrec_unpairFst) primrec_unpairSnd))
  exact h.of_eq fun _ => rfl

/-- **The uniform evaluator.** One code for EVERY centre: the output coordinate carries `⟨i, n⟩`,
so the quantifier order is `∃ e, ∀ i` rather than `∀ i, ∃ e`. That is what a composite serving a
basis needs, since the basis varies its centre at runtime. The semantic `afrReal` definitions are
untouched — only the code layer is generalized. -/
theorem exists_afrRealEvalCode {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    ∃ e : OracleCode, ∀ (r : Baire) (i n : ℕ),
      e.eval r (Nat.pair i n) = Part.some (afrReal gt r i n) := by
  obtain ⟨e, he⟩ := exists_prefixPostCode (b := fun w _ => w.unpair.2 + 1)
    (Primrec.succ.comp (primrec_unpairSnd.comp Primrec.fst)) (primrec_afrRealGU hgt)
  refine ⟨e, fun r i n => ?_⟩
  have hval : afrRealGU gt (Nat.pair (Nat.pair i n)
      (encode (streamTake r ((Nat.pair i n).unpair.2 + 1)))) = afrReal gt r i n := by
    simp only [afrRealGU, Nat.unpair_pair]
    exact afrRealG_pack gt i r n
  rw [he r (Nat.pair i n), hval]

end ContinuityOpenBall

end ComputableAnalysis
