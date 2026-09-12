/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.ContinuityBasis
import ComputableAnalysis.Measure.ContinuityOpenRestriction
import ComputableAnalysis.Measure.Conditioning
import ComputableAnalysis.Measure.Marginals
import ComputableAnalysis.RepresentedSpace.FunctionSpace
import ComputableAnalysis.Weihrauch.Compilers
import ComputableAnalysis.Weihrauch.Principles.Limit

/-!
# Continuous disintegration reduces strongly to `Lim`

The upper bound of Ackerman–Freer–Roy's classification: computing a continuous disintegration
of a joint law is strongly Weihrauch reducible to `Lim`, uniformly over presented metric spaces.

The reduction conditions on the effective `µ`-continuity opens of a computed continuity basis
of the first marginal, so that the single jump `Lim` provides decides an `x`-independent
**stability** predicate: a basis entry is stable at precision `j` when the conditionals on all
its genuine refinements stay within `2⁻⁽ʲ⁺¹⁾` of its own. Local averaging of a continuous
disintegration supplies a stable entry about every point, and stability plus local cofinality
of the refinements pins the entry's conditional within `2⁻⁽ʲ⁺¹⁾` of the true kernel, so
reading one more coordinate of that conditional's weak name yields the required `2⁻ʲ`.

Assumptions: metric, measurable and Borel structure on both factors, and the two computable
presentations. No additional nonemptiness or separability assumptions are made (those already
follow from the supplied presentations), and no completeness or Standard Borel assumption is
added.

## Main definitions and results

* `upperPayload`, `exists_upperPreprocessorCode` — the payload handed to `Lim` (joint name on
  the even track, continuity basis on the odd track) and its preprocessor.
* `exists_conditionalOnContOpenCode`, `exists_trackwiseConditionalCode` — conditioning on a
  continuity open, and the total trackwise conditional over every basis entry with a lazy
  sentinel gate.
* `refinementTail`, `exists_refinementTailCode` — the uniform refinement tail of an entry.
* `RefinementStable`, `exists_refinementStable`, `refinementStable_le` — the stability
  predicate and its two boundary theorems, the only measure theory in the jump.
* `exists_stabilityIndex`, `jumpBit_iff_not_refinementStable` — the diagonally specialized
  oracle index whose jump bit decides stability.
* `exists_disintegrateEvaluator` — one fixed evaluator with advice exactly the accepted `Lim`
  answer.
* `disintegrate_le_lim` — the headline.

## Implementation notes

Three layers of the jump are kept independently auditable: adaptive oracle access (a
three-stage prefix chain over the combined conditional and tail streams), diagonal
specialization by `smn` (the base code discards its self-input), and `Lim` interpretation
(the odd column of the accepted answer). The refinement tail bundles its certificate with the
tail code so that the tail, its asserted semantics and the stability index all refer to one
certificate; the membership search reuses the same certificate for economy, not by necessity.
-/

open MeasureTheory Metric Encodable Denumerable

set_option linter.style.longFile 1700

namespace ComputableAnalysis

open OracleCode

section UpperBound

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y)

/-- **From a joint weak name to a first-marginal weak name**, by one oracle code. -/
theorem exists_fstMarginalCode :
    ∃ c : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure (X × Y)),
      WeakMeasureNames (P.prod Q) p μ →
      ∃ m ∈ c.evalStream p, WeakMeasureNames P m (fstMarginal μ) := by
  have : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨c, hc⟩ := computableMap_fstMarginal P Q
  refine ⟨c, fun p μ hp => ?_⟩
  obtain ⟨m, hm, hmn⟩ := hc p μ ((weakMeasureRep_names_iff (P.prod Q)).mpr hp)
  exact ⟨m, hm, (weakMeasureRep_names_iff P).mp hmn⟩

/-- **From a joint weak name to a continuity basis of the first marginal**, by one oracle code. -/
theorem exists_jointBasisCode :
    ∃ c : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure (X × Y)),
      WeakMeasureNames (P.prod Q) p μ →
      ∃ B ∈ c.evalStream p, ∃ ρ : ℕ → ℕ → ℝ,
        ContinuityBasisNames P (fstMarginal μ) B ρ := by
  obtain ⟨fstCode, hfst⟩ := exists_fstMarginalCode P Q
  obtain ⟨basisCode, hbasis⟩ := exists_continuityBasisCode P
  refine ⟨basisCode.subst fstCode, fun p μ hp => ?_⟩
  obtain ⟨m, hm, hmn⟩ := hfst p μ hp
  obtain ⟨B, hB, ρ, hρ⟩ := hbasis m (fstMarginal μ) hmn
  exact ⟨B, (evalStream_subst hm).symm ▸ hB, ρ, hρ⟩

/-- **The payload handed to `Lim`**: joint weak name on the even track, continuity basis of the
first marginal on the odd track. -/
def upperPayload (p B : Baire) : Baire := Baire.interleave p B

@[simp] theorem upperPayload_evenPart (p B : Baire) :
    Baire.evenPart (upperPayload p B) = p := Baire.evenPart_interleave p B

@[simp] theorem upperPayload_oddPart (p B : Baire) :
    Baire.oddPart (upperPayload p B) = B := Baire.oddPart_interleave p B

/-- **The payload is produced by one oracle code** from the joint name alone. -/
theorem exists_payloadCode :
    ∃ c : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure (X × Y)),
      WeakMeasureNames (P.prod Q) p μ →
      ∃ B : Baire, ∃ ρ : ℕ → ℕ → ℝ,
        ContinuityBasisNames P (fstMarginal μ) B ρ ∧
        upperPayload p B ∈ c.evalStream p := by
  obtain ⟨basisCode, hbasis⟩ := exists_jointBasisCode P Q
  refine ⟨pairCode .query basisCode, fun p μ hp => ?_⟩
  obtain ⟨B, hB, ρ, hρ⟩ := hbasis p μ hp
  have hq : p ∈ (OracleCode.query).evalStream p := by
    rw [evalStream_query]; exact Part.mem_some _
  exact ⟨B, ρ, hρ, pairCode_spec hq hB⟩

/-- **The preprocessor of the reduction**: from a joint weak name it produces the `limTable` of a
payload carrying that same name together with a continuity basis of the first marginal. -/
theorem exists_upperPreprocessorCode :
    ∃ K : OracleCode, ∀ (p : Baire) (μ : ProbabilityMeasure (X × Y)),
      WeakMeasureNames (P.prod Q) p μ →
      ∃ B : Baire, ∃ ρ : ℕ → ℕ → ℝ,
        ContinuityBasisNames P (fstMarginal μ) B ρ ∧
        limTable (upperPayload p B) ∈ K.evalStream p := by
  obtain ⟨payloadCode, hpayload⟩ := exists_payloadCode P Q
  obtain ⟨tableCode, htable⟩ := exists_limTableCode
  refine ⟨tableCode.subst payloadCode, fun p μ hp => ?_⟩
  obtain ⟨B, ρ, hρ, hpay⟩ := hpayload p μ hp
  exact ⟨B, ρ, hρ, (evalStream_subst hpay).symm ▸ htable (upperPayload p B)⟩

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- The dense sequence of a presented product, read at an explicitly paired index. -/
theorem prod_dense_pair (i j : ℕ) :
    (P.prod Q).dense (Nat.pair i j) = (P.dense i, Q.dense j) := by
  change (P.dense (Nat.pair i j).unpair.1, Q.dense (Nat.pair i j).unpair.2) = _
  rw [Nat.unpair_pair]

/-- The cylinder lift of an open name: coordinate `⟨k, j⟩` carries the `k`-th enumerated ball of
`u`, re-centred at the product dense point `⟨centre, j⟩` and keeping its radius code. -/
def cylLift (u : Baire) : Baire := fun n =>
  Nat.pair (Nat.pair (u n.unpair.1).unpair.1 n.unpair.2) (u n.unpair.1).unpair.2

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
/-- **The lift names the cylinder.** -/
theorem openOf_cylLift (u : Baire) :
    openOf (P.prod Q) (cylLift u) = openOf P u ×ˢ (Set.univ : Set Y) := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => ?_) fun z hz => ?_
  · -- the `n`-th product ball sits in the cylinder over its own first-factor ball
    have hball : ball ((P.prod Q).dense (cylLift u n).unpair.1)
          ((ratOfCode (cylLift u n).unpair.2 : ℚ) : ℝ)
        = ball (P.dense (u n.unpair.1).unpair.1) ((ratOfCode (u n.unpair.1).unpair.2 : ℚ) : ℝ)
            ×ˢ ball (Q.dense n.unpair.2) ((ratOfCode (u n.unpair.1).unpair.2 : ℚ) : ℝ) := by
      rw [cylLift]
      simp only [Nat.unpair_pair]
      rw [prod_dense_pair]
      exact (ball_prod_same _ _ _).symm
    rw [hball]
    refine Set.prod_mono ?_ (Set.subset_univ _)
    exact Set.subset_iUnion
      (fun k => ball (P.dense (u k).unpair.1) ((ratOfCode (u k).unpair.2 : ℚ) : ℝ)) n.unpair.1
  · -- conversely, density supplies a second-factor centre once the radius is positive
    obtain ⟨hz1, -⟩ := hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz1
    have hpos : 0 < ((ratOfCode (u k).unpair.2 : ℚ) : ℝ) :=
      lt_of_le_of_lt dist_nonneg (mem_ball.mp hk)
    obtain ⟨j, hj⟩ := Metric.denseRange_iff.mp Q.denseRange z.2 _ hpos
    refine Set.mem_iUnion.mpr ⟨Nat.pair k j, ?_⟩
    have hball : ball ((P.prod Q).dense (cylLift u (Nat.pair k j)).unpair.1)
          ((ratOfCode (cylLift u (Nat.pair k j)).unpair.2 : ℚ) : ℝ)
        = ball (P.dense (u k).unpair.1) ((ratOfCode (u k).unpair.2 : ℚ) : ℝ)
            ×ˢ ball (Q.dense j) ((ratOfCode (u k).unpair.2 : ℚ) : ℝ) := by
      rw [cylLift]
      simp only [Nat.unpair_pair]
      rw [prod_dense_pair]
      exact (ball_prod_same _ _ _).symm
    rw [hball]
    exact ⟨hk, mem_ball.mpr hj⟩

omit [BorelSpace Y] in
/-- **The lift preserves mass**: a cylinder carries exactly its base's first-marginal mass.
Hoisted out of `contOpen_cylLift`, because the postprocessor needs it separately — it is what
transfers the positivity hypothesis of `exists_contSetRestrictionCode` from the first marginal
to the joint law. -/
theorem measure_openOf_cylLift {μ : ProbabilityMeasure (X × Y)} (u : Baire) :
    μ.toMeasure (openOf (P.prod Q) (cylLift u)) = (fstMarginal μ).toMeasure (openOf P u) := by
  rw [openOf_cylLift, fstMarginal_toMeasure, Measure.fst_apply (measurableSet_openOf P u)]
  congr 1
  exact Set.prod_univ

omit [BorelSpace Y] in
/-- Positivity transfers through the lift. -/
theorem measure_openOf_cylLift_ne_zero {μ : ProbabilityMeasure (X × Y)} {u : Baire}
    (h : (fstMarginal μ).toMeasure (openOf P u) ≠ 0) :
    μ.toMeasure (openOf (P.prod Q) (cylLift u)) ≠ 0 := by
  rwa [measure_openOf_cylLift P Q]

omit [BorelSpace Y] in
/-- **The cylinder lift of a continuity open is a continuity open for the joint law.**
Disjointness is inherited coordinatewise, and each cylinder carries exactly the first marginal's
mass of its base, so the two masses still sum to `1`. -/
theorem contOpen_cylLift {μ : ProbabilityMeasure (X × Y)} {uv : Baire}
    (h : ContinuityOpenNames P (fstMarginal μ) uv) :
    ContinuityOpenNames (P.prod Q) μ
      (Baire.interleave (cylLift uv.evenPart) (cylLift uv.oddPart)) := by
  have hmass : ∀ u : Baire, μ.toMeasure (openOf (P.prod Q) (cylLift u))
      = (fstMarginal μ).toMeasure (openOf P u) := measure_openOf_cylLift P Q
  constructor
  · rw [Baire.evenPart_interleave, Baire.oddPart_interleave, openOf_cylLift, openOf_cylLift,
      Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hx, -⟩ ⟨hx', -⟩
    exact Set.disjoint_left.mp h.disjoint hx hx'
  · rw [Baire.evenPart_interleave, Baire.oddPart_interleave, hmass, hmass]
    exact h.full

private theorem computable_cylLiftIdx : Computable fun n : ℕ => n.unpair.1 :=
  (Primrec.fst.comp Primrec.unpair).to_comp

private theorem computable_cylLiftPost :
    Computable fun z : ℕ =>
      Nat.pair (Nat.pair z.unpair.1.unpair.1 z.unpair.2.unpair.2) z.unpair.1.unpair.2 :=
  (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))).to_comp

/-- **The lift code.** One `query` at the computed base index, then a first-order repacking. -/
theorem exists_cylLiftCode :
    ∃ L : OracleCode, (∀ (u : Baire) (n : ℕ), L.eval u n = Part.some (cylLift u n)) ∧
      ∀ u : Baire, cylLift u ∈ L.evalStream u := by
  obtain ⟨eIdx, hIdx⟩ := exists_ofNatFnCode computable_cylLiftIdx
  obtain ⟨ePost, hPost⟩ := exists_ofNatFnCode computable_cylLiftPost
  have hEval : ∀ (u : Baire) (n : ℕ),
      (comp ePost (pair (comp query eIdx) OracleCode.id)).eval u n
        = Part.some (cylLift u n) := by
    intro u n
    have hq : (comp query eIdx).eval u n = Part.some (u n.unpair.1) := by
      rw [eval_comp_some (hIdx u n), eval_query]
    have hpaired : (pair (comp query eIdx) OracleCode.id).eval u n
        = Part.some (Nat.pair (u n.unpair.1) n) := by
      rw [eval_pair, hq, eval_id]
      simp [Seq.seq]
    rw [eval_comp_some hpaired, hPost]
    simp [cylLift, Nat.unpair_pair]
  exact ⟨_, hEval, fun u => mem_evalStream.mpr fun n => by
    rw [hEval u n]; exact Part.mem_some _⟩

theorem exists_conditionalOnContOpenCode :
    ∃ C : OracleCode,
      ∀ (p uv : Baire) (μ : ProbabilityMeasure (X × Y)),
        WeakMeasureNames (P.prod Q) p μ →
        ContinuityOpenNames P (fstMarginal μ) uv →
        (fstMarginal μ).toMeasure (openOf P uv.evenPart) ≠ 0 →
        ∃ q ∈ C.evalStream (Baire.interleave p uv),
          ∃ ν : ProbabilityMeasure (X × Y),
            ν.toMeasure =
              normalizedRestriction μ (openOf P uv.evenPart ×ˢ (Set.univ : Set Y)) ∧
            (weakMeasureRep Q).Names q (sndMarginal ν) := by
  classical
  have : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨L, -, hLmem⟩ := exists_cylLiftCode
  obtain ⟨restrictionCode, hrestriction⟩ := exists_contSetRestrictionCode (P := P.prod Q)
  obtain ⟨sndMarginalCode, hsnd⟩ := computableMap_sndMarginal P Q
  set liftPairCode : OracleCode := pairCode (L.subst evenCode) (L.subst oddCode) with hliftPair
  set restrictionInputCode : OracleCode :=
    pairCode evenCode (liftPairCode.subst oddCode) with hinputCode
  refine ⟨sndMarginalCode.subst (restrictionCode.subst restrictionInputCode), ?_⟩
  intro p uv μ hp hcont hpos
  set F : Baire := Baire.interleave p uv with hF
  set uv' : Baire := Baire.interleave (cylLift uv.evenPart) (cylLift uv.oddPart) with huv'
  -- 1. the lifted pair, produced from the continuity half of the input
  have hlift : uv' ∈ liftPairCode.evalStream uv := by
    rw [hliftPair, huv']
    refine pairCode_spec ?_ ?_
    · rw [evalStream_subst (q := uv.evenPart)
        (by rw [evalStream_evenCode]; exact Part.mem_some _)]
      exact hLmem _
    · rw [evalStream_subst (q := uv.oddPart)
        (by rw [evalStream_oddCode]; exact Part.mem_some _)]
      exact hLmem _
  -- 2. the stream the generic restriction compiler consumes
  have hinput : Baire.interleave p uv' ∈ restrictionInputCode.evalStream F := by
    rw [hinputCode]
    refine pairCode_spec ?_ ?_
    · rw [hF, evalStream_evenCode_interleave]; exact Part.mem_some _
    · rw [evalStream_subst (q := uv)
        (by rw [hF, evalStream_oddCode_interleave]; exact Part.mem_some _)]
      exact hlift
  -- 3. continuity transfers to the joint law
  have hcont' : ContinuityOpenNames (P.prod Q) μ uv' := contOpen_cylLift P Q hcont
  -- 4. so does positive mass
  have hpos' : μ.toMeasure (openOf (P.prod Q) uv'.evenPart) ≠ 0 := by
    rw [huv', Baire.evenPart_interleave]
    exact measure_openOf_cylLift_ne_zero P Q hpos
  -- 5. the generic restriction compiler
  obtain ⟨r, hr, ν, hν, hrν⟩ := hrestriction p uv' μ hp hcont' hpos'
  -- 6. the named target is the cylinder, not its encoding
  have hνeq : ν.toMeasure
      = normalizedRestriction μ (openOf P uv.evenPart ×ˢ (Set.univ : Set Y)) := by
    rw [hν, huv', Baire.evenPart_interleave, openOf_cylLift]
  -- 7. the second marginal
  obtain ⟨q, hq, hqν⟩ := hsnd r ν hrν
  -- 8. transport both memberships back to the original input
  refine ⟨q, ?_, ν, hνeq, hqν⟩
  have hrF : r ∈ (restrictionCode.subst restrictionInputCode).evalStream F := by
    rw [evalStream_subst hinput]; exact hr
  rw [evalStream_subst hrF]
  exact hq

omit [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- **Every nonzero basis entry has positive first-marginal mass.** -/
theorem measure_basisOpen_succ_ne_zero {μ : ProbabilityMeasure (X × Y)} {B : Baire}
    {ρ : ℕ → ℕ → ℝ} (hB : BasisEntrySpec P B ρ) (hfull : FullFirstMarginalSupport μ) (i k : ℕ) :
    (fstMarginal μ).toMeasure (basisOpen P B (Nat.pair i k + 1)) ≠ 0 := by
  have hpos : 0 < ρ i k := lt_trans (by positivity) (hB.lower i k)
  have : μ.toMeasure.fst.IsOpenPosMeasure := hfull.isOpenPosMeasure
  rw [hB.open_eq i k, fstMarginal_toMeasure]
  exact (measure_ball_pos _ _ hpos).ne'

/-- **The conditional at a nonzero basis entry**, by one code uniform in `i` and `k`. -/
theorem exists_conditionalOnBasisEntryCode :
    ∃ C : OracleCode,
      ∀ (p B : Baire) (μ : ProbabilityMeasure (X × Y)) (ρ : ℕ → ℕ → ℝ) (i k : ℕ),
        WeakMeasureNames (P.prod Q) p μ →
        ContinuityBasisNames P (fstMarginal μ) B ρ →
        FullFirstMarginalSupport μ →
        ∃ q ∈ C.evalStream
            (Baire.interleave p (Baire.track (Nat.pair i k + 1) B).oddPart),
          ∃ ν : ProbabilityMeasure (X × Y),
            ν.toMeasure = normalizedRestriction μ
              (basisOpen P B (Nat.pair i k + 1) ×ˢ (Set.univ : Set Y)) ∧
            (weakMeasureRep Q).Names q (sndMarginal ν) := by
  obtain ⟨C, hC⟩ := exists_conditionalOnContOpenCode P Q
  refine ⟨C, fun p B μ ρ i k hp hB hfull => ?_⟩
  have hpos : (fstMarginal μ).toMeasure
      (openOf P (Baire.track (Nat.pair i k + 1) B).oddPart.evenPart) ≠ 0 :=
    measure_basisOpen_succ_ne_zero P hB.toBasisEntrySpec hfull i k
  obtain ⟨q, hq, ν, hν, hqν⟩ := hC p _ μ hp (hB.continuity _) hpos
  exact ⟨q, hq, ν, hν, hqν⟩

/-- **The per-track input builder**: a total rewiring whose track `b` is exactly the stream the
conditional compiler consumes for basis entry `b`. Pure plumbing — no promise is attached, and in
particular track `0` is built like any other. -/
private theorem exists_entryInputCode :
    ∃ c : OracleCode, ∀ p B : Baire,
      ∃ R ∈ c.evalStream (Baire.interleave p B),
        ∀ b : ℕ, Baire.track b R = Baire.interleave p (Baire.track b B).oddPart := by
  refine ⟨zipTracksCode.subst (pairCode (repeatTracksCode.subst evenCode)
    (oddCode.subst (unzipTracksCode.subst oddCode))), fun p B => ?_⟩
  have hpF : p ∈ evenCode.evalStream (Baire.interleave p B) := by
    rw [evalStream_evenCode_interleave]; exact Part.mem_some _
  have hBF : B ∈ oddCode.evalStream (Baire.interleave p B) := by
    rw [evalStream_oddCode_interleave]; exact Part.mem_some _
  have h1 : (fun m => p m.unpair.2)
      ∈ (repeatTracksCode.subst evenCode).evalStream (Baire.interleave p B) := by
    rw [evalStream_subst hpF, evalStream_repeatTracksCode]; exact Part.mem_some _
  have hU : (fun j => B (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)))
      ∈ (unzipTracksCode.subst oddCode).evalStream (Baire.interleave p B) := by
    rw [evalStream_subst hBF, evalStream_unzipTracksCode]; exact Part.mem_some _
  have h2 : Baire.oddPart (fun j => B (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)))
      ∈ (oddCode.subst (unzipTracksCode.subst oddCode)).evalStream (Baire.interleave p B) := by
    rw [evalStream_subst hU, evalStream_oddCode]; exact Part.mem_some _
  refine ⟨fun m => Baire.interleave (fun m => p m.unpair.2)
      (Baire.oddPart fun j => B (Nat.pair (j / 2).unpair.1 (2 * (j / 2).unpair.2 + j % 2)))
      (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2), ?_, fun b => ?_⟩
  · rw [evalStream_subst (pairCode_spec h1 h2), evalStream_zipTracksCode]
    exact Part.mem_some _
  · rw [track_zipTracks, Baire.evenPart_interleave, Baire.oddPart_interleave,
      track_repeatTracks, track_oddPart_unzipTracks]

private theorem computable_gateSelector :
    Computable fun n : ℕ => Nat.pair n (1 - (1 - n.unpair.1)) :=
  (Primrec₂.natPair.comp Primrec.id
    (Primrec.nat_sub.comp (Primrec.const 1)
      (Primrec.nat_sub.comp (Primrec.const 1) (Primrec.fst.comp Primrec.unpair)))).to_comp

/-- **The lazy sentinel gate.** The first clause is the point: on track `0` the emitted value is
`Part.some 0` outright, with `M` absent from the right-hand side rather than merely ignored. -/
private theorem exists_sentinelGateCode (M : OracleCode) :
    ∃ W : OracleCode,
      (∀ (F : Baire) (n : ℕ), n.unpair.1 = 0 → W.eval F n = Part.some 0) ∧
      (∀ (F : Baire) (n : ℕ), n.unpair.1 ≠ 0 → W.eval F n = M.eval F n) := by
  obtain ⟨s, hs⟩ := exists_ofNatFnCode computable_gateSelector
  have hz : ∀ (F : Baire) (m : ℕ), (zero : OracleCode).eval F m = Part.some 0 :=
    fun F m => by rw [eval_zero]; rfl
  refine ⟨comp (prec zero (comp M left)) s, fun F n h => ?_, fun F n h => ?_⟩
  · rw [eval_comp_some (hs F n), show 1 - (1 - n.unpair.1) = 0 by omega, eval_prec_zero, hz]
  · rw [eval_comp_some (hs F n), show 1 - (1 - n.unpair.1) = 0 + 1 by omega, eval_prec_succ,
      eval_prec_zero, hz, some_bind_fun,
      eval_comp_some (eval_left F (Nat.pair n (Nat.pair 0 0)))]
    simp

/-- **The total trackwise conditional.** One code, defined at every numeric basis index: the
sentinel track carries a fixed valid weak name, and every genuine entry carries a weak name of the
second marginal of the normalized joint restriction to that entry's cylinder. -/
theorem exists_trackwiseConditionalCode :
    ∃ W : OracleCode,
      ∀ (p B : Baire) (μ : ProbabilityMeasure (X × Y)) (ρ : ℕ → ℕ → ℝ),
        WeakMeasureNames (P.prod Q) p μ →
        ContinuityBasisNames P (fstMarginal μ) B ρ →
        FullFirstMarginalSupport μ →
        ∃ w ∈ W.evalStream (Baire.interleave p B),
          Baire.track 0 w = (fun _ => 0) ∧
          ∀ i k, ∃ ν : ProbabilityMeasure (X × Y),
            ν.toMeasure = normalizedRestriction μ
              (basisOpen P B (Nat.pair i k + 1) ×ˢ (Set.univ : Set Y)) ∧
            WeakMeasureNames Q (Baire.track (Nat.pair i k + 1) w) (sndMarginal ν) := by
  classical
  obtain ⟨C, hC⟩ := exists_conditionalOnBasisEntryCode P Q
  obtain ⟨inp, hinp⟩ := exists_entryInputCode
  obtain ⟨W, hgate0, hgateS⟩ := exists_sentinelGateCode ((mapTracks C).subst inp)
  refine ⟨W, fun p B μ ρ hp hB hfull => ?_⟩
  obtain ⟨R, hR, hRtrack⟩ := hinp p B
  -- the coordinate equation of the trackwise compiler on this input
  have hRe : inp.eval (Baire.interleave p B) = fun n => Part.some (R n) :=
    funext fun n => Part.eq_some_iff.mpr (mem_evalStream.mp hR n)
  have hMeval : ∀ b k : ℕ, ((mapTracks C).subst inp).eval (Baire.interleave p B) (Nat.pair b k)
      = C.eval (Baire.track b R) k := by
    intro b k
    rw [eval_subst_of_eval hRe (mapTracks C), eval_mapTracks_pair]
  -- one witness per genuine entry, indexed by the predecessor track
  choose qs hqs νs hνs hqνs using fun m : ℕ => hC p B μ ρ m.unpair.1 m.unpair.2 hp hB hfull
  have hqs' : ∀ m : ℕ, qs m ∈ C.evalStream (Baire.track (m + 1) R) := by
    intro m
    rw [hRtrack (m + 1)]
    have h := hqs m
    rwa [Nat.pair_unpair m] at h
  refine ⟨fun n => if n.unpair.1 = 0 then 0 else qs (n.unpair.1 - 1) n.unpair.2, ?_, ?_, ?_⟩
  · refine mem_evalStream.mpr fun n => ?_
    by_cases h : n.unpair.1 = 0
    · rw [hgate0 _ n h]
      rw [show (if n.unpair.1 = 0 then 0 else qs (n.unpair.1 - 1) n.unpair.2) = 0 by simp [h]]
      exact Part.mem_some _
    · rw [hgateS _ n h]
      have hn : ((mapTracks C).subst inp).eval (Baire.interleave p B) n
          = C.eval (Baire.track n.unpair.1 R) n.unpair.2 := by
        conv_lhs => rw [← Nat.pair_unpair n]
        exact hMeval _ _
      have hm : n.unpair.1 = n.unpair.1 - 1 + 1 := by omega
      rw [hn, show (if n.unpair.1 = 0 then 0 else qs (n.unpair.1 - 1) n.unpair.2)
        = qs (n.unpair.1 - 1) n.unpair.2 by simp [h]]
      have hmem := mem_evalStream.mp (hqs' (n.unpair.1 - 1)) n.unpair.2
      rwa [← hm] at hmem
  · funext s; simp
  · intro i k
    refine ⟨νs (Nat.pair i k), ?_, ?_⟩
    · simpa using hνs (Nat.pair i k)
    · have hw : (Baire.track (Nat.pair i k + 1)
          fun n => if n.unpair.1 = 0 then 0 else qs (n.unpair.1 - 1) n.unpair.2)
          = qs (Nat.pair i k) := by funext s; simp
      rw [hw]
      simpa using (weakMeasureRep_names_iff Q).mp (hqνs (Nat.pair i k))

end UpperBound

section RefinementTail

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The open name carried by basis entry `b`. -/
def entryOpenName (B : Baire) (b : ℕ) : Baire := (Baire.track b B).oddPart.evenPart

omit [MeasurableSpace X] [BorelSpace X] in
theorem basisOpen_eq_openOf_entryOpenName (P : ComputableMetricPresentation X) (B : Baire)
    (b : ℕ) : basisOpen P B b = openOf P (entryOpenName B b) := rfl

/-- The packed family of entry open names, as a single query rewiring of `B`. -/
theorem track_entryNames (B : Baire) (b : ℕ) :
    Baire.track b (fun m => B (Nat.pair m.unpair.1 (4 * m.unpair.2 + 1))) = entryOpenName B b := by
  funext k
  simp only [Baire.track_apply, Nat.unpair_pair, entryOpenName, Baire.evenPart_apply,
    Baire.oddPart_apply]
  congr 2
  omega

/-- **The refinement tail of basis entry `b`**: the right inverse's total choice stream, run on
`b`'s own open name. Uniform in `B` and `b`; independent of any point. -/
def refinementTail (fires : ℕ × ℕ × RatCode → ℕ → Bool) (B : Baire) (b w : ℕ) : ℕ :=
  basisChoiceAt fires B (entryOpenName B b) w

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Property 1: every tail entry refines the source entry.** Unconditional — the `0` fillers name
`∅` — so the `≠ 0` guard is needed only where a filler would be compared, never here. -/
theorem refinementTail_subset {P : ComputableMetricPresentation X}
    {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hsound : ∀ (a : ℕ × ℕ × RatCode) (t : ℕ), fires a t = true →
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ))
    {B : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) (b w : ℕ) :
    basisOpen P B (refinementTail fires B b w) ⊆ basisOpen P B b := by
  classical
  by_cases hfire : certFires fires B (entryOpenName B b) w = true
  · rw [refinementTail, basisChoiceAt, ite_eq_left hfire]
    refine subset_trans (certFires_sound hsound hspec w hfire) ?_
    rw [basisOpen_eq_openOf_entryOpenName, openOf]
    exact Set.subset_iUnion
      (fun k => ball (P.dense (entryOpenName B b k).unpair.1)
        (((ratOfCode (entryOpenName B b k).unpair.2 : ℚ) : ℝ))) (certJ w)
  · rw [refinementTail, basisChoiceAt, ite_eq_right hfire, hspec.zero]
    exact Set.empty_subset _

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Property 2: the tail is locally cofinal.** Every point of the source entry lies in a *nonzero*
tail entry contained in any prescribed neighbourhood of that point. -/
theorem exists_refinementTail_subset {P : ComputableMetricPresentation X}
    {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true)
    {B : Baire} {ρ : ℕ → ℕ → ℝ} (hspec : BasisEntrySpec P B ρ) (b : ℕ) {x : X}
    (hx : x ∈ basisOpen P B b) {U : Set X} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ w, refinementTail fires B b w ≠ 0 ∧
      x ∈ basisOpen P B (refinementTail fires B b w) ∧
      basisOpen P B (refinementTail fires B b w) ⊆ U := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hxU
  obtain ⟨w, hmem, hfire, hsmall⟩ :=
    exists_certFires_subset hcomplete hspec (u := entryOpenName B b) hx hε
  refine ⟨w, ?_, ?_, ?_⟩
  · rw [refinementTail, basisChoiceAt, ite_eq_left hfire]
    exact certB_ne_zero_of_certFires hfire
  · rw [refinementTail, basisChoiceAt, ite_eq_left hfire]
    exact hmem
  · rw [refinementTail, basisChoiceAt, ite_eq_left hfire]
    exact subset_trans hsmall hball

private theorem computable_entryNameIdx :
    Computable fun m : ℕ => Nat.pair m.unpair.1 (4 * m.unpair.2 + 1) :=
  (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.succ.comp
      (Primrec.nat_mul.comp (Primrec.const 4) (Primrec.snd.comp Primrec.unpair)))).to_comp

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Property 3: the whole tail family is produced by one code from `B` alone.** Track `b` of the
output is `b`'s refinement tail, and the two semantic properties are bundled at the same `fires` so
that no later consumer can silently pair the code with a different certificate. -/
theorem exists_refinementTailCode (P : ComputableMetricPresentation X) :
    ∃ (fires : ℕ × ℕ × RatCode → ℕ → Bool) (T : OracleCode),
      Primrec₂ fires ∧
      (∀ a : ℕ × ℕ × RatCode,
        dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) ↔ ∃ t, fires a t = true) ∧
      (∀ B : Baire, Baire.packTracks (fun b => refinementTail fires B b) ∈ T.evalStream B) ∧
      (∀ (B : Baire) (ρ : ℕ → ℕ → ℝ), BasisEntrySpec P B ρ → ∀ b w : ℕ,
        basisOpen P B (refinementTail fires B b w) ⊆ basisOpen P B b) ∧
      (∀ (B : Baire) (ρ : ℕ → ℕ → ℝ), BasisEntrySpec P B ρ → ∀ (b : ℕ) (x : X),
        x ∈ basisOpen P B b → ∀ U : Set X, IsOpen U → x ∈ U →
        ∃ w, refinementTail fires B b w ≠ 0 ∧
          x ∈ basisOpen P B (refinementTail fires B b w) ∧
          basisOpen P B (refinementTail fires B b w) ⊆ U) := by
  classical
  obtain ⟨fires, hfiresprim, hfiresiff⟩ := repred_exists_primrec_stages P.ltSemidec
  have hsound : ∀ (a : ℕ × ℕ × RatCode) (t : ℕ), fires a t = true →
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) :=
    fun a t hat => (hfiresiff a).mpr ⟨t, hat⟩
  have hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true :=
    fun a ha => (hfiresiff a).mp ha
  obtain ⟨H, hH⟩ := exists_rightInverseCode hfiresprim
  obtain ⟨eNames, hNames⟩ := exists_ofNatFnCode computable_entryNameIdx
  refine ⟨fires, (mapTracks H).subst (zipTracksCode.subst
    (pairCode repeatTracksCode (comp query eNames))), hfiresprim, hfiresiff, fun B => ?_,
    fun B ρ hspec b w => refinementTail_subset hsound hspec b w,
    fun B ρ hspec b x hx U hU hxU => exists_refinementTail_subset hcomplete hspec b hx hU hxU⟩
  -- the per-track input: track `b` is `interleave B (entryOpenName B b)`
  have h1 : (fun m => B m.unpair.2) ∈ repeatTracksCode.evalStream B := by
    rw [evalStream_repeatTracksCode]; exact Part.mem_some _
  have h2 : (fun m => B (Nat.pair m.unpair.1 (4 * m.unpair.2 + 1)))
      ∈ (comp query eNames).evalStream B := by
    rw [evalStream_query_comp hNames]; exact Part.mem_some _
  have hR : (fun m => Baire.interleave (fun m => B m.unpair.2)
        (fun m => B (Nat.pair m.unpair.1 (4 * m.unpair.2 + 1)))
        (2 * Nat.pair m.unpair.1 (m.unpair.2 / 2) + m.unpair.2 % 2))
      ∈ (zipTracksCode.subst (pairCode repeatTracksCode (comp query eNames))).evalStream B := by
    rw [evalStream_subst (pairCode_spec h1 h2), evalStream_zipTracksCode]
    exact Part.mem_some _
  rw [evalStream_subst hR]
  refine evalStream_mapTracks_iff.mpr fun b => ?_
  rw [track_zipTracks, Baire.evenPart_interleave, Baire.oddPart_interleave, track_repeatTracks,
    track_entryNames, Baire.track_packTracks]
  exact mem_evalStream.mpr fun w => by rw [hH B (entryOpenName B b) w]; exact Part.mem_some _

end RefinementTail

section LocalAveraging

open ProbabilityTheory

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {P : ComputableMetricPresentation X} {Q : ComputableMetricPresentation Y}

omit [BorelSpace X] in
private theorem exists_nhds_conditional_le
    {μ : ProbabilityMeasure (X × Y)} {f : ContinuousKernelPoint P Q}
    (hf : IsCondKernel μ (inducedKernel f)) (x : X) {ε : ℝ} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ U : Set X, MeasurableSet U → U ⊆ V →
        μ.toMeasure (U ×ˢ (Set.univ : Set Y)) ≠ 0 →
        ∀ ν : ProbabilityMeasure (X × Y),
          ν.toMeasure = normalizedRestriction μ (U ×ˢ (Set.univ : Set Y)) →
          levyProkhorovDist (sndMarginal ν).toMeasure (f.val.toFun x).toMeasure ≤ ε := by
  classical
  have : TopologicalSpace.SeparableSpace Y :=
    ⟨⟨Set.range Q.dense, Set.countable_range _, Q.denseRange⟩⟩
  have hmk : IsMarkovKernel (inducedKernel f) := hf.1
  have hck := hf.2
  -- continuity of the disintegration, read in the Lévy–Prokhorov metric
  have hcont : Continuous fun y : X =>
      (LevyProkhorov.ofMeasure (f.val.toFun y) : LevyProkhorov (ProbabilityMeasure Y)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp f.prop.1
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp hcont x ε hε
  refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ,
    fun U hU hUV hpos ν hν => ?_⟩
  have hVdist : ∀ y ∈ U, levyProkhorovDist (f.val.toFun y).toMeasure
      (f.val.toFun x).toMeasure < ε := by
    intro y hy
    have := hball y (Metric.mem_ball.mp (hUV hy))
    rwa [LevyProkhorov.dist_probabilityMeasure_def] at this
  -- the disintegration identity on measurable rectangles over `U`
  have hdis : μ.toMeasure.fst ⊗ₘ inducedKernel f = μ.toMeasure := Measure.disintegrate _ _
  have hprod : ∀ A : Set Y, MeasurableSet A →
      μ.toMeasure (U ×ˢ A) = ∫⁻ y in U, inducedKernel f y A ∂μ.toMeasure.fst := by
    intro A hA
    conv_lhs => rw [← hdis]
    rw [Measure.compProd_apply_prod hU hA]
  -- the base mass, in both presentations
  have hcU : μ.toMeasure (U ×ˢ (Set.univ : Set Y)) = μ.toMeasure.fst U := by
    rw [Measure.fst_apply hU, Set.prod_univ]
  have hcfin : μ.toMeasure (U ×ˢ (Set.univ : Set Y)) ≠ ⊤ := measure_ne_top _ _
  -- the second marginal of the normalized restriction is the normalized cylinder mass
  have hsnd : ∀ A : Set Y, MeasurableSet A →
      (sndMarginal ν).toMeasure A
        = (μ.toMeasure (U ×ˢ (Set.univ : Set Y)))⁻¹ * μ.toMeasure (U ×ˢ A) := by
    intro A hA
    rw [sndMarginal_toMeasure, hν, normalizedRestriction, Measure.snd_apply hA,
      Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurable_snd hA)]
    congr 2
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact and_comm
  refine levyProkhorovDist_le_of_forall_le _ _ hε.le fun r A hr hA => ?_
  -- the uniform pointwise bound on the base
  have hpt : ∀ y ∈ U, inducedKernel f y A
      ≤ (f.val.toFun x).toMeasure (thickening r A) + ENNReal.ofReal r := by
    intro y hy
    have hlt : levyProkhorovEDist (f.val.toFun y).toMeasure (f.val.toFun x).toMeasure
        < ENNReal.ofReal r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr
        (lt_trans (hVdist y hy) hr)
    have hle := left_measure_le_of_levyProkhorovEDist_lt hlt hA
    rwa [ENNReal.toReal_ofReal (by linarith)] at hle
  have hmono : ∫⁻ y in U, inducedKernel f y A ∂μ.toMeasure.fst
      ≤ ∫⁻ _ in U, ((f.val.toFun x).toMeasure (thickening r A) + ENNReal.ofReal r)
          ∂μ.toMeasure.fst :=
    lintegral_mono_ae ((ae_restrict_iff' hU).mpr (Filter.Eventually.of_forall hpt))
  calc (sndMarginal ν).toMeasure A
      = (μ.toMeasure (U ×ˢ (Set.univ : Set Y)))⁻¹ * μ.toMeasure (U ×ˢ A) := hsnd A hA
    _ = (μ.toMeasure (U ×ˢ (Set.univ : Set Y)))⁻¹
          * ∫⁻ y in U, inducedKernel f y A ∂μ.toMeasure.fst := by rw [hprod A hA]
    _ ≤ (μ.toMeasure (U ×ˢ (Set.univ : Set Y)))⁻¹
          * ∫⁻ _ in U, ((f.val.toFun x).toMeasure (thickening r A) + ENNReal.ofReal r)
              ∂μ.toMeasure.fst := by gcongr
    _ = (μ.toMeasure (U ×ˢ (Set.univ : Set Y)))⁻¹
          * (((f.val.toFun x).toMeasure (thickening r A) + ENNReal.ofReal r)
              * μ.toMeasure (U ×ˢ (Set.univ : Set Y))) := by
        rw [setLIntegral_const, hcU]
    _ = (f.val.toFun x).toMeasure (thickening r A) + ENNReal.ofReal r := by
        rw [mul_comm ((f.val.toFun x).toMeasure (thickening r A) + ENNReal.ofReal r),
          ← mul_assoc, ENNReal.inv_mul_cancel hpos hcfin, one_mul]

/-- Every nonzero index's measure is the conditional its basis entry names. -/
def TrackDenotes (μ : ProbabilityMeasure (X × Y)) (P : ComputableMetricPresentation X) (B : Baire)
    (ν : ℕ → ProbabilityMeasure Y) : Prop :=
  ∀ c : ℕ, c ≠ 0 → ∃ σ : ProbabilityMeasure (X × Y),
    σ.toMeasure = normalizedRestriction μ (basisOpen P B c ×ˢ (Set.univ : Set Y)) ∧
    ν c = sndMarginal σ

/-- **The stability predicate**, over the selected track denotations. -/
def RefinementStable (ν : ℕ → ProbabilityMeasure Y) (tail : ℕ → ℕ → ℕ) (j b : ℕ) : Prop :=
  b ≠ 0 ∧
    ∀ n, tail b n ≠ 0 →
      levyProkhorovDist (ν b).toMeasure (ν (tail b n)).toMeasure ≤ (2 : ℝ)⁻¹ ^ (j + 1)

private theorem lp_triangle (a b c : ProbabilityMeasure Y) :
    levyProkhorovDist a.toMeasure c.toMeasure
      ≤ levyProkhorovDist a.toMeasure b.toMeasure
        + levyProkhorovDist b.toMeasure c.toMeasure := by
  simpa [LevyProkhorov.dist_probabilityMeasure_def] using
    dist_triangle (LevyProkhorov.ofMeasure a) (LevyProkhorov.ofMeasure b)
      (LevyProkhorov.ofMeasure c)

/-- The averaging bound, transported to a nonzero basis entry: measurability, positive mass and the
denotation contract are all discharged here so neither boundary theorem repeats them. -/
private theorem lp_entry_le_of_subset
    {μ : ProbabilityMeasure (X × Y)} {f : ContinuousKernelPoint P Q} {B : Baire}
    {ρ : ℕ → ℕ → ℝ} (hB : ContinuityBasisNames P (fstMarginal μ) B ρ)
    (hfull : FullFirstMarginalSupport μ) {ν : ℕ → ProbabilityMeasure Y}
    (hden : TrackDenotes μ P B ν) {x : X} {ε : ℝ} {V : Set X}
    (hV : ∀ U : Set X, MeasurableSet U → U ⊆ V →
      μ.toMeasure (U ×ˢ (Set.univ : Set Y)) ≠ 0 →
      ∀ σ : ProbabilityMeasure (X × Y),
        σ.toMeasure = normalizedRestriction μ (U ×ˢ (Set.univ : Set Y)) →
        levyProkhorovDist (sndMarginal σ).toMeasure (f.val.toFun x).toMeasure ≤ ε)
    {c : ℕ} (hc : c ≠ 0) (hsub : basisOpen P B c ⊆ V) :
    levyProkhorovDist (ν c).toMeasure (f.val.toFun x).toMeasure ≤ ε := by
  obtain ⟨σ, hσ, hνσ⟩ := hden c hc
  have hUmeas : MeasurableSet (basisOpen P B c) := measurableSet_openOf P (entryOpenName B c)
  have hmass : μ.toMeasure (basisOpen P B c ×ˢ (Set.univ : Set Y))
      = (fstMarginal μ).toMeasure (basisOpen P B c) := by
    rw [fstMarginal_toMeasure, Measure.fst_apply hUmeas, Set.prod_univ]
  have hpos : μ.toMeasure (basisOpen P B c ×ˢ (Set.univ : Set Y)) ≠ 0 := by
    rw [hmass]
    have hcc := pair_decode_succ hc
    rw [← hcc]
    exact measure_basisOpen_succ_ne_zero P hB.toBasisEntrySpec hfull _ _
  rw [hνσ]
  exact hV _ hUmeas hsub hpos σ hσ

/-- **Existence.** Some nonzero basis entry containing `x` is stable at precision `j`: choose it
inside the neighbourhood obtained at error `2⁻⁽ʲ⁺²⁾`; refinements stay inside that neighbourhood, so
both sides are within `2⁻⁽ʲ⁺²⁾` of `f x` and the triangle inequality closes at `2⁻⁽ʲ⁺¹⁾`. -/
theorem exists_refinementStable
    {μ : ProbabilityMeasure (X × Y)} {f : ContinuousKernelPoint P Q}
    (hf : IsCondKernel μ (inducedKernel f)) {B : Baire} {ρ : ℕ → ℕ → ℝ}
    (hB : ContinuityBasisNames P (fstMarginal μ) B ρ) (hfull : FullFirstMarginalSupport μ)
    {ν : ℕ → ProbabilityMeasure Y} (hden : TrackDenotes μ P B ν)
    {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hsound : ∀ (a : ℕ × ℕ × RatCode) (t : ℕ), fires a t = true →
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ))
    (x : X) (j : ℕ) :
    ∃ b, b ≠ 0 ∧ x ∈ basisOpen P B b ∧
      RefinementStable ν (refinementTail fires B) j b := by
  obtain ⟨V, hVopen, hxV, hV⟩ :=
    exists_nhds_conditional_le hf x (by positivity : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (j + 2))
  obtain ⟨b, hxb, hbV⟩ :=
    exists_basisSet_subset (P := P) hB.lower hB.upper hVopen hxV
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [basisSet_zero] at hxb
    exact hxb.elim
  have hbasis : ∀ n : ℕ, n ≠ 0 → basisOpen P B n = basisSet P ρ n := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hm : Nat.pair m.unpair.1 m.unpair.2 = m := Nat.pair_unpair m
    rw [basisSet_succ, ← hm, hB.open_eq m.unpair.1 m.unpair.2, hm]
  have hxb' : x ∈ basisOpen P B b := by rw [hbasis b hb0]; exact hxb
  have hbV' : basisOpen P B b ⊆ V := by rw [hbasis b hb0]; exact hbV
  refine ⟨b, hb0, hxb', hb0, fun n hn => ?_⟩
  have hcV : basisOpen P B (refinementTail fires B b n) ⊆ V :=
    subset_trans (refinementTail_subset hsound hB.toBasisEntrySpec b n) hbV'
  have h1 := lp_entry_le_of_subset hB hfull hden hV hb0 hbV'
  have h2 := lp_entry_le_of_subset hB hfull hden hV hn hcV
  have htri := lp_triangle (ν b) (f.val.toFun x) (ν (refinementTail fires B b n))
  rw [levyProkhorovDist_comm (ν (refinementTail fires B b n)).toMeasure] at h2
  have hpow : (2 : ℝ)⁻¹ ^ (j + 2) + (2 : ℝ)⁻¹ ^ (j + 2) = (2 : ℝ)⁻¹ ^ (j + 1) := by
    rw [pow_succ]; ring
  linarith

/-- **Soundness.** A stable entry's conditional is within `2⁻⁽ʲ⁺¹⁾` of `f x`. No sequence and no
limit object: for arbitrary `δ > 0`, local cofinality supplies a genuine refinement inside the
`δ`-neighbourhood, stability bounds it against `ν b`, and `le_of_forall_pos_le_add` removes `δ`. -/
theorem refinementStable_le
    {μ : ProbabilityMeasure (X × Y)} {f : ContinuousKernelPoint P Q}
    (hf : IsCondKernel μ (inducedKernel f)) {B : Baire} {ρ : ℕ → ℕ → ℝ}
    (hB : ContinuityBasisNames P (fstMarginal μ) B ρ) (hfull : FullFirstMarginalSupport μ)
    {ν : ℕ → ProbabilityMeasure Y} (hden : TrackDenotes μ P B ν)
    {fires : ℕ × ℕ × RatCode → ℕ → Bool}
    (hcomplete : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) → ∃ t, fires a t = true)
    {x : X} {j b : ℕ} (hx : x ∈ basisOpen P B b)
    (hstable : RefinementStable ν (refinementTail fires B) j b) :
    levyProkhorovDist (ν b).toMeasure (f.val.toFun x).toMeasure ≤ (2 : ℝ)⁻¹ ^ (j + 1) := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨V, hVopen, hxV, hV⟩ := exists_nhds_conditional_le hf x hδ
  obtain ⟨n, hn, -, hcV⟩ :=
    exists_refinementTail_subset hcomplete hB.toBasisEntrySpec b hx hVopen hxV
  have h1 := hstable.2 n hn
  have h2 := lp_entry_le_of_subset hB hfull hden hV hn hcV
  have htri := lp_triangle (ν b) (ν (refinementTail fires B b n)) (f.val.toFun x)
  linarith

private theorem lt_levyProkhorovDist_iff_exists_stage
    {ν₁ ν₂ : ProbabilityMeasure Y} {r₁ r₂ : Baire}
    (h₁ : WeakMeasureNames Q r₁ ν₁) (h₂ : WeakMeasureNames Q r₂ ν₂) (q : ℝ) :
    q < levyProkhorovDist ν₁.toMeasure ν₂.toMeasure ↔
      ∃ m : ℕ, q + 2 * (2 : ℝ)⁻¹ ^ m <
        levyProkhorovDist (atomic Q (r₁ m)).toMeasure (atomic Q (r₂ m)).toMeasure := by
  constructor
  · intro hq
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (by linarith : (0 : ℝ) < (levyProkhorovDist ν₁.toMeasure ν₂.toMeasure - q) / 4)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    refine ⟨m, ?_⟩
    have t1 := lp_triangle ν₁ (atomic Q (r₁ m)) ν₂
    have t2 := lp_triangle (atomic Q (r₁ m)) (atomic Q (r₂ m)) ν₂
    have e1 := h₁ m
    have e2 := h₂ m
    rw [levyProkhorovDist_comm ν₂.toMeasure] at e2
    linarith
  · rintro ⟨m, hm⟩
    have t1 := lp_triangle (atomic Q (r₁ m)) ν₁ (atomic Q (r₂ m))
    have t2 := lp_triangle ν₁ ν₂ (atomic Q (r₂ m))
    have e1 := h₁ m
    have e2 := h₂ m
    rw [levyProkhorovDist_comm ν₁.toMeasure] at e1
    linarith

/-- The coded stability threshold `2⁻⁽ʲ⁺¹⁾ + 2⁻ᵐ + 2⁻ᵐ`. -/
def stabilityThresholdCode (j m : ℕ) : RatCode :=
  addCode (halfPowCode (j + 1)) (addCode (halfPowCode m) (halfPowCode m))

theorem ratOfCode_stabilityThresholdCode (j m : ℕ) :
    ratOfCode (stabilityThresholdCode j m)
      = (2 : ℚ)⁻¹ ^ (j + 1) + ((2 : ℚ)⁻¹ ^ m + (2 : ℚ)⁻¹ ^ m) := by
  simp [stabilityThresholdCode, ratOfCode_addCode, ratOfCode_halfPowCode]

/-- The staged violation leaf at witness `z = ⟨n, ⟨m, t⟩⟩`: read the tail entry, reject the
sentinel, then test the staged strict-distance certificate between the two tracks' stage-`m`
atomic indices at the coded threshold. -/
def violationB (gt : ℕ × ℕ × RatCode → ℕ → Bool) (w : Baire) (tail : ℕ → ℕ → ℕ)
    (j b z : ℕ) : Bool :=
  if tail b z.unpair.1 = 0 then false
  else
    gt (Baire.track b w z.unpair.2.unpair.1,
        Baire.track (tail b z.unpair.1) w z.unpair.2.unpair.1,
        stabilityThresholdCode j z.unpair.2.unpair.1) z.unpair.2.unpair.2

/-- **The semantic boundary of the certificate**, proved before any halting code exists: the leaf
fires somewhere exactly when a genuine refinement actually violates the stability bound. -/
theorem exists_violationB_iff {gt : ℕ × ℕ × RatCode → ℕ → Bool}
    (hgt : ∀ a : ℕ × ℕ × RatCode,
      ((ratOfCode a.2.2 : ℚ) : ℝ)
          < levyProkhorovDist (atomic Q a.1).toMeasure (atomic Q a.2.1).toMeasure
        ↔ ∃ t, gt a t = true)
    {ν : ℕ → ProbabilityMeasure Y} {w : Baire} {tail : ℕ → ℕ → ℕ} {j b : ℕ}
    (hname : ∀ c, c ≠ 0 → WeakMeasureNames Q (Baire.track c w) (ν c)) (hb : b ≠ 0) :
    (∃ z, violationB gt w tail j b z = true) ↔
      ∃ n, tail b n ≠ 0 ∧
        (2 : ℝ)⁻¹ ^ (j + 1)
          < levyProkhorovDist (ν b).toMeasure (ν (tail b n)).toMeasure := by
  classical
  have hthr : ∀ m : ℕ, ((ratOfCode (stabilityThresholdCode j m) : ℚ) : ℝ)
      = (2 : ℝ)⁻¹ ^ (j + 1) + 2 * (2 : ℝ)⁻¹ ^ m := by
    intro m
    rw [ratOfCode_stabilityThresholdCode]
    push_cast
    ring
  constructor
  · rintro ⟨z, hz⟩
    by_cases hc : tail b z.unpair.1 = 0
    · rw [violationB, ite_eq_left hc] at hz; exact absurd hz (by simp)
    rw [violationB, ite_eq_right hc] at hz
    refine ⟨z.unpair.1, hc, ?_⟩
    have hstage := (hgt _).mpr ⟨_, hz⟩
    rw [hthr] at hstage
    exact (lt_levyProkhorovDist_iff_exists_stage (hname b hb) (hname _ hc) _).mpr
      ⟨z.unpair.2.unpair.1, hstage⟩
  · rintro ⟨n, hc, hviol⟩
    obtain ⟨m, hm⟩ :=
      (lt_levyProkhorovDist_iff_exists_stage (hname b hb) (hname _ hc) _).mp hviol
    obtain ⟨t, ht⟩ := (hgt (Baire.track b w m, Baire.track (tail b n) w m,
      stabilityThresholdCode j m)).mp (by rw [hthr]; exact hm)
    refine ⟨Nat.pair n (Nat.pair m t), ?_⟩
    simp only [violationB, Nat.unpair_pair]
    rw [ite_eq_right hc]
    exact ht

end LocalAveraging

/-- **The echo columns return the payload.** Even column `2 * i` of `limTable w` is constantly
`w i`, so any accepted limit stream reproduces `w` on its even coordinates. -/
theorem evenPart_of_lim_accepts {w a : Baire} (h : Lim.accepts (limTable w) a) :
    Baire.evenPart a = w := by
  funext i
  obtain ⟨s, hs⟩ := Lim.accepts_iff.mp h (2 * i)
  have hcol := hs s le_rfl
  rw [limTable, Nat.unpair_pair, ite_eq_left (by omega)] at hcol
  rw [Baire.evenPart_apply, ← hcol]
  congr 1
  omega

/-- **The halting columns return the payload's jump.** Odd column `2 * e + 1` carries the
monotone bounded-simulation bit, so its limit is `1` exactly when the `e`-th oracle code halts on
input `e` against the payload. -/
theorem odd_of_lim_accepts {w a : Baire} (h : Lim.accepts (limTable w) a) (e : ℕ) :
    a (2 * e + 1) = 1 ↔ ∃ t, jumpBit w e t = 1 := by
  obtain ⟨s, hs⟩ := Lim.accepts_iff.mp h (2 * e + 1)
  have hcol : ∀ t, s ≤ t → jumpBit w e t = a (2 * e + 1) := by
    intro t ht
    have := hs t ht
    rw [limTable, Nat.unpair_pair, ite_eq_right (by omega)] at this
    rw [← this]
    congr 1
    omega
  constructor
  · intro ha
    exact ⟨s, (hcol s le_rfl).trans ha⟩
  · rintro ⟨t₀, ht₀⟩
    have hmax : jumpBit w e (max s t₀) = 1 :=
      jumpBit_mono w e (le_max_right s t₀) ht₀
    exact (hcol (max s t₀) (le_max_left s t₀)).symm.trans hmax

/-- **The halting columns, negative form.** The companion of `odd_of_lim_accepts`: an odd column
limits to `0` exactly when the simulation never halts. Both directions are needed downstream, and
neither follows from the other without knowing the limit is a bit, so they are stated separately. -/
theorem odd_of_lim_accepts_eq_zero {w a : Baire} (h : Lim.accepts (limTable w) a) (e : ℕ) :
    a (2 * e + 1) = 0 ↔ ¬ ∃ t, jumpBit w e t = 1 := by
  constructor
  · intro ha hex
    rw [(odd_of_lim_accepts h e).mpr hex] at ha
    exact absurd ha one_ne_zero
  · intro hne
    obtain ⟨s, hs⟩ := Lim.accepts_iff.mp h (2 * e + 1)
    have hcol : jumpBit w e s = a (2 * e + 1) := by
      have := hs s le_rfl
      rw [limTable, Nat.unpair_pair, ite_eq_right (by omega)] at this
      rw [← this]
      congr 1
      omega
    rcases jumpBit_cases w e s with h0 | h1
    · exact hcol.symm.trans h0
    · exact absurd ⟨s, h1⟩ hne

section StabilityJump
/-- Field accessors of the search input `Nat.pair (Nat.pair j b) z`, `z = ⟨n, ⟨m, t⟩⟩`. -/
private def sjJ (u : ℕ) : ℕ := u.unpair.1.unpair.1
private def sjB (u : ℕ) : ℕ := u.unpair.1.unpair.2
private def sjN (u : ℕ) : ℕ := u.unpair.2.unpair.1
private def sjM (u : ℕ) : ℕ := u.unpair.2.unpair.2.unpair.1
private def sjT (u : ℕ) : ℕ := u.unpair.2.unpair.2.unpair.2

/-- Position of `tail b n` in the combined stream. -/
private def sjTailPos (u : ℕ) : ℕ := 2 * Nat.pair (sjB u) (sjN u) + 1
/-- Position of `track b w m` in the combined stream. -/
private def sjSrcPos (u : ℕ) : ℕ := 2 * Nat.pair (sjB u) (sjM u)
/-- Stage-1 bound: covers the tail read and the source-track read. -/
private def sjB₀ (u : ℕ) : ℕ := sjTailPos u + sjSrcPos u + 1
/-- Decode a prefix. -/
private def sjPref (h : ℕ) : List ℕ := ofNat (List ℕ) h
/-- The refinement entry `c`, read from a prefix. -/
private def sjC (u h : ℕ) : ℕ := (sjPref h).getD (sjTailPos u) 0
/-- Stage-2 bound: extends stage 1 through `track c w m`. -/
private def sjB₁ (u h : ℕ) : ℕ := sjB₀ u + 2 * Nat.pair (sjC u h) (sjM u) + 1
/-- The postprocessor: `0` on a violation, `1` otherwise (the polarity `rfind` searches for). -/
private def sjPost (gt : ℕ × ℕ × RatCode → ℕ → Bool) (v : ℕ) : ℕ :=
  if sjC v.unpair.1 v.unpair.2 = 0 then 1
  else if gt ((sjPref v.unpair.2).getD (sjSrcPos v.unpair.1) 0,
      (sjPref v.unpair.2).getD (2 * Nat.pair (sjC v.unpair.1 v.unpair.2) (sjM v.unpair.1)) 0,
      stabilityThresholdCode (sjJ v.unpair.1) (sjM v.unpair.1)) (sjT v.unpair.1) = true
    then 0 else 1

private theorem primrec_sjJ : Primrec sjJ := primrec_unpairFst.comp primrec_unpairFst
private theorem primrec_sjB : Primrec sjB := primrec_unpairSnd.comp primrec_unpairFst
private theorem primrec_sjN : Primrec sjN := primrec_unpairFst.comp primrec_unpairSnd
private theorem primrec_sjM : Primrec sjM :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp primrec_unpairSnd)
private theorem primrec_sjT : Primrec sjT :=
  primrec_unpairSnd.comp (primrec_unpairSnd.comp primrec_unpairSnd)

private theorem primrec_sjTailPos : Primrec sjTailPos :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec₂.natPair.comp primrec_sjB primrec_sjN))

private theorem primrec_sjSrcPos : Primrec sjSrcPos :=
  Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp primrec_sjB primrec_sjM)

private theorem primrec_sjB₀ : Primrec sjB₀ :=
  Primrec.succ.comp (Primrec.nat_add.comp primrec_sjTailPos primrec_sjSrcPos)

private theorem primrec_sjPref : Primrec sjPref := Primrec.ofNat (List ℕ)

private theorem primrec₂_sjC : Primrec₂ sjC :=
  ((Primrec.list_getD 0).comp (primrec_sjPref.comp Primrec.snd)
    (primrec_sjTailPos.comp Primrec.fst)).to₂

private theorem primrec₂_sjB₁ : Primrec₂ sjB₁ :=
  (Primrec.succ.comp (Primrec.nat_add.comp (primrec_sjB₀.comp Primrec.fst)
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (primrec₂_sjC.comp Primrec.fst Primrec.snd)
        (primrec_sjM.comp Primrec.fst))))).to₂

private theorem primrec_sjPost {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    Primrec (sjPost gt) := by
  have hu : Primrec fun v : ℕ => v.unpair.1 := primrec_unpairFst
  have hh : Primrec fun v : ℕ => v.unpair.2 := primrec_unpairSnd
  have hc : Primrec fun v : ℕ => sjC v.unpair.1 v.unpair.2 := primrec₂_sjC.comp hu hh
  have hm : Primrec fun v : ℕ => sjM v.unpair.1 := primrec_sjM.comp hu
  have hsrc : Primrec fun v : ℕ => (sjPref v.unpair.2).getD (sjSrcPos v.unpair.1) 0 :=
    (Primrec.list_getD 0).comp (primrec_sjPref.comp hh) (primrec_sjSrcPos.comp hu)
  have href : Primrec fun v : ℕ =>
      (sjPref v.unpair.2).getD (2 * Nat.pair (sjC v.unpair.1 v.unpair.2) (sjM v.unpair.1)) 0 :=
    (Primrec.list_getD 0).comp (primrec_sjPref.comp hh)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp hc hm))
  have hthr : Primrec fun v : ℕ => stabilityThresholdCode (sjJ v.unpair.1) (sjM v.unpair.1) :=
    primrec₂_addCode.comp (primrec_halfPowCode.comp (Primrec.succ.comp (primrec_sjJ.comp hu)))
      (primrec₂_addCode.comp (primrec_halfPowCode.comp hm) (primrec_halfPowCode.comp hm))
  have hfire : Primrec fun v : ℕ =>
      gt ((sjPref v.unpair.2).getD (sjSrcPos v.unpair.1) 0,
        (sjPref v.unpair.2).getD (2 * Nat.pair (sjC v.unpair.1 v.unpair.2) (sjM v.unpair.1)) 0,
        stabilityThresholdCode (sjJ v.unpair.1) (sjM v.unpair.1)) (sjT v.unpair.1) :=
    hgt.comp (hsrc.pair (href.pair hthr)) (primrec_sjT.comp hu)
  exact Primrec.ite (PrimrecRel.comp Primrec.eq hc (Primrec.const 0)) (Primrec.const 1)
    (Primrec.ite (PrimrecRel.comp Primrec.eq hfire (Primrec.const true)) (Primrec.const 0)
      (Primrec.const 1))

/-- Reading the combined stream through a taken prefix, below the prefix length. -/
private theorem sjPref_getD (F : Baire) {k i : ℕ} (h : i < k) :
    (sjPref (encode (streamTake F k))).getD i 0 = F i := by
  rw [sjPref, ofNat_encode, streamTake_getD F h]

/-- **The chain's value is the violation leaf**, with the fixed-point equation for the third
stage established inside: the longer prefix decodes the same refinement entry. -/
private theorem sjPost_value (gt : ℕ × ℕ × RatCode → ℕ → Bool) (w : Baire)
    (tail : ℕ → ℕ → ℕ) (j b z : ℕ) :
    sjPost gt (Nat.pair (Nat.pair (Nat.pair j b) z)
      (encode (streamTake (Baire.interleave w (Baire.packTracks tail))
        (sjB₁ (Nat.pair (Nat.pair j b) z)
          (encode (streamTake (Baire.interleave w (Baire.packTracks tail))
            (sjB₁ (Nat.pair (Nat.pair j b) z)
              (encode (streamTake (Baire.interleave w (Baire.packTracks tail))
                (sjB₀ (Nat.pair (Nat.pair j b) z)))))))))))
      = if violationB gt w tail j b z = true then 0 else 1 := by
  set F : Baire := Baire.interleave w (Baire.packTracks tail) with hF
  set u : ℕ := Nat.pair (Nat.pair j b) z with hu
  have hJ : sjJ u = j := by simp [sjJ, hu, Nat.unpair_pair]
  have hB : sjB u = b := by simp [sjB, hu, Nat.unpair_pair]
  have hN : sjN u = z.unpair.1 := by simp [sjN, hu, Nat.unpair_pair]
  have hM : sjM u = z.unpair.2.unpair.1 := by simp [sjM, hu, Nat.unpair_pair]
  have hT : sjT u = z.unpair.2.unpair.2 := by simp [sjT, hu, Nat.unpair_pair]
  -- the three oracle reads, as coordinates of `F`
  have hFtail : F (2 * Nat.pair b z.unpair.1 + 1) = tail b z.unpair.1 := by
    rw [hF, Baire.interleave_odd]; simp [Baire.packTracks, Nat.unpair_pair]
  have hFsrc : ∀ c, F (2 * Nat.pair c z.unpair.2.unpair.1)
      = Baire.track c w z.unpair.2.unpair.1 := by
    intro c; rw [hF, Baire.interleave_even, Baire.track_apply]
  -- stage 1 decodes the refinement entry
  have hTailPos : sjTailPos u = 2 * Nat.pair b z.unpair.1 + 1 := by rw [sjTailPos, hB, hN]
  have hSrcPos : sjSrcPos u = 2 * Nat.pair b z.unpair.2.unpair.1 := by rw [sjSrcPos, hB, hM]
  have hlt0 : sjTailPos u < sjB₀ u := by rw [sjB₀]; omega
  have hlt0' : sjSrcPos u < sjB₀ u := by rw [sjB₀]; omega
  set k₀ : ℕ := sjB₀ u with hk₀
  have hc0 : sjC u (encode (streamTake F k₀)) = tail b z.unpair.1 := by
    rw [sjC, sjPref_getD F hlt0, hTailPos, hFtail]
  set k₁ : ℕ := sjB₁ u (encode (streamTake F k₀)) with hk₁
  have hk₁val : k₁ = k₀ + 2 * Nat.pair (tail b z.unpair.1) z.unpair.2.unpair.1 + 1 := by
    rw [hk₁, sjB₁, hc0, hM]
  have hle : k₀ ≤ k₁ := by omega
  -- stage 2 decodes the same entry: the fixed-point equation
  have hc1 : sjC u (encode (streamTake F k₁)) = tail b z.unpair.1 := by
    rw [sjC, sjPref_getD F (lt_of_lt_of_le hlt0 hle), hTailPos, hFtail]
  have hfix : sjB₁ u (encode (streamTake F k₁)) = k₁ := by
    rw [sjB₁, hc1, hM, hk₁val]
  have hs1 : 2 * Nat.pair b z.unpair.2.unpair.1 < k₁ := by rw [← hSrcPos]; omega
  have hs2 : 2 * Nat.pair (tail b z.unpair.1) z.unpair.2.unpair.1 < k₁ := by omega
  rw [hfix]
  simp only [sjPost, Nat.unpair_pair, hc1, hJ, hM, hT, hSrcPos]
  rw [violationB]
  by_cases hcz : tail b z.unpair.1 = 0
  · rw [ite_eq_left hcz, ite_eq_left hcz]
    rfl
  · rw [ite_eq_right hcz, ite_eq_right hcz, sjPref_getD F hs1, sjPref_getD F hs2, hFsrc, hFsrc]

/-- **The total violation test body.** One code, total on every combined stream, returning `0`
exactly at the violating witnesses. -/
theorem exists_violationChainCode {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    ∃ V : OracleCode, ∀ (w : Baire) (tail : ℕ → ℕ → ℕ) (j b z : ℕ),
      V.eval (Baire.interleave w (Baire.packTracks tail)) (Nat.pair (Nat.pair j b) z)
        = Part.some (if violationB gt w tail j b z = true then 0 else 1) := by
  obtain ⟨V, hV⟩ := exists_prefixChainCode (b₀ := sjB₀) (b₁ := sjB₁) (b₂ := sjB₁)
    (g := sjPost gt) primrec_sjB₀ primrec₂_sjB₁ primrec₂_sjB₁ (primrec_sjPost hgt)
  exact ⟨V, fun w tail j b z => by rw [hV, sjPost_value]⟩

/-- **Minimization over a total `{0,1}`-valued body halts exactly on a witness.** -/
theorem eval_rfind_of_total {V : OracleCode} {F : Baire} {a : ℕ} {viol : ℕ → Bool}
    (hV : ∀ z, V.eval F (Nat.pair a z) = Part.some (if viol z = true then 0 else 1)) :
    (rfind V).eval F a = Nat.rfind (fun n => Part.some (viol n) : ℕ →. Bool) := by
  rw [eval_rfind, show (fun n => (fun x : ℕ => decide (x = 0)) <$> V.eval F (Nat.pair a n)
      : ℕ →. Bool) = fun n => Part.some (viol n) from
    funext fun n => by
      rw [hV, Part.map_eq_map, Part.map_some]
      cases viol n <;> simp]

/-- The value returned by minimization over a total `{0,1}`-valued body is a witness. -/
theorem viol_of_mem_eval_rfind {V : OracleCode} {F : Baire} {a : ℕ} {viol : ℕ → Bool}
    (hV : ∀ z, V.eval F (Nat.pair a z) = Part.some (if viol z = true then 0 else 1)) {v : ℕ}
    (hv : v ∈ (rfind V).eval F a) : viol v = true := by
  rw [eval_rfind_of_total hV] at hv
  exact (Part.mem_some_iff.mp (Nat.rfind_spec hv)).symm

theorem rfind_dom_iff_exists {V : OracleCode} {F : Baire} {a : ℕ} {viol : ℕ → Bool}
    (hV : ∀ z, V.eval F (Nat.pair a z) = Part.some (if viol z = true then 0 else 1)) :
    ((rfind V).eval F a).Dom ↔ ∃ z, viol z = true := by
  rw [eval_rfind_of_total hV]
  refine Nat.rfind_dom.trans ⟨fun ⟨n, hn, _⟩ => ⟨n, (Part.mem_some_iff.mp hn).symm⟩,
    fun ⟨z, hz⟩ => ⟨z, Part.mem_some_iff.mpr hz.symm, fun _ => Part.some_dom _⟩⟩

/-- **The jump bit witnesses halting.** Some stage of the jump column is `1` exactly when the
`e`-th code halts on input `e` against the stream. -/
theorem exists_jumpBit_eq_one_iff (p : Baire) (e : ℕ) :
    (∃ t, jumpBit p e t = 1) ↔ ((ofNat OracleCode e).eval p e).Dom := by
  simp only [jumpBit, Bool.toNat_eq_one, Option.isSome_iff_exists]
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨t, x, hx⟩
    exact ⟨x, evalnPrefix_complete.mpr ⟨t, hx⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨t, ht⟩ := evalnPrefix_complete.mp hx
    exact ⟨t, x, ht⟩

/-- **The payload composition.** The combined stream is produced from the payload by pairing the
trackwise conditional (run on the whole payload) with the refinement tail run on the odd half. -/
theorem interleave_mem_stabilityInput {W T : OracleCode} {p B w : Baire} {tail : ℕ → ℕ → ℕ}
    (hw : w ∈ W.evalStream (upperPayload p B)) (hT : Baire.packTracks tail ∈ T.evalStream B) :
    Baire.interleave w (Baire.packTracks tail)
      ∈ (pairCode W (T.subst oddCode)).evalStream (upperPayload p B) := by
  refine pairCode_spec hw ?_
  rw [evalStream_subst (cg := oddCode) (q := B)
    (by rw [upperPayload, evalStream_oddCode_interleave]; exact Part.mem_some _)]
  exact hT

/-- **The stability index.** Given any compiler `inp` from a payload to the combined stream,
one computable index function `idx j b` whose diagonal jump bit fires exactly on a violation.
The base code `comp (badSearch.subst inp) left` discards the diagonal self-input. -/
theorem exists_stabilityIndex {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt)
    (inp : OracleCode) :
    ∃ idx : ℕ → ℕ → ℕ, Computable₂ idx ∧
      ∀ (payload w : Baire) (tail : ℕ → ℕ → ℕ),
        Baire.interleave w (Baire.packTracks tail) ∈ inp.evalStream payload →
        ∀ j b, ((∃ t, jumpBit payload (idx j b) t = 1) ↔
          ∃ z, violationB gt w tail j b z = true) := by
  obtain ⟨V, hV⟩ := exists_violationChainCode hgt
  obtain ⟨s, hs, hsmn⟩ := smn
  set base : OracleCode := comp ((rfind V).subst inp) left with hbase
  refine ⟨fun j b => s (encode base) (Nat.pair j b),
    (hs.comp (Computable.const _)
      (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)).to₂,
    fun payload w tail hF j b => ?_⟩
  have hFe : inp.eval payload = fun n => Part.some (Baire.interleave w (Baire.packTracks tail) n) :=
    funext fun n => Part.eq_some_iff.mpr (mem_evalStream.mp hF n)
  rw [exists_jumpBit_eq_one_iff, hsmn, hbase, eval_comp_some (eval_left _ _), Nat.unpair_pair,
    eval_subst_of_eval hFe]
  exact rfind_dom_iff_exists (hV w tail j b)

end StabilityJump

section StabilityJumpSemantics

variable {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {Q : ComputableMetricPresentation Y}

/-- **The concrete staged certificate**, extracted from the Prokhorov presentation: one
primitive recursive stage function witnessing strict atomic Lévy–Prokhorov comparisons. This is
the only place the `LevyProkhorov` synonym is touched. -/
theorem exists_stagedGtCert (Q : ComputableMetricPresentation Y) :
    ∃ gt : ℕ × ℕ × RatCode → ℕ → Bool, Primrec₂ gt ∧
      ∀ a : ℕ × ℕ × RatCode,
        ((ratOfCode a.2.2 : ℚ) : ℝ)
            < levyProkhorovDist (atomic Q a.1).toMeasure (atomic Q a.2.1).toMeasure
          ↔ ∃ t, gt a t = true := by
  obtain ⟨gt, hprim, hiff⟩ := repred_exists_primrec_stages (prokhorovPresentation Q).gtSemidec
  exact ⟨gt, hprim, fun a => (hiff a).symm.symm⟩

/-- **The jump bit decides stability**, given the index's halting equivalence and the name
contracts. `b ≠ 0` is where the sentinel is rejected. -/
theorem jumpBit_iff_not_refinementStable {gt : ℕ × ℕ × RatCode → ℕ → Bool}
    (hgtspec : ∀ a : ℕ × ℕ × RatCode,
      ((ratOfCode a.2.2 : ℚ) : ℝ)
          < levyProkhorovDist (atomic Q a.1).toMeasure (atomic Q a.2.1).toMeasure
        ↔ ∃ t, gt a t = true)
    {ν : ℕ → ProbabilityMeasure Y} {w : Baire} {tail : ℕ → ℕ → ℕ} {j b : ℕ}
    (hname : ∀ c, c ≠ 0 → WeakMeasureNames Q (Baire.track c w) (ν c)) (hb : b ≠ 0)
    {payload : Baire} {e : ℕ}
    (hjump : (∃ t, jumpBit payload e t = 1) ↔ ∃ z, violationB gt w tail j b z = true) :
    (∃ t, jumpBit payload e t = 1) ↔ ¬ RefinementStable ν tail j b := by
  classical
  rw [hjump, exists_violationB_iff hgtspec hname hb, RefinementStable]
  constructor
  · rintro ⟨n, hc, hlt⟩ ⟨-, hall⟩
    exact absurd (hall n hc) (not_le.mpr hlt)
  · intro hns
    obtain ⟨n, hn⟩ := not_forall.mp (not_and.mp hns hb)
    obtain ⟨hc, hnle⟩ := Classical.not_imp.mp hn
    exact ⟨n, hc, not_le.mp hnle⟩

omit [BorelSpace Y] in
/-- **The odd column at the stability index reads stability.** -/
theorem odd_of_lim_accepts_iff_refinementStable {payload a : Baire}
    (h : Lim.accepts (limTable payload) a) {e : ℕ}
    {ν : ℕ → ProbabilityMeasure Y} {tail : ℕ → ℕ → ℕ} {j b : ℕ}
    (hjump : (∃ t, jumpBit payload e t = 1) ↔ ¬ RefinementStable ν tail j b) :
    a (2 * e + 1) = 0 ↔ RefinementStable ν tail j b := by
  rw [odd_of_lim_accepts_eq_zero h, hjump, not_not]

end StabilityJumpSemantics

section MembershipCertificate

variable {X : Type} [MetricSpace X] {P : ComputableMetricPresentation X}

theorem mem_openOf_iff_exists_ltCert {ltCert : ℕ × ℕ × RatCode → ℕ → Bool}
    (hlt : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) ↔ ∃ t, ltCert a t = true)
    {r : Baire} {x : X} (hr : P.NamesPoint r x) (u : Baire) :
    x ∈ openOf P u ↔
      ∃ k m t, ltCert (r m, (u k).unpair.1, subCode (u k).unpair.2 (halfPowCode m)) t = true := by
  have hthr : ∀ k m : ℕ, ((ratOfCode (subCode (u k).unpair.2 (halfPowCode m)) : ℚ) : ℝ)
      = ((ratOfCode (u k).unpair.2 : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ m := by
    intro k m
    rw [ratOfCode_subCode, ratOfCode_halfPowCode]
    push_cast
    ring
  simp only [openOf, Set.mem_iUnion, Metric.mem_ball]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
      (half_pos (sub_pos.mpr hk) :
        0 < (((ratOfCode (u k).unpair.2 : ℚ) : ℝ) - dist x (P.dense (u k).unpair.1)) / 2)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have h1 := hr m
    have h2 := dist_triangle (P.dense (r m)) x (P.dense (u k).unpair.1)
    obtain ⟨t, ht⟩ := (hlt (r m, (u k).unpair.1, subCode (u k).unpair.2 (halfPowCode m))).mp
      (by change dist (P.dense (r m)) (P.dense (u k).unpair.1) < _; rw [hthr]; linarith)
    exact ⟨k, m, t, ht⟩
  · rintro ⟨k, m, t, ht⟩
    have hd : dist (P.dense (r m)) (P.dense (u k).unpair.1)
        < ((ratOfCode (subCode (u k).unpair.2 (halfPowCode m)) : ℚ) : ℝ) :=
      (hlt (r m, (u k).unpair.1, subCode (u k).unpair.2 (halfPowCode m))).mpr ⟨t, ht⟩
    rw [hthr] at hd
    have h1 := hr m
    have h2 := dist_triangle x (P.dense (r m)) (P.dense (u k).unpair.1)
    rw [dist_comm] at h1
    exact ⟨k, by linarith⟩

end MembershipCertificate

section SearchLayer

/-- The search leaf. -/
def searchLeaf (ltCert : ℕ × ℕ × RatCode → ℕ → Bool) (idx : ℕ → ℕ → ℕ) (a r : Baire)
    (j v : ℕ) : Bool :=
  if v.unpair.1 = 0 then false
  else if a (2 * idx j v.unpair.1 + 1) = 0 then
    ltCert (r v.unpair.2.unpair.2.unpair.1,
      (entryOpenName a.evenPart.oddPart v.unpair.1 v.unpair.2.unpair.1).unpair.1,
      subCode (entryOpenName a.evenPart.oddPart v.unpair.1 v.unpair.2.unpair.1).unpair.2
        (halfPowCode v.unpair.2.unpair.2.unpair.1)) v.unpair.2.unpair.2.unpair.2
  else false

/-- Positions of the three oracle reads in `interleave a r`, at input `u = Nat.pair j v`:
the jump column, the constituent of the basis entry, the argument name's approximant. -/
private def slJumpPos (idx : ℕ → ℕ → ℕ) (u : ℕ) : ℕ :=
  2 * (2 * idx u.unpair.1 u.unpair.2.unpair.1 + 1)
private def slEntryPos (u : ℕ) : ℕ :=
  2 * (2 * (2 * Nat.pair u.unpair.2.unpair.1 (2 * (2 * u.unpair.2.unpair.2.unpair.1) + 1) + 1))
private def slNamePos (u : ℕ) : ℕ := 2 * u.unpair.2.unpair.2.unpair.2.unpair.1 + 1

/-- The leaf postprocessor on `Nat.pair u (Nat.pair R₁ (Nat.pair R₂ R₃))`: `0` on success. -/
private def slPost (ltCert : ℕ × ℕ × RatCode → ℕ → Bool) (y : ℕ) : ℕ :=
  if y.unpair.1.unpair.2.unpair.1 = 0 then 1
  else if y.unpair.2.unpair.1 = 0 then
    if ltCert (y.unpair.2.unpair.2.unpair.2, y.unpair.2.unpair.2.unpair.1.unpair.1,
        subCode y.unpair.2.unpair.2.unpair.1.unpair.2
          (halfPowCode y.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1))
        y.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2 = true then 0 else 1
  else 1

private theorem computable_slJumpPos {idx : ℕ → ℕ → ℕ} (hidx : Computable₂ idx) :
    Computable (slJumpPos idx) :=
  Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.succ.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2)
      (hidx.comp primrec_unpairFst.to_comp
        (primrec_unpairFst.to_comp.comp primrec_unpairSnd.to_comp))))

private theorem primrec_slEntryPos : Primrec slEntryPos :=
  Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (primrec_unpairFst.comp primrec_unpairSnd)
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_mul.comp (Primrec.const 2)
            (primrec_unpairFst.comp (primrec_unpairSnd.comp primrec_unpairSnd))))
          (Primrec.const 1))))
      (Primrec.const 1)))

private theorem primrec_slNamePos : Primrec slNamePos :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (primrec_unpairFst.comp (primrec_unpairSnd.comp
      (primrec_unpairSnd.comp primrec_unpairSnd))))

private theorem primrec_slPost {ltCert : ℕ × ℕ × RatCode → ℕ → Bool} (hlt : Primrec₂ ltCert) :
    Primrec (slPost ltCert) := by
  have hu : Primrec fun y : ℕ => y.unpair.1 := primrec_unpairFst
  have hR : Primrec fun y : ℕ => y.unpair.2 := primrec_unpairSnd
  have hb : Primrec fun y : ℕ => y.unpair.1.unpair.2.unpair.1 :=
    primrec_unpairFst.comp (primrec_unpairSnd.comp hu)
  have hm : Primrec fun y : ℕ => y.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1 :=
    primrec_unpairFst.comp (primrec_unpairSnd.comp (primrec_unpairSnd.comp
      (primrec_unpairSnd.comp hu)))
  have ht : Primrec fun y : ℕ => y.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2 :=
    primrec_unpairSnd.comp (primrec_unpairSnd.comp (primrec_unpairSnd.comp
      (primrec_unpairSnd.comp hu)))
  have hR1 : Primrec fun y : ℕ => y.unpair.2.unpair.1 := primrec_unpairFst.comp hR
  have hR2 : Primrec fun y : ℕ => y.unpair.2.unpair.2.unpair.1 :=
    primrec_unpairFst.comp (primrec_unpairSnd.comp hR)
  have hR3 : Primrec fun y : ℕ => y.unpair.2.unpair.2.unpair.2 :=
    primrec_unpairSnd.comp (primrec_unpairSnd.comp hR)
  have hfire : Primrec fun y : ℕ =>
      ltCert (y.unpair.2.unpair.2.unpair.2, y.unpair.2.unpair.2.unpair.1.unpair.1,
        subCode y.unpair.2.unpair.2.unpair.1.unpair.2
          (halfPowCode y.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1))
        y.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2 :=
    hlt.comp (hR3.pair ((primrec_unpairFst.comp hR2).pair
      (primrec₂_subCode.comp (primrec_unpairSnd.comp hR2) (primrec_halfPowCode.comp hm)))) ht
  exact Primrec.ite (PrimrecRel.comp Primrec.eq hb (Primrec.const 0)) (Primrec.const 1)
    (Primrec.ite (PrimrecRel.comp Primrec.eq hR1 (Primrec.const 0))
      (Primrec.ite (PrimrecRel.comp Primrec.eq hfire (Primrec.const true)) (Primrec.const 0)
        (Primrec.const 1))
      (Primrec.const 1))

private theorem slPost_value (ltCert : ℕ × ℕ × RatCode → ℕ → Bool) (idx : ℕ → ℕ → ℕ)
    (a r : Baire) (j v : ℕ) :
    slPost ltCert (Nat.pair (Nat.pair j v)
      (Nat.pair (Baire.interleave a r (slJumpPos idx (Nat.pair j v)))
        (Nat.pair (Baire.interleave a r (slEntryPos (Nat.pair j v)))
          (Baire.interleave a r (slNamePos (Nat.pair j v))))))
      = if searchLeaf ltCert idx a r j v = true then 0 else 1 := by
  have hE : entryOpenName a.evenPart.oddPart v.unpair.1 v.unpair.2.unpair.1
      = a (2 * (2 * Nat.pair v.unpair.1 (2 * (2 * v.unpair.2.unpair.1) + 1) + 1)) := rfl
  simp only [slPost, slJumpPos, slEntryPos, slNamePos, Nat.unpair_pair, Baire.interleave_even,
    Baire.interleave_odd]
  rw [searchLeaf, hE]
  by_cases hb : v.unpair.1 = 0
  · rw [ite_eq_left hb, ite_eq_left hb]
    rfl
  · rw [ite_eq_right hb, ite_eq_right hb]
    by_cases ha : a (2 * idx j v.unpair.1 + 1) = 0
    · rw [ite_eq_left ha, ite_eq_left ha]
    · rw [ite_eq_right ha, ite_eq_right ha]
      rfl

/-- **The total search leaf code**: three `query` reads at computed positions, then the
postprocessor. `idx` enters only through `exists_ofNatFnCode`, so `Computable₂` suffices. -/
theorem exists_searchLeafCode {ltCert : ℕ × ℕ × RatCode → ℕ → Bool} (hlt : Primrec₂ ltCert)
    {idx : ℕ → ℕ → ℕ} (hidx : Computable₂ idx) :
    ∃ L : OracleCode, ∀ (a r : Baire) (j v : ℕ),
      L.eval (Baire.interleave a r) (Nat.pair j v)
        = Part.some (if searchLeaf ltCert idx a r j v = true then 0 else 1) := by
  obtain ⟨G, hG⟩ := exists_ofNatFnCode (primrec_slPost hlt).to_comp
  obtain ⟨C₁, hC₁⟩ := exists_ofNatFnCode (computable_slJumpPos hidx)
  obtain ⟨C₂, hC₂⟩ := exists_ofNatFnCode primrec_slEntryPos.to_comp
  obtain ⟨C₃, hC₃⟩ := exists_ofNatFnCode primrec_slNamePos.to_comp
  refine ⟨comp G (pair OracleCode.id (pair (comp query C₁)
    (pair (comp query C₂) (comp query C₃)))), fun a r j v => ?_⟩
  rw [eval_comp_some (eval_pair_some (eval_id _ _) (eval_pair_some
    ((eval_comp_some (hC₁ _ _)).trans (eval_query _ _))
    (eval_pair_some ((eval_comp_some (hC₂ _ _)).trans (eval_query _ _))
      ((eval_comp_some (hC₃ _ _)).trans (eval_query _ _))))), hG, slPost_value]

variable {X : Type} [MetricSpace X] {P : ComputableMetricPresentation X}

/-- **Search soundness**: every accepted witness names a nonzero entry containing the argument
whose jump column reads `0`. -/
theorem searchLeaf_sound {ltCert : ℕ × ℕ × RatCode → ℕ → Bool}
    (hlt : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) ↔ ∃ t, ltCert a t = true)
    {r : Baire} {x : X} (hr : P.NamesPoint r x) {idx : ℕ → ℕ → ℕ} {a : Baire} {j v : ℕ}
    (hv : searchLeaf ltCert idx a r j v = true) :
    v.unpair.1 ≠ 0 ∧ x ∈ basisOpen P a.evenPart.oddPart v.unpair.1 ∧
      a (2 * idx j v.unpair.1 + 1) = 0 := by
  by_cases hb : v.unpair.1 = 0
  · rw [searchLeaf, ite_eq_left hb] at hv
    exact absurd hv Bool.false_ne_true
  by_cases ha : a (2 * idx j v.unpair.1 + 1) = 0
  · rw [searchLeaf, ite_eq_right hb, ite_eq_left ha] at hv
    exact ⟨hb, (mem_openOf_iff_exists_ltCert hlt hr _).mpr ⟨_, _, _, hv⟩, ha⟩
  · rw [searchLeaf, ite_eq_right hb, ite_eq_right ha] at hv
    exact absurd hv Bool.false_ne_true

/-- **Search completeness**: a good entry yields an accepted witness naming it. -/
theorem searchLeaf_complete {ltCert : ℕ × ℕ × RatCode → ℕ → Bool}
    (hlt : ∀ a : ℕ × ℕ × RatCode,
      dist (P.dense a.1) (P.dense a.2.1) < ((ratOfCode a.2.2 : ℚ) : ℝ) ↔ ∃ t, ltCert a t = true)
    {r : Baire} {x : X} (hr : P.NamesPoint r x) {idx : ℕ → ℕ → ℕ} {a : Baire} {j b : ℕ}
    (hb : b ≠ 0) (hx : x ∈ basisOpen P a.evenPart.oddPart b) (ha : a (2 * idx j b + 1) = 0) :
    ∃ v, searchLeaf ltCert idx a r j v = true := by
  obtain ⟨k, m, t, hkmt⟩ := (mem_openOf_iff_exists_ltCert hlt hr _).mp hx
  refine ⟨Nat.pair b (Nat.pair k (Nat.pair m t)), ?_⟩
  simp only [searchLeaf, Nat.unpair_pair]
  rw [ite_eq_right hb, ite_eq_left ha]
  exact hkmt

end SearchLayer

section Evaluator

open ProbabilityTheory

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {P : ComputableMetricPresentation X} {Q : ComputableMetricPresentation Y}

omit [BorelSpace X] [BorelSpace Y] in
/-- **The track family** of the trackwise conditional's output: one probability measure per
index, satisfying the denotation contract and the name contract at every nonzero index. -/
theorem exists_trackFamily {μ : ProbabilityMeasure (X × Y)} {B w : Baire}
    (hw : ∀ i k, ∃ ν : ProbabilityMeasure (X × Y),
      ν.toMeasure = normalizedRestriction μ
        (basisOpen P B (Nat.pair i k + 1) ×ˢ (Set.univ : Set Y)) ∧
      WeakMeasureNames Q (Baire.track (Nat.pair i k + 1) w) (sndMarginal ν)) :
    ∃ ν : ℕ → ProbabilityMeasure Y, TrackDenotes μ P B ν ∧
      ∀ c, c ≠ 0 → WeakMeasureNames Q (Baire.track c w) (ν c) := by
  choose νs hνs hnames using hw
  refine ⟨fun c => sndMarginal (νs (c - 1).unpair.1 (c - 1).unpair.2), fun c hc => ?_,
    fun c hc => ?_⟩
  · have h := hνs (c - 1).unpair.1 (c - 1).unpair.2
    rw [pair_decode_succ hc] at h
    exact ⟨_, h, rfl⟩
  · have h := hnames (c - 1).unpair.1 (c - 1).unpair.2
    rwa [pair_decode_succ hc] at h

/-- **The evaluator.** One fixed code `E`, with advice exactly the accepted `Lim` answer `a`,
advice-realizes the disintegration on every argument name: search for a nonzero basis entry
containing the argument whose stability bit reads `0`, then emit coordinate `j + 1` of that
entry's conditional track. -/
theorem exists_disintegrateEvaluator (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    ∃ E : OracleCode,
      ∀ (p B a : Baire) (μ : ProbabilityMeasure (X × Y)) (ρ : ℕ → ℕ → ℝ)
        (f : ContinuousKernelPoint P Q),
        WeakMeasureNames (P.prod Q) p μ →
        ContinuityBasisNames P (fstMarginal μ) B ρ →
        FullFirstMarginalSupport μ →
        IsCondKernel μ (inducedKernel f) →
        Lim.accepts (limTable (upperPayload p B)) a →
        AdvisedRealizes P.cauchyRep (weakMeasureRep Q) E a f.val.toFun := by
  classical
  obtain ⟨W, hW⟩ := exists_trackwiseConditionalCode P Q
  obtain ⟨fires, T, hfiresprim, hfires, hT, -, -⟩ := exists_refinementTailCode P
  obtain ⟨gt, hgtprim, hgtspec⟩ := exists_stagedGtCert Q
  obtain ⟨idx, hidx, hidxspec⟩ := exists_stabilityIndex hgtprim (pairCode W (T.subst oddCode))
  obtain ⟨L, hL⟩ := exists_searchLeafCode hfiresprim hidx
  obtain ⟨K, hK⟩ := exists_ofNatFnCode
    (g := fun u => Nat.pair u.unpair.2.unpair.1 (u.unpair.1 + 1))
    (Primrec₂.natPair.to_comp.comp (primrec_unpairFst.comp primrec_unpairSnd).to_comp
      (Computable.succ.comp primrec_unpairFst.to_comp))
  refine ⟨comp (W.subst (evenCode.subst evenCode)) (comp K (pair OracleCode.id (rfind L))),
    fun p B a μ ρ f hp hB hfull hf hacc r x hr => ?_⟩
  have hr' : P.NamesPoint r x := P.cauchyRep_names_iff.mp hr
  have hae : a.evenPart = upperPayload p B := evenPart_of_lim_accepts hacc
  have hBa : a.evenPart.oddPart = B := by rw [hae, upperPayload_oddPart]
  -- the fixed data: conditional tracks, their denotations, the stability bits
  obtain ⟨w, hw, -, hwtr⟩ := hW p B μ ρ hp hB hfull
  obtain ⟨ν, hden, hname⟩ := exists_trackFamily hwtr
  have hF := interleave_mem_stabilityInput hw (hT B)
  have hjump : ∀ j b, b ≠ 0 →
      (a (2 * idx j b + 1) = 0 ↔ RefinementStable ν (refinementTail fires B) j b) :=
    fun j b hb => odd_of_lim_accepts_iff_refinementStable hacc
      (jumpBit_iff_not_refinementStable hgtspec hname hb (hidxspec _ _ _ hF j b))
  have hsound : ∀ (c : ℕ × ℕ × RatCode) (t : ℕ), fires c t = true →
      dist (P.dense c.1) (P.dense c.2.1) < ((ratOfCode c.2.2 : ℚ) : ℝ) :=
    fun c t h => (hfires c).mpr ⟨t, h⟩
  have hcomplete : ∀ c : ℕ × ℕ × RatCode,
      dist (P.dense c.1) (P.dense c.2.1) < ((ratOfCode c.2.2 : ℚ) : ℝ) → ∃ t, fires c t = true :=
    fun c h => (hfires c).mp h
  -- the search converges at every coordinate
  have hdom : ∀ j, ((rfind L).eval (Baire.interleave a r) j).Dom := by
    intro j
    obtain ⟨b, hb, hxb, hstable⟩ := exists_refinementStable hf hB hfull hden hsound x j
    exact (rfind_dom_iff_exists (hL a r j)).mpr
      (searchLeaf_complete hfires hr' hb (by rw [hBa]; exact hxb) ((hjump j b hb).mpr hstable))
  choose vsel hvsel using fun j => Part.dom_iff_mem.mp (hdom j)
  -- every selected witness is good
  have hgood : ∀ j, (vsel j).unpair.1 ≠ 0 ∧ x ∈ basisOpen P B (vsel j).unpair.1 ∧
      RefinementStable ν (refinementTail fires B) j (vsel j).unpair.1 := by
    intro j
    obtain ⟨hb, hxb, ha⟩ :=
      searchLeaf_sound hfires hr' (viol_of_mem_eval_rfind (hL a r j) (hvsel j))
    rw [hBa] at hxb
    exact ⟨hb, hxb, (hjump j _ hb).mp ha⟩
  -- the conditional compiler runs on the advice's even half
  have hev : (evenCode.subst evenCode).eval (Baire.interleave a r)
      = fun n => Part.some (a.evenPart n) := by
    have hmem : a.evenPart ∈ (evenCode.subst evenCode).evalStream (Baire.interleave a r) := by
      rw [evalStream_subst (cg := evenCode) (q := a)
        (by rw [evalStream_evenCode_interleave]; exact Part.mem_some _), evalStream_evenCode]
      exact Part.mem_some _
    exact funext fun n => Part.eq_some_iff.mpr (mem_evalStream.mp hmem n)
  refine ⟨fun j => Baire.track (vsel j).unpair.1 w (j + 1), mem_evalStream.mpr fun j => ?_,
    (weakMeasureRep_names_iff Q).mpr fun j => ?_⟩
  · rw [eval_comp_some ((eval_comp_some (eval_pair_some (eval_id _ _)
      (Part.eq_some_iff.mpr (hvsel j)))).trans (hK _ _)), Nat.unpair_pair,
      eval_subst_of_eval hev, hae]
    exact mem_evalStream.mp hw _
  · obtain ⟨hb, hxb, hstable⟩ := hgood j
    have h1 := hname _ hb (j + 1)
    have h2 := refinementStable_le hf hB hfull hden hcomplete hxb hstable
    have htri := lp_triangle (atomic Q (Baire.track (vsel j).unpair.1 w (j + 1)))
      (ν (vsel j).unpair.1) (f.val.toFun x)
    rw [levyProkhorovDist_comm] at h1
    rw [levyProkhorovDist_comm]
    have hpow : (2 : ℝ)⁻¹ ^ (j + 1) + (2 : ℝ)⁻¹ ^ (j + 1) = (2 : ℝ)⁻¹ ^ j := by
      rw [pow_succ]; ring
    linarith

end Evaluator

section Headline

open ProbabilityTheory

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- **The general upper bound**: continuous disintegration reduces strongly to `Lim`. -/
theorem disintegrate_le_lim (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) : Disintegrate P Q ≤sW Lim := by
  classical
  have : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨K, hK⟩ := exists_upperPreprocessorCode P Q
  obtain ⟨E, hE⟩ := exists_disintegrateEvaluator P Q
  obtain ⟨H, hH⟩ := exists_funPackCode E
  refine stabilizationTable_le_lim (K := K) (H := H) fun p μ hpμ hdom => ?_
  obtain ⟨hfull, f, hf⟩ := disintegrate_dom_iff.mp hdom
  have hp : WeakMeasureNames (P.prod Q) p μ := (weakMeasureRep_names_iff (P.prod Q)).mp hpμ
  obtain ⟨B, ρ, hB, hKmem⟩ := hK p μ hp
  refine ⟨limTable (upperPayload p B), hKmem, limTable_dom _, fun a hacc => ?_⟩
  exact ⟨funPack E a, hH a, f,
    Representation.subtype_names_iff.mpr (names_funPack (hE p B a μ ρ f hp hB hfull hf hacc)),
    hfull, hf⟩

end Headline

end ComputableAnalysis
