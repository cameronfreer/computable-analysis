/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecArith
import ComputableAnalysis.Metric.CauchyRepresentation
import ComputableAnalysis.RepresentedSpace.Equivalence
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.MetricSpace.PiNat

/-!
# The Cantor computable metric presentation

Unit 24: the Cantor slice of the metric layer. Convention 11's scoped instances live in
`ComputableAnalysis.PiNatInstances`: the `PiNat` metric `dist x y = (1/2) ^ firstDiff x y`
(definitionally compatible with the product uniformity, via
`PiNat.metricSpaceOfDiscreteUniformity`) and the matching Borel structure.

Under those instances, `cantorPresentation` presents Cantor space with dense sequence the
`false`-extended decoded binary words. The distance between two dense points is an
*exactly coded* dyadic rational — `0` for equal extended words, else `(1/2) ^ d` at the
first padded-word mismatch `d` — so both convention 7 threshold comparisons are decidable,
hence r.e. through `repred_of_ratLt`.

`cantorPresentation_cauchyRep_equiv` identifies the induced fast Cauchy representation
with the strict Cantor representation `cantorRep` (unit 7). Both directions are explicit
realizers from `OracleCode.exists_prefixPostCode`: a length-`(n + 1)` prefix of a strict
name decodes to the index of a `(1/2)^n`-close dense point, and coordinate `i` of the
point is read off any indexed dense point within `(1/2)^(i+1)`.
-/

namespace ComputableAnalysis

/-! ### Convention 11: scoped `PiNat` instances -/

namespace PiNatInstances

/-- Scoped Cantor metric: `dist x y = (1/2) ^ (firstDiff x y)`, via mathlib's
`PiNat.metricSpaceOfDiscreteUniformity` (the `Bool` factors carry the discrete `⊥`
uniformity, whose uniformity filter is definitionally principal on the identity relation,
exactly as for `PiNat.metricSpaceNatNat`); the induced uniformity and topology are
definitionally the product ones. -/
noncomputable scoped instance cantorMetricSpace : MetricSpace Cantor :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl

/-- Scoped Borel structure for the scoped Cantor metric: stated explicitly because
instance search will not cross the definitional equality between the metric topology and
the product topology on its own. -/
scoped instance : BorelSpace Cantor := Pi.borelSpace

end PiNatInstances

open scoped PiNatInstances
open OracleCode Encodable Denumerable

/-! ### Basic distance facts for the scoped Cantor metric -/

private theorem cantor_dist_eq_of_ne {x y : Cantor} (h : x ≠ y) :
    dist x y = (1 / 2 : ℝ) ^ PiNat.firstDiff x y :=
  PiNat.dist_eq_of_ne h

/-- Two Cantor points closer than `(1/2)^n` agree at all coordinates `≤ n`. -/
private theorem cantor_apply_eq_of_dist_lt {x y : Cantor} {n : ℕ}
    (h : dist x y < (1 / 2 : ℝ) ^ n) {i : ℕ} (hi : i ≤ n) : x i = y i :=
  PiNat.apply_eq_of_dist_lt h hi

private theorem cantor_mem_cylinder_iff_dist_le {x y : Cantor} {n : ℕ} :
    y ∈ PiNat.cylinder x n ↔ dist y x ≤ (1 / 2 : ℝ) ^ n :=
  PiNat.mem_cylinder_iff_dist_le

/-! ### Small arithmetic helpers -/

private theorem half_pow_succ_le (n : ℕ) : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

private theorem half_pow_succ_lt (n : ℕ) : (1 / 2 : ℝ) ^ (n + 1) < (1 / 2 : ℝ) ^ n := by
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n]

private theorem inv_two_eq_half : ((2 : ℝ)⁻¹) = 1 / 2 := by norm_num

/-! ### The dense sequence: words extended by `false`s -/

/-- Decode an index to a binary word (`Primcodable (List Bool)` numbering; garbage ↦ `[]`). -/
def denseWord (m : ℕ) : List Bool := (Encodable.decode (α := List Bool) m).getD []

/-- The Cantor point of a word: extend by `false`s. -/
def wordPoint (s : List Bool) : Cantor := streamExtend s fun _ => false

/-- The dense sequence of the Cantor presentation. -/
def densePoint (m : ℕ) : Cantor := wordPoint (denseWord m)

/-- Decoding an index to a binary word is primitive recursive. -/
theorem primrec_denseWord : Primrec denseWord :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- Decoding inverts encoding on binary words. -/
theorem denseWord_encode (s : List Bool) : denseWord (Encodable.encode s) = s := by
  simp [denseWord, Encodable.encodek]

/-- Coordinates of an extended word: the word's entries below its length, `false` beyond. -/
theorem wordPoint_apply (s : List Bool) (i : ℕ) : wordPoint s i = s.getD i false := by
  by_cases h : i < s.length
  · rw [wordPoint, streamExtend_apply_lt _ _ h, List.getD_eq_getElem _ _ h]
  · rw [wordPoint, streamExtend_apply_ge _ _ (Nat.le_of_not_lt h),
      List.getD_eq_default _ _ (Nat.le_of_not_lt h)]

private theorem densePoint_apply (m i : ℕ) : densePoint m i = (denseWord m).getD i false :=
  wordPoint_apply _ i

/-! ### Word-level distance of two dense points

The exact criterion: `wordPoint s = wordPoint t` iff the `false`-padded words agree
below `wordBound s t = max s.length t.length` (beyond it both pads are `false`); when
they differ, the first difference of the streams is the first padded-word mismatch
`wordFirstDiff s t < wordBound s t`, and the distance is `(1/2) ^ wordFirstDiff s t`. -/

/-- Beyond `wordBound s t` both padded words read `false`. -/
private def wordBound (s t : List Bool) : ℕ := max s.length t.length

/-- Padded-word mismatch at coordinate `i`. -/
private def wordMism (s t : List Bool) (i : ℕ) : Bool := decide (s.getD i false ≠ t.getD i false)

/-- First padded mismatch below the bound (`= wordBound s t` when there is none). -/
private def wordFirstDiff (s t : List Bool) : ℕ :=
  (List.range (wordBound s t)).findIdx (wordMism s t)

private theorem getD_eq_false_of_bound_le {s t : List Bool} {i : ℕ} (h : wordBound s t ≤ i) :
    s.getD i false = false ∧ t.getD i false = false :=
  ⟨List.getD_eq_default _ _ (le_trans (le_max_left _ _) h),
    List.getD_eq_default _ _ (le_trans (le_max_right _ _) h)⟩

/-- The decidable equality criterion for extended words. -/
private theorem wordPoint_eq_iff {s t : List Bool} :
    wordPoint s = wordPoint t ↔
      ∀ i < wordBound s t, s.getD i false = t.getD i false := by
  constructor
  · intro h i _
    have := congrFun h i
    rwa [wordPoint_apply, wordPoint_apply] at this
  · intro h
    funext i
    rw [wordPoint_apply, wordPoint_apply]
    by_cases hi : i < wordBound s t
    · exact h i hi
    · obtain ⟨hs, ht⟩ := getD_eq_false_of_bound_le (Nat.le_of_not_lt hi)
      rw [hs, ht]

private theorem wordFirstDiff_lt_bound {s t : List Bool} (h : wordPoint s ≠ wordPoint t) :
    wordFirstDiff s t < wordBound s t := by
  obtain ⟨i, hi, hne⟩ : ∃ i, i < wordBound s t ∧ s.getD i false ≠ t.getD i false := by
    by_contra hall
    push Not at hall
    exact h (wordPoint_eq_iff.mpr hall)
  have hlt : (List.range (wordBound s t)).findIdx (wordMism s t)
      < (List.range (wordBound s t)).length :=
    List.findIdx_lt_length_of_exists
      ⟨i, List.mem_range.mpr hi, by simp only [wordMism, decide_eq_true_eq]; exact hne⟩
  simpa [wordFirstDiff] using hlt

private theorem wordFirstDiff_eq_bound {s t : List Bool} (h : wordPoint s = wordPoint t) :
    wordFirstDiff s t = wordBound s t := by
  have hfalse : ∀ x ∈ List.range (wordBound s t), wordMism s t x = false := by
    intro x hx
    simp only [wordMism, decide_eq_false_iff_not, ne_eq, not_not]
    exact wordPoint_eq_iff.mp h x (List.mem_range.mp hx)
  have := List.findIdx_eq_length_of_false hfalse
  simpa [wordFirstDiff] using this

/-- When the extended words differ, their `PiNat.firstDiff` is the first padded-word
mismatch. -/
private theorem firstDiff_wordPoint {s t : List Bool} (h : wordPoint s ≠ wordPoint t) :
    PiNat.firstDiff (wordPoint s) (wordPoint t) = wordFirstDiff s t := by
  have hdlt := wordFirstDiff_lt_bound h
  have hdlt' : wordFirstDiff s t < (List.range (wordBound s t)).length := by simpa using hdlt
  have hmism : wordMism s t (wordFirstDiff s t) = true := by
    have := List.findIdx_getElem (p := wordMism s t)
      (xs := List.range (wordBound s t)) (w := hdlt')
    simpa [wordFirstDiff] using this
  have hne_d : wordPoint s (wordFirstDiff s t) ≠ wordPoint t (wordFirstDiff s t) := by
    rw [wordPoint_apply, wordPoint_apply]
    simp only [wordMism, decide_eq_true_eq] at hmism
    exact hmism
  have hagree : ∀ j < wordFirstDiff s t, wordPoint s j = wordPoint t j := by
    intro j hj
    have hfalse := List.not_of_lt_findIdx (p := wordMism s t)
      (xs := List.range (wordBound s t)) (i := j) (by simpa [wordFirstDiff] using hj)
    have hidx : wordMism s t j = false := by simpa using hfalse
    rw [wordPoint_apply, wordPoint_apply]
    simp only [wordMism, decide_eq_false_iff_not, ne_eq, not_not] at hidx
    exact hidx
  refine le_antisymm ?_ ?_
  · by_contra hlt
    push Not at hlt
    exact hne_d (PiNat.apply_eq_of_lt_firstDiff hlt)
  · by_contra hlt
    push Not at hlt
    exact PiNat.apply_firstDiff_ne h (hagree _ hlt)

/-! ### The distance as a rational code -/

/-- `2 ^ d` through primitive-recursion-friendly iteration. -/
private def pow2 (d : ℕ) : ℕ := (fun x => 2 * x)^[d] 1

private theorem pow2_eq (d : ℕ) : pow2 d = 2 ^ d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow2, Function.iterate_succ_apply', ← pow2, ih, pow_succ]; ring

private theorem primrec_pow2 : Primrec pow2 :=
  (primrec_pow 2).of_eq fun d => (pow2_eq d).symm

/-- The rational code of the distance between two dense points: `0` for equal extended
words, otherwise `1 / 2 ^ wordFirstDiff` as the unnormalized fraction
`(1 - 0)/((2^d - 1) + 1)`. -/
private def distCode (m₁ m₂ : ℕ) : ℕ :=
  if wordFirstDiff (denseWord m₁) (denseWord m₂) = wordBound (denseWord m₁) (denseWord m₂)
  then zeroCode
  else Nat.pair (Nat.pair 1 0) (pow2 (wordFirstDiff (denseWord m₁) (denseWord m₂)) - 1)

private theorem primrec₂_distCode : Primrec₂ distCode := by
  have hs : Primrec fun p : ℕ × ℕ => denseWord p.1 := primrec_denseWord.comp Primrec.fst
  have ht : Primrec fun p : ℕ × ℕ => denseWord p.2 := primrec_denseWord.comp Primrec.snd
  have hbound : Primrec fun p : ℕ × ℕ => wordBound (denseWord p.1) (denseWord p.2) :=
    Primrec.nat_max.comp (Primrec.list_length.comp hs) (Primrec.list_length.comp ht)
  have h1 : Primrec fun q : (ℕ × ℕ) × ℕ => (denseWord q.1.1).getD q.2 false :=
    (Primrec.list_getD false).comp
      (primrec_denseWord.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
  have h2 : Primrec fun q : (ℕ × ℕ) × ℕ => (denseWord q.1.2).getD q.2 false :=
    (Primrec.list_getD false).comp
      (primrec_denseWord.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hmismRaw : PrimrecPred fun q : (ℕ × ℕ) × ℕ =>
      ¬((denseWord q.1.1).getD q.2 false = (denseWord q.1.2).getD q.2 false) :=
    (Primrec.eq.comp h1 h2).not
  have hmism : Primrec₂ fun (p : ℕ × ℕ) (i : ℕ) =>
      wordMism (denseWord p.1) (denseWord p.2) i := by
    obtain ⟨_, hraw⟩ := hmismRaw
    exact hraw.of_eq fun q => decide_eq_decide.mpr Iff.rfl
  have hfd : Primrec fun p : ℕ × ℕ => wordFirstDiff (denseWord p.1) (denseWord p.2) :=
    (Primrec.list_findIdx (Primrec.list_range.comp hbound) hmism).of_eq fun p => rfl
  have hpow : Primrec fun p : ℕ × ℕ =>
      pow2 (wordFirstDiff (denseWord p.1) (denseWord p.2)) := primrec_pow2.comp hfd
  exact (Primrec.ite (Primrec.eq.comp hfd hbound) (Primrec.const zeroCode)
    (Primrec₂.natPair.comp (Primrec.const (Nat.pair 1 0))
      (Primrec.nat_sub.comp hpow (Primrec.const 1)))).of_eq fun p => rfl

/-- The distance between two dense points is exactly the coded rational. -/
private theorem dist_densePoint_eq (m₁ m₂ : ℕ) :
    dist (densePoint m₁) (densePoint m₂) = ((ratOfCode (distCode m₁ m₂) : ℚ) : ℝ) := by
  by_cases h : densePoint m₁ = densePoint m₂
  · rw [distCode, if_pos (wordFirstDiff_eq_bound h), ratOfCode_zeroCode, h, dist_self]
    norm_num
  · have hne : wordFirstDiff (denseWord m₁) (denseWord m₂)
        ≠ wordBound (denseWord m₁) (denseWord m₂) :=
      Nat.ne_of_lt (wordFirstDiff_lt_bound h)
    rw [distCode, if_neg hne, cantor_dist_eq_of_ne h]
    have h' : wordPoint (denseWord m₁) ≠ wordPoint (denseWord m₂) := h
    rw [show PiNat.firstDiff (densePoint m₁) (densePoint m₂)
        = wordFirstDiff (denseWord m₁) (denseWord m₂) from firstDiff_wordPoint h']
    set d := wordFirstDiff (denseWord m₁) (denseWord m₂) with hd
    have hpos : 0 < pow2 d := by rw [pow2_eq]; positivity
    have hden : ((pow2 d - 1 : ℕ) : ℚ) + 1 = ((2 : ℚ)) ^ d := by
      have hsub : (pow2 d - 1) + 1 = pow2 d := Nat.succ_pred_eq_of_pos hpos
      have : (((pow2 d - 1) + 1 : ℕ) : ℚ) = ((pow2 d : ℕ) : ℚ) := by exact_mod_cast hsub
      push_cast at this ⊢
      rw [this, pow2_eq]
      push_cast
      ring
    rw [ratOfCode]
    simp only [Nat.unpair_pair, hden]
    push_cast
    rw [div_pow, one_pow]
    norm_num

/-! ### Density -/

private theorem dist_wordPoint_streamTake (x : Cantor) (n : ℕ) :
    dist (wordPoint (streamTake x n)) x ≤ (1 / 2 : ℝ) ^ n := by
  have hmem : wordPoint (streamTake x n) ∈ PiNat.cylinder x n := by
    rw [← cylinder_streamTake]
    exact streamExtend_mem_cylinder _ _
  exact cantor_mem_cylinder_iff_dist_le.mp hmem

private theorem denseRange_densePoint : DenseRange densePoint := by
  rw [Metric.denseRange_iff]
  intro x r hr
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨Encodable.encode (streamTake x n), lt_of_le_of_lt ?_ hn⟩
  have h1 : densePoint (Encodable.encode (streamTake x n)) = wordPoint (streamTake x n) := by
    rw [densePoint, denseWord_encode]
  rw [h1, dist_comm]
  exact dist_wordPoint_streamTake x n

/-! ### The presentation -/

/-- The Cantor computable metric presentation: dense sequence the `false`-extended decoded
words; both threshold comparisons semidecided (indeed decided) through the exact rational
code of the distance between two dense points. -/
def cantorPresentation : ComputableMetricPresentation Cantor where
  dense := densePoint
  denseRange := denseRange_densePoint
  ltSemidec := repred_of_ratLt
    (primrec₂_distCode.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)
    fun w => by rw [dist_densePoint_eq w.1 w.2.1]; exact_mod_cast Iff.rfl
  gtSemidec := repred_of_ratLt (Primrec.snd.comp Primrec.snd)
    (primrec₂_distCode.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    fun w => by rw [dist_densePoint_eq w.1 w.2.1]; exact_mod_cast Iff.rfl

/-! ### Direction 1: `cantorRep` names to fast Cauchy names -/

/-- On a strict Cantor name, the decoded word of a prefix is the prefix of the point. -/
private theorem natWordToBool_streamTake {p : Baire} (hle : ∀ k, p k ≤ 1) (n : ℕ) :
    natWordToBool (streamTake p n) = streamTake (fun k => p k == 1) n := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [natWordToBool, List.getElem_map, getElem_streamTake]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle i) with h | h <;> simp [h]

private theorem computableMap_cantorRep_to_cauchyRep :
    ComputableMap cantorRep cantorPresentation.cauchyRep id := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode (b := fun n _ => n + 1)
    (g := fun w => Encodable.encode (natWordToBool (ofNat (List ℕ) w.unpair.2)))
    (Primrec.succ.comp Primrec.fst)
    (Primrec.encode.comp (primrec_natWordToBool.comp
      ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd)))
  have hcomp : c.Computes fun p n => Encodable.encode (natWordToBool (streamTake p (n + 1))) := by
    intro p n
    rw [hc p n]
    simp only [Nat.unpair_pair, ofNat_encode]
  refine ⟨c, Realizes.of_computes hcomp fun p x hpx => ?_⟩
  obtain ⟨hle, hx⟩ := cantorRep_names_iff.mp hpx
  refine (cantorPresentation.cauchyRep_names_iff).mpr fun n => ?_
  have hword : natWordToBool (streamTake p (n + 1)) = streamTake x (n + 1) := by
    rw [natWordToBool_streamTake hle, hx]
  change dist (densePoint (Encodable.encode (natWordToBool (streamTake p (n + 1))))) x
      ≤ ((2 : ℝ)⁻¹) ^ n
  rw [hword, inv_two_eq_half]
  have h1 : densePoint (Encodable.encode (streamTake x (n + 1)))
      = wordPoint (streamTake x (n + 1)) := by
    rw [densePoint, denseWord_encode]
  rw [h1]
  exact le_trans (dist_wordPoint_streamTake x (n + 1)) (half_pow_succ_le n)

/-! ### Direction 2: fast Cauchy names to `cantorRep` names -/

private theorem computableMap_cauchyRep_to_cantorRep :
    ComputableMap cantorPresentation.cauchyRep cantorRep id := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode (b := fun n _ => n + 2)
    (g := fun w => cond ((denseWord
        ((ofNat (List ℕ) w.unpair.2).getD (w.unpair.1 + 1) 0)).getD w.unpair.1 false) 1 0)
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2))
    (Primrec.cond
      ((Primrec.list_getD false).comp
        (primrec_denseWord.comp ((Primrec.list_getD 0).comp
          ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd)
          (Primrec.succ.comp primrec_unpairFst)))
        primrec_unpairFst)
      (Primrec.const 1) (Primrec.const 0))
  have hcomp : c.Computes fun q i => cond ((denseWord (q (i + 1))).getD i false) 1 0 := by
    intro q i
    rw [hc q i]
    simp only [Nat.unpair_pair, ofNat_encode,
      streamTake_getD q (by omega : i + 1 < i + 2)]
  refine ⟨c, Realizes.of_computes hcomp fun q x hqx => ?_⟩
  have hnp := (cantorPresentation.cauchyRep_names_iff).mp hqx
  have hagree : ∀ i, (denseWord (q (i + 1))).getD i false = x i := by
    intro i
    have hd : dist (densePoint (q (i + 1))) x < (1 / 2 : ℝ) ^ i := by
      refine lt_of_le_of_lt (le_trans (hnp (i + 1)) (le_of_eq ?_)) (half_pow_succ_lt i)
      rw [inv_two_eq_half]
    have := cantor_apply_eq_of_dist_lt hd (le_refl i)
    rwa [densePoint_apply] at this
  refine cantorRep_names_iff.mpr ⟨fun i => ?_, ?_⟩
  · cases (denseWord (q (i + 1))).getD i false <;> simp
  · funext i
    simp only [id_eq]
    rw [← hagree i]
    cases (denseWord (q (i + 1))).getD i false <;> rfl

/-! ### The equivalence -/

/-- The fast Cauchy representation of the Cantor presentation is computably equivalent to
the strict Cantor representation. -/
theorem cantorPresentation_cauchyRep_equiv : cantorPresentation.cauchyRep ≡c cantorRep :=
  ⟨computableMap_cauchyRep_to_cantorRep, computableMap_cantorRep_to_cauchyRep⟩

end ComputableAnalysis
