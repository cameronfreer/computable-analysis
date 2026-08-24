/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.CylinderValues
import ComputableAnalysis.Measure.Construction
import ComputableAnalysis.Metric.Real
import ComputableAnalysis.Metric.RatCodeArith
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Measure constructors: Dirac, Bernoulli products, mixtures, binary products

Each construction produces a `ProbabilityMeasure Cantor` through unit 19's existence
theorem from an explicitly consistent cylinder-mass function, and comes with a `cylMass`
law and a computability theorem:

* `diracMeasure` — point mass; computable-point preservation via the uniform
  cylinder-value equivalence (`computablePoint_cantorMeasureRep_iff`) and the decidable
  cylinder-membership test on a computable `cantorRep` name.
* `bernoulliProduct` — the i.i.d. product measure with parameter `p ∈ [0,1]`, uniformly
  computable in the parameter (`computableMap_bernoulliProduct`).
* `finiteMixture` — convex mixtures (normalization `∑ w = 1` is a hypothesis, never
  repaired), with a single uniform realizer over the pinned interleaved input
  (`exists_uniform_finiteMixture_realizer`).
* `productMeasure` — the binary product along the interleaving identification, equal to
  the mathlib product measure pushed through `Cantor.interleave`
  (`productMeasure_eq_map_prod`) and computable (`computableMap_productMeasure`).

The code-level rational arithmetic (`addCode`, `mulCode`, `clampCode`, …) comes from
`ComputableAnalysis/Metric/RatCodeArith.lean`, and the clamped-approximation estimates
(`clamp_mem_Icc`, `clamp_eq_self`, `abs_clamp_sub_clamp_le`) from
`ComputableAnalysis/Metric/Real.lean`, where they are public; the local copies this module
once carried have been deleted.
-/

open MeasureTheory

namespace ComputableAnalysis

open OracleCode Encodable Denumerable

/-! ### Word decoding (private duplicate of `Metric/Real.lean`) -/

section WordDecoding

/-- Decode a coordinate as the (default-`[]`) binary word it encodes. -/
private def wordOf (e : ℕ) : List Bool := (decode (α := List Bool) e).getD []

private theorem primrec_wordOf : Primrec wordOf :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

private theorem wordOf_encode (s : List Bool) : wordOf (encode s) = s := by
  simp [wordOf]

end WordDecoding

/-! ### Names bridges and estimate toolkit (private duplicates of `Metric/Real.lean`) -/

section EstimateToolkit

private theorem realNames_iff {p : Baire} {x : ℝ} :
    realRep.Names p x ↔
      ∀ n : ℕ, |((ratOfCode (p n) : ℚ) : ℝ) - x| ≤ (2 : ℝ)⁻¹ ^ n := by
  refine Iff.trans realPresentation.cauchyRep_names_iff ?_
  constructor
  · intro h n
    have hn := h n
    rw [Real.dist_eq] at hn
    exact hn
  · intro h n
    rw [Real.dist_eq]
    exact h n


/-- Products of `[0,1]`-families stay in `[0,1]`. -/
private theorem prod_mem_Icc {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) : (∏ i, a i) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun i _ => (ha i).1,
    Finset.prod_le_one (fun i _ => (ha i).1) fun i _ => (ha i).2⟩

/-- Telescoping product estimate: for families in `[0,1]`,
`|∏aᵢ - ∏bᵢ| ≤ ∑|aᵢ - bᵢ|`. -/
private theorem abs_prod_sub_prod_le :
    ∀ {k : ℕ} (a b : Fin k → ℝ), (∀ i, a i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, b i ∈ Set.Icc (0 : ℝ) 1) → |∏ i, a i - ∏ i, b i| ≤ ∑ i, |a i - b i| := by
  intro k
  induction k with
  | zero => intro a b _ _; simp
  | succ k ih =>
    intro a b ha hb
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have hBm : (∏ i : Fin k, b i.succ) ∈ Set.Icc (0 : ℝ) 1 :=
      prod_mem_Icc _ fun i => hb i.succ
    have ha0 : |a 0| ≤ 1 := abs_le.mpr ⟨by linarith [(ha 0).1], (ha 0).2⟩
    have hBabs : |∏ i : Fin k, b i.succ| ≤ 1 := abs_le.mpr ⟨by linarith [hBm.1], hBm.2⟩
    have hihs : |∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ|
        ≤ ∑ i : Fin k, |a i.succ - b i.succ| :=
      ih _ _ (fun i => ha i.succ) fun i => hb i.succ
    calc |a 0 * ∏ i : Fin k, a i.succ - b 0 * ∏ i : Fin k, b i.succ|
        = |a 0 * (∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ)
            + (a 0 - b 0) * ∏ i : Fin k, b i.succ| := by
          congr 1
          ring
      _ ≤ |a 0 * (∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ)|
            + |(a 0 - b 0) * ∏ i : Fin k, b i.succ| := abs_add_le _ _
      _ = |a 0| * |∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ|
            + |a 0 - b 0| * |∏ i : Fin k, b i.succ| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ i : Fin k, |a i.succ - b i.succ|) + |a 0 - b 0| * 1 := by
          gcongr
      _ = |a 0 - b 0| + ∑ i : Fin k, |a i.succ - b i.succ| := by ring

/-- Approximate factors multiply: if `A ∈ [0,1]` and `y ∈ [0,1]`, then
`|A·B - x·y| ≤ 2ε` whenever `|A - x| ≤ ε` and `|B - y| ≤ ε`. -/
private theorem abs_mul_sub_mul_le {A B x y ε : ℝ} (hA : A ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (h1 : |A - x| ≤ ε) (h2 : |B - y| ≤ ε) :
    |A * B - x * y| ≤ 2 * ε := by
  have hAabs : |A| ≤ 1 := abs_le.mpr ⟨by linarith [hA.1], hA.2⟩
  have hyabs : |y| ≤ 1 := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  have hε : (0 : ℝ) ≤ ε := (abs_nonneg _).trans h2
  calc |A * B - x * y|
      = |A * (B - y) + (A - x) * y| := by
        congr 1
        ring
    _ ≤ |A * (B - y)| + |(A - x) * y| := abs_add_le _ _
    _ = |A| * |B - y| + |A - x| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * ε + ε * 1 :=
        add_le_add (mul_le_mul hAabs h2 (abs_nonneg _) zero_le_one)
          (mul_le_mul h1 hyabs (abs_nonneg _) hε)
    _ = 2 * ε := by ring

/-- The precision bump: `k · 2⁻⁽ⁿ⁺ᵏ⁾ ≤ 2⁻ⁿ`, from `k < 2 ^ k`. -/
private theorem bump (k n : ℕ) : (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) ≤ (2 : ℝ)⁻¹ ^ n := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h1 : (k : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact hk
  calc (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k)
      = ((k : ℝ) * (2 : ℝ)⁻¹ ^ k) * (2 : ℝ)⁻¹ ^ n := by rw [pow_add]; ring
    _ ≤ 1 * (2 : ℝ)⁻¹ ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 : ℝ)⁻¹ ^ n := one_mul _

/-- Half-powers are antitone in the exponent. -/
private theorem halfPow_le_halfPow {m n : ℕ} (h : n ≤ m) :
    (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ n :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- List sum over `List.range` as a `Fin` sum. -/
private theorem listSum_range_map {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i : Fin k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Fin.sum_univ_castSucc, ih]
    simp

/-- A mapped list product as a `Fin` product over the coordinates. -/
private theorem listProd_map_eq_finProd {M : Type*} [CommMonoid M] (s : List Bool)
    (g : Bool → M) : (s.map g).prod = ∏ i : Fin s.length, g s[i] := by
  rw [← List.ofFn_getElem_eq_map, List.prod_ofFn]
  rfl

/-- Second-component monotonicity of `Nat.pair` (the `≤` version). -/
private theorem pair_le_pair_right (a : ℕ) {b c : ℕ} (h : b ≤ c) :
    Nat.pair a b ≤ Nat.pair a c := by
  rcases lt_or_eq_of_le h with h' | rfl
  · exact (Nat.pair_lt_pair_right a h').le
  · exact le_rfl

/-- A constant stream at an exact rational code is a `unitIntervalRep` name. -/
private theorem constNames_of_eq {v : Set.Icc (0 : ℝ) 1} {m : ℕ}
    (hm : ((ratOfCode m : ℚ) : ℝ) = v.val) :
    unitIntervalRep.Names (fun _ => m) v := by
  refine Representation.subtype_names_iff.mpr (realNames_iff.mpr fun n => ?_)
  rw [hm, sub_self, abs_zero]
  positivity

/-- The unit complement preserves `[0,1]`. -/
private theorem one_sub_mem_Icc {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    1 - x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- A Boolean selection between two `[0,1]` values stays in `[0,1]`. -/
private theorem cond_mem_Icc {a b : ℝ} (c : Bool) (ha : a ∈ Set.Icc (0 : ℝ) 1)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) : cond c a b ∈ Set.Icc (0 : ℝ) 1 := by
  cases c
  · exact hb
  · exact ha

/-- A Boolean selection of approximants keeps the error bound. -/
private theorem abs_cond_sub_cond_le {a a' b b' ε : ℝ} (c : Bool) (ha : |a - a'| ≤ ε)
    (hb : |b - b'| ≤ ε) : |cond c a b - cond c a' b'| ≤ ε := by
  cases c
  · exact hb
  · exact ha

/-- Complementing both approximants preserves the error. -/
private theorem abs_one_sub_sub_one_sub (A a : ℝ) : |1 - A - (1 - a)| = |A - a| := by
  have h : 1 - A - (1 - a) = -(A - a) := by ring
  rw [h, abs_neg]

end EstimateToolkit

/-! ### Measurability of interleaving -/

/-- Interleaving is jointly measurable: each output coordinate reads one input
coordinate of one component. -/
theorem Cantor.measurable_interleave :
    Measurable fun p : Cantor × Cantor => Cantor.interleave p.1 p.2 := by
  refine measurable_pi_lambda _ fun n => ?_
  by_cases h : n % 2 = 0
  · simp only [Cantor.interleave, ite_eq_left h]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [Cantor.interleave, ite_eq_right h]
    exact (measurable_pi_apply _).comp measurable_snd

/-! ### The Dirac measure -/

/-- Cylinder membership is decidable: it is the word equation `streamTake x s.length = s`
(`mem_cylinder_iff`). Private support for the indicator statement of
`cylMass_diracMeasure`. -/
private instance decidableMemCylinder (x : Cantor) (s : List Bool) :
    Decidable (x ∈ (cylinder s : Set Cantor)) :=
  decidable_of_iff _ mem_cylinder_iff.symm

/-- The Dirac point mass at `x`, as a probability measure on Cantor space. -/
noncomputable def diracMeasure (x : Cantor) : ProbabilityMeasure Cantor :=
  ⟨Measure.dirac x, inferInstance⟩

/-- Cylinder masses of the Dirac measure: the indicator of cylinder membership. -/
theorem cylMass_diracMeasure (x : Cantor) (s : List Bool) :
    cylMass (diracMeasure x) s = if x ∈ (cylinder s : Set Cantor) then 1 else 0 := by
  change ((Measure.dirac x) (cylinder s)).toReal = _
  rw [Measure.dirac_apply' _ (measurableSet_cylinder s)]
  by_cases h : x ∈ (cylinder s : Set Cantor)
  · rw [Set.indicator_of_mem h, ite_eq_left h]
    simp
  · rw [Set.indicator_of_notMem h, ite_eq_right h]
    simp

/-- The primrec decision kernel of the cylinder test: compare a decoded word with the
target word and answer with the exact rational code of `1` or `0`. -/
private def cylTestKernel (v : List ℕ × List Bool) : ℕ :=
  if natWordToBool v.1 = v.2 then oneCode else zeroCode

private theorem primrec_cylTestKernel : Primrec cylTestKernel := by
  unfold cylTestKernel
  exact Primrec.ite
    (PrimrecRel.comp Primrec.eq (primrec_natWordToBool.comp Primrec.fst) Primrec.snd)
    (Primrec.const oneCode) (Primrec.const zeroCode)

/-- The computable cylinder-membership test read off a computable `cantorRep` name:
`t (encode s)` compares the first `s.length` decoded bits with `s` and answers with the
exact rational code of the corresponding Dirac mass. -/
private theorem exists_computable_cylinderTest {q : ℕ → ℕ} (hq : Computable q) :
    ∃ t : ℕ → ℕ, Computable t ∧
      ∀ s : List Bool, t (encode s)
        = if natWordToBool ((List.range s.length).map q) = s then oneCode else zeroCode := by
  have hQL : Computable fun len => (List.range len).map q := by
    have h : Computable fun len : ℕ =>
        Nat.rec (motive := fun _ => List ℕ) [] (fun y IH => IH ++ [q y]) len :=
      Computable.nat_rec Computable.id (Computable.const [])
        (Primrec.list_append.to_comp.comp (Computable.snd.comp Computable.snd)
          (Primrec.list_cons.to_comp.comp (hq.comp (Computable.fst.comp Computable.snd))
            (Computable.const []))).to₂
    refine h.of_eq fun len => ?_
    induction len with
    | zero => simp
    | succ m ih => simp [List.range_succ, ih]
  have hw : Computable wordOf := primrec_wordOf.to_comp
  refine ⟨fun e => cylTestKernel ((List.range (wordOf e).length).map q, wordOf e),
    primrec_cylTestKernel.to_comp.comp
      ((hQL.comp (Primrec.list_length.to_comp.comp hw)).pair hw), fun s => ?_⟩
  simp only [cylTestKernel, wordOf_encode]

/-- **Dirac preserves computable points**: from a computable `cantorRep` name of `x`, one
computable first-order procedure produces all cylinder masses of `diracMeasure x` (the
constant `1`- or `0`-name selected by the decidable membership test), so the uniform
cylinder-value equivalence applies. -/
theorem computablePoint_diracMeasure {x : Cantor} (hx : cantorRep.ComputablePoint x) :
    cantorMeasureRep.ComputablePoint (diracMeasure x) := by
  obtain ⟨q, hqc, hqx⟩ := hx
  obtain ⟨hle, hxq⟩ := cantorRep_names_iff.mp hqx
  obtain ⟨t, htc, hts⟩ := exists_computable_cylinderTest hqc
  refine computablePoint_cantorMeasureRep_iff.mpr ⟨fun e _ => t e, ?_, ?_⟩
  · exact (htc.comp Computable.fst).to₂
  · intro s
    have hstream : natWordToBool ((List.range s.length).map q) = streamTake x s.length := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      simp only [natWordToBool, List.getElem_map, List.getElem_range, getElem_streamTake]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle i) with h | h <;> simp [hxq, h]
    have hts' : t (encode s) = if streamTake x s.length = s then oneCode else zeroCode := by
      rw [hts s, hstream]
    refine constNames_of_eq ?_
    have hval : (cylMass01 (diracMeasure x) s).val
        = if x ∈ (cylinder s : Set Cantor) then 1 else 0 := cylMass_diracMeasure x s
    rw [hts', hval]
    by_cases hxs : x ∈ (cylinder s : Set Cantor)
    · rw [ite_eq_left (mem_cylinder_iff.mp hxs), ite_eq_left hxs, ratOfCode_oneCode]
      norm_num
    · rw [ite_eq_right fun h => hxs (mem_cylinder_iff.mpr h), ite_eq_right hxs, ratOfCode_zeroCode]
      norm_num

/-! ### The Bernoulli product measure -/

/-- The Bernoulli product cylinder-mass function: each `true` bit contributes `p`, each
`false` bit `1 - p`. -/
private def bernoulliMass (p : Set.Icc (0 : ℝ) 1) (s : List Bool) : ℝ :=
  ∏ i : Fin s.length, cond s[i] p.1 (1 - p.1)

private theorem bernoulliMass_map (p : Set.Icc (0 : ℝ) 1) (s : List Bool) :
    bernoulliMass p s = (s.map fun b => cond b p.1 (1 - p.1)).prod := by
  unfold bernoulliMass
  exact (listProd_map_eq_finProd s fun b => cond b p.1 (1 - p.1)).symm

private theorem bernoulliMass_append (p : Set.Icc (0 : ℝ) 1) (s : List Bool) (b : Bool) :
    bernoulliMass p (s ++ [b]) = bernoulliMass p s * cond b p.1 (1 - p.1) := by
  rw [bernoulliMass_map, bernoulliMass_map, List.map_append, List.prod_append]
  simp

private theorem bernoulliMass_consistent (p : Set.Icc (0 : ℝ) 1) :
    IsConsistentCylinderMass (bernoulliMass p) := by
  refine ⟨by simp [bernoulliMass], fun s => ?_, fun s => ?_⟩
  · refine Finset.prod_nonneg fun i _ => ?_
    exact (cond_mem_Icc _ p.2 (one_sub_mem_Icc p.2)).1
  · rw [bernoulliMass_append, bernoulliMass_append, Bool.cond_false, Bool.cond_true]
    ring

/-- The i.i.d. Bernoulli **product** measure on Cantor space with parameter `p ∈ [0,1]`
(not the one-bit `bernoulliMeasure`), from unit 19's existence theorem. -/
noncomputable def bernoulliProduct (p : Set.Icc (0 : ℝ) 1) : ProbabilityMeasure Cantor :=
  (existsUnique_probabilityMeasure_of_isConsistent (bernoulliMass_consistent p)).exists.choose

/-- Cylinder masses of the Bernoulli product: the word-indexed product of bit
probabilities. -/
theorem cylMass_bernoulliProduct (p : Set.Icc (0 : ℝ) 1) (s : List Bool) :
    cylMass (bernoulliProduct p) s = ∏ i : Fin s.length, cond s[i] p.1 (1 - p.1) :=
  (existsUnique_probabilityMeasure_of_isConsistent
    (bernoulliMass_consistent p)).exists.choose_spec s

/-- The precision index of the Bernoulli realizer at output coordinate
`Nat.pair e n`: read the parameter name at precision `n + |s| + 1`. -/
private def bernoulliIdx (v : ℕ) : ℕ :=
  v.unpair.1.unpair.2 + (wordOf v.unpair.1.unpair.1).length + 1

private theorem primrec_bernoulliIdx : Primrec bernoulliIdx := by
  unfold bernoulliIdx
  exact Primrec.succ.comp (Primrec.nat_add.comp (primrec_unpairSnd.comp primrec_unpairFst)
    (Primrec.list_length.comp (primrec_wordOf.comp (primrec_unpairFst.comp primrec_unpairFst))))

/-- The clamped factor of the Bernoulli realizer, read from the oracle prefix. -/
private def bernoulliFactor (v : ℕ) : ℕ :=
  clampCode ((ofNat (List ℕ) v.unpair.2).getD (bernoulliIdx v) 0)

private theorem primrec_bernoulliFactor : Primrec bernoulliFactor := by
  unfold bernoulliFactor
  exact primrec_clampCode.comp ((Primrec.list_getD 0).comp
    ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd) primrec_bernoulliIdx)

/-- Oracle-free postprocessor of the Bernoulli realizer: multiply, over the bits of the
decoded word, the clamped factor for `true` and its unit complement for `false`. -/
private def bernoulliPost (v : ℕ) : ℕ :=
  prodCode ((wordOf v.unpair.1.unpair.1).map fun bit =>
    cond bit (bernoulliFactor v) (symmCode (bernoulliFactor v)))

private theorem primrec_bernoulliPost : Primrec bernoulliPost := by
  unfold bernoulliPost
  exact primrec_prodCode.comp (Primrec.list_map
    (primrec_wordOf.comp (primrec_unpairFst.comp primrec_unpairFst))
    (Primrec.cond Primrec.snd (primrec_bernoulliFactor.comp Primrec.fst)
      (primrec_symmCode.comp (primrec_bernoulliFactor.comp Primrec.fst))).to₂)

/-- Prefix length needed by the Bernoulli realizer at output coordinate `m` (the head
argument of the adaptive bound is unused). -/
private def bernoulliBound (m _h : ℕ) : ℕ :=
  m.unpair.2 + (wordOf m.unpair.1).length + 2

private theorem primrec₂_bernoulliBound : Primrec₂ bernoulliBound := by
  unfold bernoulliBound
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp (primrec_unpairSnd.comp Primrec.fst)
      (Primrec.list_length.comp (primrec_wordOf.comp (primrec_unpairFst.comp Primrec.fst))))
    (Primrec.const 2)).to₂

/-- **Uniform computability of the Bernoulli product in its parameter.** The realizer's
output component for the word `s` at precision `n` is the coded rational product of
`|s|` clamped copies of the parameter approximant at precision `n + |s| + 1` (`true`
bits) and its unit complement (`false` bits); the telescoping product estimate gives the
`2⁻ⁿ` rate. -/
theorem computableMap_bernoulliProduct :
    ComputableMap unitIntervalRep cantorMeasureRep bernoulliProduct := by
  obtain ⟨c, hc⟩ :=
    OracleCode.exists_prefixPostCode primrec₂_bernoulliBound primrec_bernoulliPost
  refine ⟨c, Realizes.of_computes hc fun P p hPp => ?_⟩
  have hP : ∀ j : ℕ, |((ratOfCode (P j) : ℚ) : ℝ) - p.val| ≤ (2 : ℝ)⁻¹ ^ j :=
    realNames_iff.mp (Representation.subtype_names_iff.mp hPp)
  refine cantorMeasureRep_names_iff.mpr fun s => ?_
  refine Representation.subtype_names_iff.mpr (realNames_iff.mpr fun n => ?_)
  have hpost : bernoulliPost (Nat.pair (Nat.pair (encode s) n)
      (encode (streamTake P (bernoulliBound (Nat.pair (encode s) n) (P 0)))))
      = prodCode (s.map fun bit =>
          cond bit (clampCode (P (n + s.length + 1)))
            (symmCode (clampCode (P (n + s.length + 1))))) := by
    simp only [bernoulliPost, bernoulliFactor, bernoulliIdx, bernoulliBound,
      Nat.unpair_pair, ofNat_encode, wordOf_encode]
    rw [streamTake_getD P (by omega)]
  have hcast : ((ratOfCode (bernoulliPost (Nat.pair (Nat.pair (encode s) n)
      (encode (streamTake P (bernoulliBound (Nat.pair (encode s) n) (P 0)))))) : ℚ) : ℝ)
      = ∏ i : Fin s.length,
          cond s[i] (max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)))
            (1 - max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ))) := by
    rw [hpost, ratOfCode_prodCode, List.map_map, listProd_map_eq_finProd (M := ℚ),
      Rat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases hb : s[i]
    · simp only [Function.comp_apply, Bool.cond_false, ratOfCode_symmCode,
        ratOfCode_clampCode]
      push_cast
      rfl
    · simp only [Function.comp_apply, Bool.cond_true, ratOfCode_clampCode]
      push_cast
      rfl
  have hA : max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
    clamp_mem_Icc _
  have hAp : |max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)) - p.val|
      ≤ (2 : ℝ)⁻¹ ^ (n + s.length + 1) := by
    calc |max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)) - p.val|
        = |max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ))
            - max 0 (min 1 p.val)| := by rw [clamp_eq_self p.2]
      _ ≤ |((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ) - p.val| :=
          abs_clamp_sub_clamp_le _ _
      _ ≤ (2 : ℝ)⁻¹ ^ (n + s.length + 1) := hP (n + s.length + 1)
  have hval : ((cylMass01 (bernoulliProduct p) s : ℝ))
      = ∏ i : Fin s.length, cond s[i] p.1 (1 - p.1) := cylMass_bernoulliProduct p s
  calc |((ratOfCode (bernoulliPost (Nat.pair (Nat.pair (encode s) n)
        (encode (streamTake P (bernoulliBound (Nat.pair (encode s) n) (P 0)))))) : ℚ) : ℝ)
        - (cylMass01 (bernoulliProduct p) s : ℝ)|
      = |(∏ i : Fin s.length,
            cond s[i] (max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)))
              (1 - max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ))))
          - ∏ i : Fin s.length, cond s[i] p.1 (1 - p.1)| := by rw [hcast, hval]
    _ ≤ ∑ i : Fin s.length,
          |cond s[i] (max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)))
              (1 - max 0 (min 1 ((ratOfCode (P (n + s.length + 1)) : ℚ) : ℝ)))
            - cond s[i] p.1 (1 - p.1)| :=
        abs_prod_sub_prod_le _ _
          (fun i => cond_mem_Icc _ hA (one_sub_mem_Icc hA))
          (fun i => cond_mem_Icc _ p.2 (one_sub_mem_Icc p.2))
    _ ≤ ∑ _i : Fin s.length, (2 : ℝ)⁻¹ ^ (n + s.length) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (abs_cond_sub_cond_le s[i] hAp ?_).trans (halfPow_le_halfPow (by omega))
        rw [abs_one_sub_sub_one_sub]
        exact hAp
    _ = (s.length : ℝ) * (2 : ℝ)⁻¹ ^ (n + s.length) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (2 : ℝ)⁻¹ ^ n := bump s.length n

/-! ### Finite mixtures -/

/-- `M` packs the `k` measure names per the pinned layout: the head carries `k`, and
component `i` is the measure name `fun n => M (1 + Nat.pair i n)`. -/
def PacksMeasures (M : Baire) (k : ℕ) (μs : Fin k → ProbabilityMeasure Cantor) : Prop :=
  M 0 = k ∧ ∀ i : Fin k, cantorMeasureRep.Names (fun n => M (1 + Nat.pair i n)) (μs i)

/-- The mixture cylinder-mass function: the weighted sum of component masses. -/
private noncomputable def mixtureMass {k : ℕ} (w : Fin k → Set.Icc (0 : ℝ) 1)
    (μs : Fin k → ProbabilityMeasure Cantor) (s : List Bool) : ℝ :=
  ∑ i, (w i).1 * cylMass (μs i) s

private theorem mixtureMass_consistent {k : ℕ} (w : Fin k → Set.Icc (0 : ℝ) 1)
    (hw : ∑ i, (w i).1 = 1) (μs : Fin k → ProbabilityMeasure Cantor) :
    IsConsistentCylinderMass (mixtureMass w μs) := by
  refine ⟨?_, fun s => ?_, fun s => ?_⟩
  · unfold mixtureMass
    simp only [cylMass_nil, mul_one]
    exact hw
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (w i).2.1 (cylMass_nonneg _ _)
  · unfold mixtureMass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cylMass_split (μs i) s]
    ring

/-- The finite convex mixture `∑ᵢ wᵢ • μᵢ`. Normalization (`∑ w = 1`) is a hypothesis —
never re-derived or repaired — and the measure comes from unit 19's existence theorem. -/
noncomputable def finiteMixture {k : ℕ} (w : Fin k → Set.Icc (0 : ℝ) 1)
    (hw : ∑ i, (w i).1 = 1) (μs : Fin k → ProbabilityMeasure Cantor) :
    ProbabilityMeasure Cantor :=
  (existsUnique_probabilityMeasure_of_isConsistent
    (mixtureMass_consistent w hw μs)).exists.choose

/-- Cylinder masses of a finite mixture: the weighted sum of component masses. -/
theorem cylMass_finiteMixture {k : ℕ} (w : Fin k → Set.Icc (0 : ℝ) 1)
    (hw : ∑ i, (w i).1 = 1) (μs : Fin k → ProbabilityMeasure Cantor) (s : List Bool) :
    cylMass (finiteMixture w hw μs) s = ∑ i, (w i).1 * cylMass (μs i) s :=
  (existsUnique_probabilityMeasure_of_isConsistent
    (mixtureMass_consistent w hw μs)).exists.choose_spec s

/-- The decoded oracle prefix of the mixture realizer. -/
private def mixList (v : ℕ) : List ℕ := ofNat (List ℕ) v.unpair.2

private theorem primrec_mixList : Primrec mixList := by
  unfold mixList
  exact (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd

/-- The component count, read at the head of the interleaved input. -/
private def mixK (v : ℕ) : ℕ := (mixList v).getD 0 0

private theorem primrec_mixK : Primrec mixK := by
  unfold mixK
  exact (Primrec.list_getD 0).comp primrec_mixList (Primrec.const 0)

/-- The bumped working precision `n + k + 1` of the mixture realizer. -/
private def mixR (v : ℕ) : ℕ := v.unpair.1.unpair.2 + mixK v + 1

private theorem primrec_mixR : Primrec mixR := by
  unfold mixR
  exact Primrec.succ.comp (Primrec.nat_add.comp
    (primrec_unpairSnd.comp primrec_unpairFst) primrec_mixK)

/-- The `i`-th mixture term: clamped weight times clamped component mass, read at the
interleaved coordinates. -/
private def mixTerm (v i : ℕ) : ℕ :=
  mulCode (clampCode ((mixList v).getD (2 * (1 + Nat.pair i (mixR v))) 0))
    (clampCode ((mixList v).getD
      (2 * (1 + Nat.pair i (Nat.pair v.unpair.1.unpair.1 (mixR v))) + 1) 0))

private theorem primrec₂_mixTerm : Primrec₂ mixTerm := by
  unfold mixTerm
  have hL : Primrec fun p : ℕ × ℕ => mixList p.1 := primrec_mixList.comp Primrec.fst
  have hR : Primrec fun p : ℕ × ℕ => mixR p.1 := primrec_mixR.comp Primrec.fst
  have hIW : Primrec fun p : ℕ × ℕ => 2 * (1 + Nat.pair p.2 (mixR p.1)) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp Primrec.snd hR))
  have hIM : Primrec fun p : ℕ × ℕ =>
      2 * (1 + Nat.pair p.2 (Nat.pair p.1.unpair.1.unpair.1 (mixR p.1))) + 1 :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp Primrec.snd
        (Primrec₂.natPair.comp
          ((primrec_unpairFst.comp primrec_unpairFst).comp Primrec.fst) hR))))
  exact (primrec₂_mulCode.comp
    (primrec_clampCode.comp ((Primrec.list_getD 0).comp hL hIW))
    (primrec_clampCode.comp ((Primrec.list_getD 0).comp hL hIM))).to₂

/-- Oracle-free postprocessor of the mixture realizer: sum the `k` clamped weighted
terms. -/
private def mixPost (v : ℕ) : ℕ := sumCode ((List.range (mixK v)).map (mixTerm v))

private theorem primrec_mixPost : Primrec mixPost := by
  unfold mixPost
  exact primrec_sumCode.comp
    (Primrec.list_map (Primrec.list_range.comp primrec_mixK) primrec₂_mixTerm)

/-- Prefix length needed by the mixture realizer at output coordinate `m` with head
`h = k`: it covers all interleaved weight and mass coordinates at the bumped precision. -/
private def mixBound (m h : ℕ) : ℕ :=
  2 * (1 + Nat.pair h (Nat.pair m.unpair.1 (m.unpair.2 + h + 1))) + 2

private theorem primrec₂_mixBound : Primrec₂ mixBound := by
  unfold mixBound
  exact (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp Primrec.snd
      (Primrec₂.natPair.comp (primrec_unpairFst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.nat_add.comp
          (primrec_unpairSnd.comp Primrec.fst) Primrec.snd))))))
    (Primrec.const 2)).to₂

/-- **One total oracle code uniformly realizes all finite mixtures** over the pinned
interleaved input `Baire.interleave W M`: `W` packs the `k` weights (unit 16 layout, so
`k` is readable at the head `(Baire.interleave W M) 0 = W 0`), `M` packs the `k` measure
names. The output component for the word `s` at precision `n` is the coded sum of clamped
weight-times-mass products at the bumped precision `n + k + 1`. -/
theorem exists_uniform_finiteMixture_realizer :
    ∃ c : OracleCode, ∀ (k : ℕ) (W M : Baire) (w : Fin k → Set.Icc (0 : ℝ) 1)
      (hw : ∑ i, (w i).1 = 1) (μs : Fin k → ProbabilityMeasure Cantor),
      Packs W k (fun i => (w i).1) → PacksMeasures M k μs →
      ∃ q ∈ c.evalStream (Baire.interleave W M),
        cantorMeasureRep.Names q (finiteMixture w hw μs) := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode primrec₂_mixBound primrec_mixPost
  refine ⟨c, fun k W M w hw μs hW hM => ?_⟩
  have hG0 : Baire.interleave W M 0 = k := by
    have h0 : Baire.interleave W M 0 = W 0 := Baire.interleave_even W M 0
    rw [h0, hW.1]
  set Q : Baire := fun m => mixPost (Nat.pair m (encode (streamTake (Baire.interleave W M)
    (mixBound m (Baire.interleave W M 0))))) with hQdef
  have hQmem : Q ∈ c.evalStream (Baire.interleave W M) :=
    mem_evalStream.mpr fun m => by rw [hc (Baire.interleave W M) m]; exact Part.mem_some _
  refine ⟨Q, hQmem, cantorMeasureRep_names_iff.mpr fun s => ?_⟩
  refine Representation.subtype_names_iff.mpr (realNames_iff.mpr fun n => ?_)
  have hB : mixBound (Nat.pair (encode s) n) (Baire.interleave W M 0)
      = 2 * (1 + Nat.pair k (Nat.pair (encode s) (n + k + 1))) + 2 := by
    rw [hG0]
    simp only [mixBound, Nat.unpair_pair]
  have hgetD : ∀ j, j < 2 * (1 + Nat.pair k (Nat.pair (encode s) (n + k + 1))) + 2 →
      (streamTake (Baire.interleave W M)
        (mixBound (Nat.pair (encode s) n) (Baire.interleave W M 0))).getD j 0
        = Baire.interleave W M j := by
    intro j hj
    rw [hB]
    exact streamTake_getD _ hj
  have hk0 : (streamTake (Baire.interleave W M)
      (mixBound (Nat.pair (encode s) n) (Baire.interleave W M 0))).getD 0 0 = k := by
    rw [hgetD 0 (by omega), hG0]
  have hQval : ratOfCode (Q (Nat.pair (encode s) n))
      = ∑ i : Fin k, ratOfCode (mulCode
          (clampCode (W (1 + Nat.pair i (n + k + 1))))
          (clampCode (M (1 + Nat.pair i (Nat.pair (encode s) (n + k + 1)))))) := by
    simp only [hQdef]
    simp only [mixPost, mixK, mixList, Nat.unpair_pair, ofNat_encode, hk0]
    rw [ratOfCode_sumCode, List.map_map, listSum_range_map (M := ℚ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 : Nat.pair (i : ℕ) (Nat.pair (encode s) (n + k + 1))
        < Nat.pair k (Nat.pair (encode s) (n + k + 1)) :=
      Nat.pair_lt_pair_left _ i.isLt
    have hiW : 2 * (1 + Nat.pair (i : ℕ) (n + k + 1))
        < 2 * (1 + Nat.pair k (Nat.pair (encode s) (n + k + 1))) + 2 := by
      have h1 : Nat.pair (i : ℕ) (n + k + 1)
          ≤ Nat.pair (i : ℕ) (Nat.pair (encode s) (n + k + 1)) :=
        pair_le_pair_right _ (Nat.right_le_pair _ _)
      omega
    have hiM : 2 * (1 + Nat.pair (i : ℕ) (Nat.pair (encode s) (n + k + 1))) + 1
        < 2 * (1 + Nat.pair k (Nat.pair (encode s) (n + k + 1))) + 2 := by
      omega
    simp only [Function.comp_apply, mixTerm, mixK, mixR, mixList, Nat.unpair_pair,
      ofNat_encode, hk0]
    rw [hgetD _ hiW, hgetD _ hiM, Baire.interleave_even, Baire.interleave_odd]
  have hWest : ∀ i : Fin k,
      |((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ) - (w i).1|
        ≤ (2 : ℝ)⁻¹ ^ (n + k + 1) := fun i => realNames_iff.mp (hW.2 i) (n + k + 1)
  have hMest : ∀ i : Fin k,
      |((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s) (n + k + 1)))) : ℚ) : ℝ)
        - cylMass (μs i) s| ≤ (2 : ℝ)⁻¹ ^ (n + k + 1) := fun i =>
    realNames_iff.mp (Representation.subtype_names_iff.mp
      (cantorMeasureRep_names_iff.mp (hM.2 i) s)) (n + k + 1)
  have hterm : ∀ i : Fin k,
      |max 0 (min 1 ((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ))
          * max 0 (min 1 ((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
              (n + k + 1)))) : ℚ) : ℝ))
        - (w i).1 * cylMass (μs i) s| ≤ 2 * (2 : ℝ)⁻¹ ^ (n + k + 1) := by
    intro i
    refine abs_mul_sub_mul_le (clamp_mem_Icc _)
      ⟨cylMass_nonneg _ _, cylMass_le_one _ _⟩ ?_ ?_
    · calc |max 0 (min 1 ((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ)) - (w i).1|
          = |max 0 (min 1 ((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ))
              - max 0 (min 1 (w i).1)| := by rw [clamp_eq_self (w i).2]
        _ ≤ |((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ) - (w i).1| :=
            abs_clamp_sub_clamp_le _ _
        _ ≤ (2 : ℝ)⁻¹ ^ (n + k + 1) := hWest i
    · calc |max 0 (min 1 ((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
              (n + k + 1)))) : ℚ) : ℝ)) - cylMass (μs i) s|
          = |max 0 (min 1 ((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
              (n + k + 1)))) : ℚ) : ℝ))
              - max 0 (min 1 (cylMass (μs i) s))| := by
            rw [clamp_eq_self ⟨cylMass_nonneg _ _, cylMass_le_one _ _⟩]
        _ ≤ |((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
              (n + k + 1)))) : ℚ) : ℝ) - cylMass (μs i) s| := abs_clamp_sub_clamp_le _ _
        _ ≤ (2 : ℝ)⁻¹ ^ (n + k + 1) := hMest i
  have hcast : ((ratOfCode (Q (Nat.pair (encode s) n)) : ℚ) : ℝ)
      = ∑ i : Fin k, max 0 (min 1 ((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ))
          * max 0 (min 1 ((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
              (n + k + 1)))) : ℚ) : ℝ)) := by
    rw [hQval, Rat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ratOfCode_mulCode, ratOfCode_clampCode, ratOfCode_clampCode]
    push_cast
    rfl
  have hval : ((cylMass01 (finiteMixture w hw μs) s : ℝ))
      = ∑ i, (w i).1 * cylMass (μs i) s := cylMass_finiteMixture w hw μs s
  calc |((ratOfCode (Q (Nat.pair (encode s) n)) : ℚ) : ℝ)
        - (cylMass01 (finiteMixture w hw μs) s : ℝ)|
      = |∑ i : Fin k,
          (max 0 (min 1 ((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ))
            * max 0 (min 1 ((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
                (n + k + 1)))) : ℚ) : ℝ))
            - (w i).1 * cylMass (μs i) s)| := by
        rw [hcast, hval, ← Finset.sum_sub_distrib]
    _ ≤ ∑ i : Fin k,
          |max 0 (min 1 ((ratOfCode (W (1 + Nat.pair i (n + k + 1))) : ℚ) : ℝ))
            * max 0 (min 1 ((ratOfCode (M (1 + Nat.pair i (Nat.pair (encode s)
                (n + k + 1)))) : ℚ) : ℝ))
            - (w i).1 * cylMass (μs i) s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, 2 * (2 : ℝ)⁻¹ ^ (n + k + 1) := Finset.sum_le_sum fun i _ => hterm i
    _ = (k : ℝ) * (2 * (2 : ℝ)⁻¹ ^ (n + k + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) := by
        rw [pow_succ]
        ring
    _ ≤ (2 : ℝ)⁻¹ ^ n := bump k n

/-! ### The binary product measure -/

private theorem wordEven_nil : wordEven ([] : List Bool) = [] := rfl

private theorem wordOdd_nil : wordOdd ([] : List Bool) = [] := rfl

/-- Appending one bit extends the even subword exactly when the length is even. -/
private theorem wordEven_append_bit (s : List Bool) (b : Bool) :
    wordEven (s ++ [b]) = if s.length % 2 = 0 then wordEven s ++ [b] else wordEven s := by
  by_cases h : s.length % 2 = 0
  · rw [ite_eq_left h]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : 2 * i < s.length + 1 := by
      have h1' := h1
      simp at h1'
      omega
    rw [getElem_wordEven h1]
    rcases Nat.lt_or_ge (2 * i) s.length with hlt | hge
    · have hiw : i < (wordEven s).length := by
        rw [length_wordEven]
        omega
      rw [List.getElem_append_left hlt, List.getElem_append_left hiw, getElem_wordEven hiw]
    · rw [List.getElem_append_right hge,
        List.getElem_append_right (by rw [length_wordEven]; omega)]
      simp
  · rw [ite_eq_right h]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : 2 * i < s.length := by
      have h1' := h1
      simp at h1'
      omega
    rw [getElem_wordEven h1, getElem_wordEven h2, List.getElem_append_left hi]

/-- Appending one bit extends the odd subword exactly when the length is odd. -/
private theorem wordOdd_append_bit (s : List Bool) (b : Bool) :
    wordOdd (s ++ [b]) = if s.length % 2 = 0 then wordOdd s else wordOdd s ++ [b] := by
  by_cases h : s.length % 2 = 0
  · rw [ite_eq_left h]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : 2 * i + 1 < s.length := by
      have h1' := h1
      simp at h1'
      omega
    rw [getElem_wordOdd h1, getElem_wordOdd h2, List.getElem_append_left hi]
  · rw [ite_eq_right h]
    refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
    have hi : 2 * i + 1 < s.length + 1 := by
      have h1' := h1
      simp at h1'
      omega
    rw [getElem_wordOdd h1]
    rcases Nat.lt_or_ge (2 * i + 1) s.length with hlt | hge
    · have hiw : i < (wordOdd s).length := by
        rw [length_wordOdd]
        omega
      rw [List.getElem_append_left hlt, List.getElem_append_left hiw, getElem_wordOdd hiw]
    · rw [List.getElem_append_right hge,
        List.getElem_append_right (by rw [length_wordOdd]; omega)]
      simp

/-- The product cylinder-mass function: the two deinterleaved subword masses multiply. -/
private noncomputable def prodMass (μ ν : ProbabilityMeasure Cantor) (s : List Bool) : ℝ :=
  cylMass μ (wordEven s) * cylMass ν (wordOdd s)

private theorem prodMass_consistent (μ ν : ProbabilityMeasure Cantor) :
    IsConsistentCylinderMass (prodMass μ ν) := by
  refine ⟨?_, fun s => ?_, fun s => ?_⟩
  · unfold prodMass
    rw [wordEven_nil, wordOdd_nil, cylMass_nil, cylMass_nil, mul_one]
  · exact mul_nonneg (cylMass_nonneg _ _) (cylMass_nonneg _ _)
  · unfold prodMass
    simp only [wordEven_append_bit, wordOdd_append_bit]
    by_cases h : s.length % 2 = 0
    · simp only [ite_eq_left h]
      rw [cylMass_split μ (wordEven s)]
      ring
    · simp only [ite_eq_right h]
      rw [cylMass_split ν (wordOdd s)]
      ring

/-- The binary product measure along the pinned interleaving identification, from unit
19's existence theorem applied to the deinterleaved product masses. -/
noncomputable def productMeasure (μ ν : ProbabilityMeasure Cantor) :
    ProbabilityMeasure Cantor :=
  (existsUnique_probabilityMeasure_of_isConsistent (prodMass_consistent μ ν)).exists.choose

/-- Cylinder masses of the product: the deinterleaved subword masses multiply. -/
theorem cylMass_productMeasure (μ ν : ProbabilityMeasure Cantor) (s : List Bool) :
    cylMass (productMeasure μ ν) s = cylMass μ (wordEven s) * cylMass ν (wordOdd s) :=
  (existsUnique_probabilityMeasure_of_isConsistent
    (prodMass_consistent μ ν)).exists.choose_spec s

/-- **Classical semantics of the product**: `productMeasure` is the image of the mathlib
product measure under the interleaving identification. Both sides are probability
measures agreeing on the generating π-system of cylinders (the preimage of a cylinder is
the product of the subword cylinders). -/
theorem productMeasure_eq_map_prod (μ ν : ProbabilityMeasure Cantor) :
    (productMeasure μ ν).toMeasure =
      (μ.toMeasure.prod ν.toMeasure).map fun p => Cantor.interleave p.1 p.2 := by
  have hpre : ∀ s : List Bool,
      (fun p : Cantor × Cantor => Cantor.interleave p.1 p.2) ⁻¹'
          (cylinder s : Set Cantor)
        = (cylinder (wordEven s) : Set Cantor) ×ˢ (cylinder (wordOdd s) : Set Cantor) := by
    intro s
    ext p
    simp only [Set.mem_preimage, Set.mem_prod]
    exact Cantor.interleave_mem_cylinder_iff
  have : IsProbabilityMeasure ((μ.toMeasure.prod ν.toMeasure).map
      fun p => Cantor.interleave p.1 p.2) :=
    Measure.isProbabilityMeasure_map Cantor.measurable_interleave.aemeasurable
  refine Measure.ext_of_generateFrom_of_iUnion cantorCylinders (fun _ => Set.univ)
    generateFrom_cantorCylinders.symm isPiSystem_cantorCylinders
    (Set.iUnion_const Set.univ) (fun _ => ⟨[], cylinder_nil⟩)
    (fun _ => measure_ne_top _ _) ?_
  rintro _ ⟨s, rfl⟩
  rw [Measure.map_apply Cantor.measurable_interleave (measurableSet_cylinder s), hpre s,
    Measure.prod_prod]
  have hL : (productMeasure μ ν).toMeasure (cylinder s)
      = ENNReal.ofReal (cylMass μ (wordEven s) * cylMass ν (wordOdd s)) := by
    rw [← cylMass_productMeasure]
    simp only [cylMass]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hL, ENNReal.ofReal_mul (cylMass_nonneg μ (wordEven s))]
  simp only [cylMass]
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- List-level even subword (a `Primrec`-friendly form of `wordEven`). -/
private def wordEvenL (s : List Bool) : List Bool :=
  (List.range ((s.length + 1) / 2)).map fun i => s.getD (2 * i) false

/-- List-level odd subword (a `Primrec`-friendly form of `wordOdd`). -/
private def wordOddL (s : List Bool) : List Bool :=
  (List.range (s.length / 2)).map fun i => s.getD (2 * i + 1) false

private theorem wordEvenL_eq (s : List Bool) : wordEvenL s = wordEven s := by
  refine List.ext_getElem (by simp [wordEvenL]) fun i h1 h2 => ?_
  have hi : 2 * i < s.length := by
    have h2' := h2
    simp at h2'
    omega
  simp only [wordEvenL, List.getElem_map, List.getElem_range]
  rw [getElem_wordEven h2, List.getD_eq_getElem _ _ hi]

private theorem wordOddL_eq (s : List Bool) : wordOddL s = wordOdd s := by
  refine List.ext_getElem (by simp [wordOddL]) fun i h1 h2 => ?_
  have hi : 2 * i + 1 < s.length := by
    have h2' := h2
    simp at h2'
    omega
  simp only [wordOddL, List.getElem_map, List.getElem_range]
  rw [getElem_wordOdd h2, List.getD_eq_getElem _ _ hi]

private theorem primrec_wordEvenL : Primrec wordEvenL := by
  unfold wordEvenL
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp
      (Primrec.succ.comp Primrec.list_length) (Primrec.const 2)))
    ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to₂

private theorem primrec_wordOddL : Primrec wordOddL := by
  unfold wordOddL
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)))
    ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))).to₂

/-- Even-component read index of the product realizer at word code `e`, precision `n`. -/
private def prodIdxE (e n : ℕ) : ℕ :=
  2 * Nat.pair (encode (wordEvenL (wordOf e))) (n + 2)

/-- Odd-component read index of the product realizer at word code `e`, precision `n`. -/
private def prodIdxO (e n : ℕ) : ℕ :=
  2 * Nat.pair (encode (wordOddL (wordOf e))) (n + 2) + 1

private theorem primrec₂_prodIdxE : Primrec₂ prodIdxE := by
  unfold prodIdxE
  exact (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp
    (Primrec.encode.comp (primrec_wordEvenL.comp (primrec_wordOf.comp Primrec.fst)))
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2)))).to₂

private theorem primrec₂_prodIdxO : Primrec₂ prodIdxO := by
  unfold prodIdxO
  exact (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec₂.natPair.comp
    (Primrec.encode.comp (primrec_wordOddL.comp (primrec_wordOf.comp Primrec.fst)))
    (Primrec.nat_add.comp Primrec.snd (Primrec.const 2))))).to₂

/-- Prefix length needed by the product realizer at output coordinate `m` (the head
argument of the adaptive bound is unused). -/
private def prodMeasureBound (m _h : ℕ) : ℕ :=
  prodIdxE m.unpair.1 m.unpair.2 + prodIdxO m.unpair.1 m.unpair.2 + 1

private theorem primrec₂_prodMeasureBound : Primrec₂ prodMeasureBound := by
  unfold prodMeasureBound
  exact (Primrec.succ.comp (Primrec.nat_add.comp
    (primrec₂_prodIdxE.comp (primrec_unpairFst.comp Primrec.fst)
      (primrec_unpairSnd.comp Primrec.fst))
    (primrec₂_prodIdxO.comp (primrec_unpairFst.comp Primrec.fst)
      (primrec_unpairSnd.comp Primrec.fst)))).to₂

/-- Oracle-free postprocessor of the product realizer: multiply the clamped component
approximants of the two subwords at precision `n + 2`. -/
private def prodMeasurePost (v : ℕ) : ℕ :=
  mulCode
    (clampCode ((ofNat (List ℕ) v.unpair.2).getD
      (prodIdxE v.unpair.1.unpair.1 v.unpair.1.unpair.2) 0))
    (clampCode ((ofNat (List ℕ) v.unpair.2).getD
      (prodIdxO v.unpair.1.unpair.1 v.unpair.1.unpair.2) 0))

private theorem primrec_prodMeasurePost : Primrec prodMeasurePost := by
  unfold prodMeasurePost
  have hL : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd
  have hE : Primrec fun v : ℕ => prodIdxE v.unpair.1.unpair.1 v.unpair.1.unpair.2 :=
    primrec₂_prodIdxE.comp (primrec_unpairFst.comp primrec_unpairFst)
      (primrec_unpairSnd.comp primrec_unpairFst)
  have hO : Primrec fun v : ℕ => prodIdxO v.unpair.1.unpair.1 v.unpair.1.unpair.2 :=
    primrec₂_prodIdxO.comp (primrec_unpairFst.comp primrec_unpairFst)
      (primrec_unpairSnd.comp primrec_unpairFst)
  exact primrec₂_mulCode.comp
    (primrec_clampCode.comp ((Primrec.list_getD 0).comp hL hE))
    (primrec_clampCode.comp ((Primrec.list_getD 0).comp hL hO))

/-- **Computability of the binary product.** The realizer reads the interleaved pair of
measure names and outputs, for the word `s` at precision `n`, the coded product of the
two clamped component approximants of `wordEven s` and `wordOdd s` at precision
`n + 2`. -/
theorem computableMap_productMeasure :
    ComputableMap (cantorMeasureRep.prod cantorMeasureRep) cantorMeasureRep
      fun p => productMeasure p.1 p.2 := by
  obtain ⟨c, hc⟩ :=
    OracleCode.exists_prefixPostCode primrec₂_prodMeasureBound primrec_prodMeasurePost
  refine ⟨c, Realizes.of_computes hc fun r ab hab => ?_⟩
  obtain ⟨hμ, hν⟩ := Representation.prod_names_iff.mp hab
  have hμM : MeasureNames r.evenPart ab.1 := cantorMeasureRep_names_iff.mp hμ
  have hνM : MeasureNames r.oddPart ab.2 := cantorMeasureRep_names_iff.mp hν
  refine cantorMeasureRep_names_iff.mpr fun s => ?_
  refine Representation.subtype_names_iff.mpr (realNames_iff.mpr fun n => ?_)
  have hidxE : prodIdxE (encode s) n = 2 * Nat.pair (encode (wordEven s)) (n + 2) := by
    simp only [prodIdxE, wordOf_encode, wordEvenL_eq]
  have hidxO : prodIdxO (encode s) n = 2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1 := by
    simp only [prodIdxO, wordOf_encode, wordOddL_eq]
  have hboundE : prodIdxE (encode s) n < prodMeasureBound (Nat.pair (encode s) n) (r 0) := by
    simp only [prodMeasureBound, Nat.unpair_pair]
    omega
  have hboundO : prodIdxO (encode s) n < prodMeasureBound (Nat.pair (encode s) n) (r 0) := by
    simp only [prodMeasureBound, Nat.unpair_pair]
    omega
  have hpost : prodMeasurePost (Nat.pair (Nat.pair (encode s) n)
      (encode (streamTake r (prodMeasureBound (Nat.pair (encode s) n) (r 0)))))
      = mulCode
          (clampCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))))
          (clampCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1))) := by
    simp only [prodMeasurePost, Nat.unpair_pair, ofNat_encode]
    rw [streamTake_getD r hboundE, streamTake_getD r hboundO, hidxE, hidxO]
  have hEest : |((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ)
      - cylMass ab.1 (wordEven s)| ≤ (2 : ℝ)⁻¹ ^ (n + 2) :=
    realNames_iff.mp (Representation.subtype_names_iff.mp (hμM (wordEven s))) (n + 2)
  have hOest : |((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ)
      - cylMass ab.2 (wordOdd s)| ≤ (2 : ℝ)⁻¹ ^ (n + 2) :=
    realNames_iff.mp (Representation.subtype_names_iff.mp (hνM (wordOdd s))) (n + 2)
  have hclampE : |max 0 (min 1
      ((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ))
      - cylMass ab.1 (wordEven s)| ≤ (2 : ℝ)⁻¹ ^ (n + 2) := by
    calc |max 0 (min 1
          ((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ))
          - cylMass ab.1 (wordEven s)|
        = |max 0 (min 1
            ((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ))
            - max 0 (min 1 (cylMass ab.1 (wordEven s)))| := by
          rw [clamp_eq_self ⟨cylMass_nonneg _ _, cylMass_le_one _ _⟩]
      _ ≤ |((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ)
            - cylMass ab.1 (wordEven s)| := abs_clamp_sub_clamp_le _ _
      _ ≤ (2 : ℝ)⁻¹ ^ (n + 2) := hEest
  have hclampO : |max 0 (min 1
      ((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ))
      - cylMass ab.2 (wordOdd s)| ≤ (2 : ℝ)⁻¹ ^ (n + 2) := by
    calc |max 0 (min 1
          ((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ))
          - cylMass ab.2 (wordOdd s)|
        = |max 0 (min 1
            ((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ))
            - max 0 (min 1 (cylMass ab.2 (wordOdd s)))| := by
          rw [clamp_eq_self ⟨cylMass_nonneg _ _, cylMass_le_one _ _⟩]
      _ ≤ |((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ)
            - cylMass ab.2 (wordOdd s)| := abs_clamp_sub_clamp_le _ _
      _ ≤ (2 : ℝ)⁻¹ ^ (n + 2) := hOest
  have hcast : ((ratOfCode (mulCode
      (clampCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))))
      (clampCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)))) : ℚ) : ℝ)
      = max 0 (min 1
          ((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ))
        * max 0 (min 1
          ((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ)) := by
    rw [ratOfCode_mulCode, ratOfCode_clampCode, ratOfCode_clampCode]
    push_cast
    rfl
  have hval : ((cylMass01 (productMeasure ab.1 ab.2) s : ℝ))
      = cylMass ab.1 (wordEven s) * cylMass ab.2 (wordOdd s) :=
    cylMass_productMeasure ab.1 ab.2 s
  calc |((ratOfCode (prodMeasurePost (Nat.pair (Nat.pair (encode s) n)
        (encode (streamTake r (prodMeasureBound (Nat.pair (encode s) n) (r 0)))))) : ℚ) : ℝ)
        - (cylMass01 (productMeasure ab.1 ab.2) s : ℝ)|
      = |max 0 (min 1
            ((ratOfCode (r (2 * Nat.pair (encode (wordEven s)) (n + 2))) : ℚ) : ℝ))
          * max 0 (min 1
            ((ratOfCode (r (2 * Nat.pair (encode (wordOdd s)) (n + 2) + 1)) : ℚ) : ℝ))
          - cylMass ab.1 (wordEven s) * cylMass ab.2 (wordOdd s)| := by
        rw [hpost, hcast, hval]
    _ ≤ 2 * (2 : ℝ)⁻¹ ^ (n + 2) :=
        abs_mul_sub_mul_le (clamp_mem_Icc _)
          ⟨cylMass_nonneg _ _, cylMass_le_one _ _⟩ hclampE hclampO
    _ = (2 : ℝ)⁻¹ ^ (n + 1) := by
        rw [pow_succ]
        ring
    _ ≤ (2 : ℝ)⁻¹ ^ n := halfPow_le_halfPow (Nat.le_succ n)

end ComputableAnalysis
