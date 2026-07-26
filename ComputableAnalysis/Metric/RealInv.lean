/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.Real

/-!
# Division away from zero

Reciprocal is a computable map from the represented positive reals to the represented
reals, with **no** modulus datum: positivity is Σ₁ along any fast Cauchy name, so the
realizer searches for its own lower-bound certificate. Per output coordinate `n`:

* **Search** (`OracleCode.rfind`): find the least stage `k` with
  `2·(2⁻¹)^k < ratOfCode (p k)` — a decidable ℕ cross-multiplication comparison on coded
  rationals (`searchVal`). A hit exists on every name of a positive `x` (any `k` with
  `(2⁻¹)^k < x/3` works), and any hit certifies the lower bound
  `x ≥ ratOfCode (p k) - (2⁻¹)^k > (2⁻¹)^k`.
* **Output**: query the name at working precision `m := n + 2k + 1` and emit the coded
  reciprocal (`invRatCode`). The certificate forces `ratOfCode (p m) > (2⁻¹)^(k+1)`, so
  `|q⁻¹ - x⁻¹| = |x - q| / (q·x) ≤ (2⁻¹)^m / ((2⁻¹)^(k+1) · (2⁻¹)^k) = (2⁻¹)^n`.

The search diverges off valid names (e.g. on names of nonpositive reals), so the realizer
is partial — precedented by `Metric/Admissibility.lean` — and the `Realizes` witness is
built directly through `OracleCode.mem_evalStream`, never `Realizes.of_computes`.
Coded-rational helpers come from `Metric/RatCodeArith.lean` and `Metric/Presentation.lean`;
only the names bridge is re-derived privately, since it is `private` in `Metric/Real.lean`.
-/

namespace ComputableAnalysis

open OracleCode

/-! ### Private re-derivation: the names bridge -/

/-- Names of `realRep` are exactly the fast rational approximation streams (private
re-derivation of the `Metric/Real.lean` names bridge). -/
private theorem realRep_names_iff {p : Baire} {x : ℝ} :
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

/-! ### The coded search test and the coded reciprocal -/

/-- The stage-`k` search test on a rational code `m`: `0` exactly when the coded value
exceeds the threshold `2·(2⁻¹)^k` — the decidable ℕ cross-multiplication form of
`2/2^k < (a - b)/(c + 1)` — and `1` otherwise (`rfind`'s search-for-zero convention). -/
private def searchVal (m k : ℕ) : ℕ :=
  if 2 * (m.unpair.2 + 1) + m.unpair.1.unpair.2 * 2 ^ k < m.unpair.1.unpair.1 * 2 ^ k
  then 0 else 1

/-- The search test hits zero exactly at the rational threshold comparison. -/
private theorem searchVal_eq_zero_iff {m k : ℕ} :
    searchVal m k = 0 ↔ 2 * ((2 : ℚ)⁻¹) ^ k < ratOfCode m := by
  have hpk : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  have hq : (2 * (m.unpair.2 + 1) + m.unpair.1.unpair.2 * 2 ^ k
        < m.unpair.1.unpair.1 * 2 ^ k)
      ↔ 2 * ((2 : ℚ)⁻¹) ^ k < ratOfCode m := by
    rw [ratOfCode, inv_pow, ← div_eq_mul_inv, div_lt_div_iff₀ hpk hden, sub_mul,
      lt_sub_iff_add_lt]
    exact_mod_cast Iff.rfl
  rw [searchVal]
  split_ifs with h
  · exact iff_of_true rfl (hq.mp h)
  · exact iff_of_false (by simp) fun hlt => h (hq.mpr hlt)

/-- Powering is primitive recursive (bridge from `Nat.Primrec.pow`). -/
private theorem primrec₂_pow : Primrec₂ (· ^ · : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The packed form of the search test is primitive recursive. -/
private theorem primrec_searchValPost :
    Primrec fun v : ℕ => searchVal v.unpair.1 v.unpair.2 := by
  have ha : Primrec fun v : ℕ => v.unpair.1.unpair.1.unpair.1 :=
    primrec_unpairFst.comp (primrec_unpairFst.comp primrec_unpairFst)
  have hb : Primrec fun v : ℕ => v.unpair.1.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp (primrec_unpairFst.comp primrec_unpairFst)
  have hc : Primrec fun v : ℕ => 2 * (v.unpair.1.unpair.2 + 1) :=
    Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (primrec_unpairSnd.comp primrec_unpairFst))
  have hpow : Primrec fun v : ℕ => 2 ^ v.unpair.2 :=
    primrec₂_pow.comp (Primrec.const 2) primrec_unpairSnd
  exact (Primrec.ite
    (Primrec.nat_lt.comp
      (Primrec.nat_add.comp hc (Primrec.nat_mul.comp hb hpow))
      (Primrec.nat_mul.comp ha hpow))
    (Primrec.const 0) (Primrec.const 1)).of_eq fun v => rfl

/-- Reciprocal on positive rational codes:
`(a - b)/(c + 1) ↦ ((c + 1) - 0)/((a - b - 1) + 1)` when `b < a`, else `zeroCode`
(never hit in the certified regime). -/
private def invRatCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.2 < m.unpair.1.unpair.1 then
    Nat.pair (Nat.pair (m.unpair.2 + 1) 0) (m.unpair.1.unpair.1 - m.unpair.1.unpair.2 - 1)
  else zeroCode

/-- On codes of positive rationals, `invRatCode` decodes to the reciprocal. -/
private theorem ratOfCode_invRatCode {m : ℕ} (h : 0 < ratOfCode m) :
    ratOfCode (invRatCode m) = (ratOfCode m)⁻¹ := by
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  have hba : m.unpair.1.unpair.2 < m.unpair.1.unpair.1 := by
    by_contra hcon
    have hle : (m.unpair.1.unpair.1 : ℚ) ≤ (m.unpair.1.unpair.2 : ℚ) := by
      exact_mod_cast Nat.le_of_not_lt hcon
    have hnp : ratOfCode m ≤ 0 := by
      rw [ratOfCode]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    exact absurd h (not_lt.mpr hnp)
  have hsub : ((m.unpair.1.unpair.1 - m.unpair.1.unpair.2 - 1 : ℕ) : ℚ) + 1
      = (m.unpair.1.unpair.1 : ℚ) - (m.unpair.1.unpair.2 : ℚ) := by
    have hone : m.unpair.1.unpair.1 - m.unpair.1.unpair.2 - 1 + 1
        = m.unpair.1.unpair.1 - m.unpair.1.unpair.2 := by omega
    calc ((m.unpair.1.unpair.1 - m.unpair.1.unpair.2 - 1 : ℕ) : ℚ) + 1
        = ((m.unpair.1.unpair.1 - m.unpair.1.unpair.2 - 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      _ = ((m.unpair.1.unpair.1 - m.unpair.1.unpair.2 : ℕ) : ℚ) := by rw [hone]
      _ = (m.unpair.1.unpair.1 : ℚ) - (m.unpair.1.unpair.2 : ℚ) :=
          Nat.cast_sub hba.le
  rw [invRatCode, if_pos hba]
  simp only [ratOfCode, Nat.unpair_pair]
  rw [hsub, inv_div]
  push_cast
  ring

/-- The coded reciprocal is primitive recursive. -/
private theorem primrec_invRatCode : Primrec invRatCode := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  exact Primrec.ite (Primrec.nat_lt.comp hb ha)
    (Primrec₂.natPair.comp
      (Primrec₂.natPair.comp (Primrec.succ.comp primrec_unpairSnd) (Primrec.const 0))
      (Primrec.nat_sub.comp (Primrec.nat_sub.comp ha hb) (Primrec.const 1)))
    (Primrec.const zeroCode)

/-! ### The realizer -/

/-- **Division away from zero.** Reciprocal is a computable map from the represented
positive reals: an `rfind` search certifies a rational lower bound `(2⁻¹)^k < x` from the
name alone (positivity is Σ₁ — no modulus datum), and coordinate `n` emits the coded
reciprocal of the approximant at working precision `n + 2k + 1`. The realizer diverges on
names of nonpositive reals, so the `Realizes` witness is assembled directly via
`mem_evalStream`. -/
theorem computableMap_realInv_pos :
    ComputableMap (realRep.subtype fun x => 0 < x) realRep fun x => x.1⁻¹ := by
  obtain ⟨svC, hsv⟩ := exists_ofNatFnCode (g := fun v => searchVal v.unpair.1 v.unpair.2)
    primrec_searchValPost.to_comp
  obtain ⟨idxC, hidxC⟩ := exists_ofNatFnCode (g := fun v => v.unpair.1 + 2 * v.unpair.2 + 1)
    (Primrec.succ.comp (Primrec.nat_add.comp primrec_unpairFst
      (Primrec.nat_mul.comp (Primrec.const 2) primrec_unpairSnd))).to_comp
  obtain ⟨invC, hinvC⟩ := exists_ofNatFnCode (g := invRatCode) primrec_invRatCode.to_comp
  refine ⟨.comp (.comp invC (.comp .query idxC))
    (.pair OracleCode.id (OracleCode.rfind
      (.comp svC (.pair (.comp .query .right) .right)))), fun p s hps => ?_⟩
  have hap : ∀ n : ℕ, |((ratOfCode (p n) : ℚ) : ℝ) - s.val| ≤ (2 : ℝ)⁻¹ ^ n :=
    realRep_names_iff.mp (Representation.subtype_names_iff.mp hps)
  have hx : (0 : ℝ) < s.val := s.property
  -- the (total) search-test value along the name
  have hSC : ∀ n k : ℕ,
      (OracleCode.comp svC (.pair (.comp .query .right) .right)).eval p (Nat.pair n k)
        = Part.some (searchVal (p k) k) := by
    intro n k
    have hr : OracleCode.right.eval p (Nat.pair n k) = Part.some k := by
      rw [eval_right, Nat.unpair_pair]
    have h1 : (OracleCode.comp .query .right).eval p (Nat.pair n k) = Part.some (p k) := by
      rw [eval_comp_some hr, eval_query]
    rw [eval_comp_some (eval_pair_some h1 hr), hsv]
    simp only [Nat.unpair_pair]
  -- the search converges: a success stage exists on any name of a positive real
  let pred : ℕ → Bool := fun k => decide (searchVal (p k) k = 0)
  have hpreddef : pred = fun k => decide (searchVal (p k) k = 0) := rfl
  have hrfeq : ∀ n : ℕ,
      (OracleCode.rfind (.comp svC (.pair (.comp .query .right) .right))).eval p n
        = Nat.rfind (pred : ℕ →. Bool) := by
    intro n
    rw [eval_rfind]
    congr 1
    funext k
    rw [hSC n k, PFun.coe_val]
    simp [hpreddef]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by positivity : (0 : ℝ) < s.val / 3)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hpk : pred k = true := by
    simp only [hpreddef, decide_eq_true_eq]
    rw [searchVal_eq_zero_iff]
    have habs := abs_le.mp (hap k)
    have hr : ((2 * (2 : ℚ)⁻¹ ^ k : ℚ) : ℝ) < ((ratOfCode (p k) : ℚ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hr
  obtain ⟨k₀, hk₀, -⟩ := Nat.rfind_min' hpk
  have hrf : ∀ n : ℕ,
      (OracleCode.rfind (.comp svC (.pair (.comp .query .right) .right))).eval p n
        = Part.some k₀ := fun n =>
    Part.eq_some_iff.mpr (by rw [hrfeq n]; exact hk₀)
  -- the certified lower bound at the found stage
  have hlow : (2 : ℝ)⁻¹ ^ k₀ < s.val := by
    have hspec0 := Nat.rfind_spec hk₀
    rw [PFun.coe_val, Part.mem_some_iff] at hspec0
    have hzero : searchVal (p k₀) k₀ = 0 := by
      have h' := hspec0.symm
      simp only [hpreddef, decide_eq_true_eq] at h'
      exact h'
    have hs : 2 * (2 : ℚ)⁻¹ ^ k₀ < ratOfCode (p k₀) := searchVal_eq_zero_iff.mp hzero
    have hsr : ((2 * (2 : ℚ)⁻¹ ^ k₀ : ℚ) : ℝ) < ((ratOfCode (p k₀) : ℚ) : ℝ) := by
      exact_mod_cast hs
    push_cast at hsr
    have habs := abs_le.mp (hap k₀)
    linarith
  -- the output estimate at working precision `n + 2k₀ + 1`
  have key : ∀ n : ℕ,
      |((ratOfCode (invRatCode (p (n + 2 * k₀ + 1))) : ℚ) : ℝ) - s.val⁻¹|
        ≤ (2 : ℝ)⁻¹ ^ n := by
    intro n
    set m := n + 2 * k₀ + 1 with hm
    set q : ℝ := ((ratOfCode (p m) : ℚ) : ℝ) with hqdef
    have hqm : |q - s.val| ≤ (2 : ℝ)⁻¹ ^ m := hap m
    have hpow : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (k₀ + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hqlow : (2 : ℝ)⁻¹ ^ (k₀ + 1) < q := by
      have habs := abs_le.mp hqm
      have hsucc : (2 : ℝ)⁻¹ ^ k₀ = 2 * (2 : ℝ)⁻¹ ^ (k₀ + 1) := by
        rw [pow_succ]
        ring
      linarith
    have hq0 : (0 : ℝ) < q := lt_trans (by positivity) hqlow
    have hqQ : 0 < ratOfCode (p m) := by
      have hq0' := hq0
      rw [hqdef] at hq0'
      exact_mod_cast hq0'
    have hval : ((ratOfCode (invRatCode (p m)) : ℚ) : ℝ) = q⁻¹ := by
      rw [ratOfCode_invRatCode hqQ, Rat.cast_inv]
    have hden : (2 : ℝ)⁻¹ ^ (2 * k₀ + 1) ≤ q * s.val := by
      calc (2 : ℝ)⁻¹ ^ (2 * k₀ + 1) = (2 : ℝ)⁻¹ ^ (k₀ + 1) * (2 : ℝ)⁻¹ ^ k₀ := by
            rw [← pow_add]
            congr 1
            omega
        _ ≤ q * s.val := mul_le_mul hqlow.le hlow.le (by positivity) hq0.le
    rw [hval, inv_sub_inv hq0.ne' hx.ne', abs_div, abs_of_pos (mul_pos hq0 hx),
      div_le_iff₀ (mul_pos hq0 hx)]
    calc |s.val - q|
        ≤ (2 : ℝ)⁻¹ ^ m := by
          rw [abs_sub_comm]
          exact hqm
      _ = (2 : ℝ)⁻¹ ^ n * (2 : ℝ)⁻¹ ^ (2 * k₀ + 1) := by
          rw [← pow_add]
          congr 1
      _ ≤ (2 : ℝ)⁻¹ ^ n * (q * s.val) := mul_le_mul_of_nonneg_left hden (by positivity)
  -- assembly: the full code evaluates coordinatewise to the coded reciprocal
  have hout : ∀ n : ℕ,
      (OracleCode.comp (.comp invC (.comp .query idxC))
        (.pair OracleCode.id (OracleCode.rfind
          (.comp svC (.pair (.comp .query .right) .right))))).eval p n
        = Part.some (invRatCode (p (n + 2 * k₀ + 1))) := by
    intro n
    have h1 := eval_pair_some (eval_id p n) (hrf n)
    have hidx2 : idxC.eval p (Nat.pair n k₀) = Part.some (n + 2 * k₀ + 1) := by
      rw [hidxC]
      simp only [Nat.unpair_pair]
    have h2 : (OracleCode.comp .query idxC).eval p (Nat.pair n k₀)
        = Part.some (p (n + 2 * k₀ + 1)) := by
      rw [eval_comp_some hidx2, eval_query]
    rw [eval_comp_some h1, eval_comp_some h2, hinvC]
  refine ⟨fun n => invRatCode (p (n + 2 * k₀ + 1)),
    mem_evalStream.mpr fun n => ?_, realRep_names_iff.mpr key⟩
  rw [hout n]
  exact Part.mem_some _

end ComputableAnalysis
