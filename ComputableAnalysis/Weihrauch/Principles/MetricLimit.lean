/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Principles.Limit
import ComputableAnalysis.Metric.CauchyRepresentation
import ComputableAnalysis.Metric.RatCodeArith
import ComputableAnalysis.TypeTwo.Tracks
import ComputableAnalysis.TypeTwo.Universal
import ComputableAnalysis.ForMathlib.REPredStages

/-!
# Limits in a presented metric space reduce to `Lim`

For a computable metric presentation `P`, the limit of a convergent, not necessarily fast,
sequence of named points is decoded from the `Lim` answer alone. `exists_limitDecoder` gives one
fixed oracle code that, on any accepted answer of `limTable w` whose input tracks name points
`z n` converging to `zlim`, emits a fast Cauchy name of `zlim`. This is the upper half of the
classical fact that the limit operation of a computable metric space reduces strongly to `Lim`.
It is stated at the level of names, so it also serves presentations whose carrier is never used
as a represented space.

No completeness assumption is made: convergence to the limit is a hypothesis.

## Main results

* `exists_limitDecoder` — the answer-only limit decoder.

## Implementation notes

For output coordinate `j` the decoder selects a track `N` satisfying the anchored tail bound
`∀ m ≥ N, dist (z m) (z N) ≤ 2⁻⁽ʲ⁺¹⁾`, which bounds the distance from `z N` to the limit, and
emits coordinate `j + 1` of that track; the two errors sum to `2⁻ʲ`.

Failure of the tail bound is Σ⁰₁ in the names: a witness `(m, k, t)` certifies at stage `t` that
the coordinate-`k` approximants of tracks `m ≥ N` and `N` are more than `2⁻⁽ʲ⁺¹⁾ + 2 · 2⁻ᵏ` apart.
So the jump of `w` decides the bound, and the odd columns of the accepted answer carry that jump
through a diagonal `smn` index. Both oracle reads of the violation test sit at positions computed
from the witness, so the test is an ordinary two-query code. The even half of the answer echoes
`w`, which is where the emitted coordinate is read.
-/

open Encodable Denumerable Filter Topology

namespace ComputableAnalysis

open OracleCode

/-! ### The violation leaf -/

/-- The violation leaf at witness `u = ⟨m, ⟨k, t⟩⟩`, for output precision `j` and candidate
`N`: `m ≥ N`, and the stage-`t` strict certificate
`2⁻⁽ʲ⁺¹⁾ + 2⁻ᵏ + 2⁻ᵏ < dist (dense (track m w k)) (dense (track N w k))` fires. -/
private def tailViol (gt : ℕ × ℕ × RatCode → ℕ → Bool) (w : Baire) (j N u : ℕ) : Bool :=
  if N ≤ u.unpair.1 then
    gt (w (Nat.pair u.unpair.1 u.unpair.2.unpair.1), w (Nat.pair N u.unpair.2.unpair.1),
      stabilityThresholdCode j u.unpair.2.unpair.1) u.unpair.2.unpair.2
  else false

/-- Fields of the leaf input `x = ⟨⟨j, N⟩, ⟨m, ⟨k, t⟩⟩⟩`. -/
private def tvJ (x : ℕ) : ℕ := x.unpair.1.unpair.1
private def tvN (x : ℕ) : ℕ := x.unpair.1.unpair.2
private def tvM (x : ℕ) : ℕ := x.unpair.2.unpair.1
private def tvK (x : ℕ) : ℕ := x.unpair.2.unpair.2.unpair.1
private def tvT (x : ℕ) : ℕ := x.unpair.2.unpair.2.unpair.2

/-- The two read positions: `track m w k` and `track N w k`. -/
private def tvPos₁ (x : ℕ) : ℕ := Nat.pair (tvM x) (tvK x)
private def tvPos₂ (x : ℕ) : ℕ := Nat.pair (tvN x) (tvK x)

/-- The postprocessor on `⟨x, ⟨R₁, R₂⟩⟩`: `0` on a violation. -/
private def tvPost (gt : ℕ × ℕ × RatCode → ℕ → Bool) (y : ℕ) : ℕ :=
  if tvN y.unpair.1 ≤ tvM y.unpair.1 then
    if gt (y.unpair.2.unpair.1, y.unpair.2.unpair.2,
        stabilityThresholdCode (tvJ y.unpair.1) (tvK y.unpair.1)) (tvT y.unpair.1) = true
      then 0 else 1
  else 1

private theorem primrec_tvJ : Primrec tvJ := primrec_unpairFst.comp primrec_unpairFst
private theorem primrec_tvN : Primrec tvN := primrec_unpairSnd.comp primrec_unpairFst
private theorem primrec_tvM : Primrec tvM := primrec_unpairFst.comp primrec_unpairSnd
private theorem primrec_tvK : Primrec tvK :=
  primrec_unpairFst.comp (primrec_unpairSnd.comp primrec_unpairSnd)
private theorem primrec_tvT : Primrec tvT :=
  primrec_unpairSnd.comp (primrec_unpairSnd.comp primrec_unpairSnd)

private theorem primrec_tvPos₁ : Primrec tvPos₁ := Primrec₂.natPair.comp primrec_tvM primrec_tvK
private theorem primrec_tvPos₂ : Primrec tvPos₂ := Primrec₂.natPair.comp primrec_tvN primrec_tvK

private theorem primrec_tvPost {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    Primrec (tvPost gt) := by
  have hx : Primrec fun y : ℕ => y.unpair.1 := primrec_unpairFst
  have hR₁ : Primrec fun y : ℕ => y.unpair.2.unpair.1 := primrec_unpairFst.comp primrec_unpairSnd
  have hR₂ : Primrec fun y : ℕ => y.unpair.2.unpair.2 := primrec_unpairSnd.comp primrec_unpairSnd
  have hthr : Primrec fun y : ℕ =>
      stabilityThresholdCode (tvJ y.unpair.1) (tvK y.unpair.1) :=
    primrec₂_stabilityThresholdCode.comp (primrec_tvJ.comp hx) (primrec_tvK.comp hx)
  have hfire : Primrec fun y : ℕ =>
      gt (y.unpair.2.unpair.1, y.unpair.2.unpair.2,
        stabilityThresholdCode (tvJ y.unpair.1) (tvK y.unpair.1)) (tvT y.unpair.1) :=
    hgt.comp (hR₁.pair (hR₂.pair hthr)) (primrec_tvT.comp hx)
  exact Primrec.ite (PrimrecRel.comp Primrec.nat_le (primrec_tvN.comp hx) (primrec_tvM.comp hx))
    (Primrec.ite (PrimrecRel.comp Primrec.eq hfire (Primrec.const true)) (Primrec.const 0)
      (Primrec.const 1))
    (Primrec.const 1)

private theorem tvPost_value (gt : ℕ × ℕ × RatCode → ℕ → Bool) (w : Baire) (j N u : ℕ) :
    tvPost gt (Nat.pair (Nat.pair (Nat.pair j N) u)
      (Nat.pair (w (tvPos₁ (Nat.pair (Nat.pair j N) u)))
        (w (tvPos₂ (Nat.pair (Nat.pair j N) u)))))
      = if tailViol gt w j N u = true then 0 else 1 := by
  simp only [tvPost, tvPos₁, tvPos₂, tvJ, tvN, tvM, tvK, tvT, Nat.unpair_pair]
  rw [tailViol]
  by_cases h : N ≤ u.unpair.1
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]
    rfl

/-- **The total violation leaf**: two `query` reads at computed positions, then the
postprocessor. -/
private theorem exists_tailViolCode {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    ∃ V : OracleCode, ∀ (w : Baire) (j N u : ℕ),
      V.eval w (Nat.pair (Nat.pair j N) u)
        = Part.some (if tailViol gt w j N u = true then 0 else 1) := by
  obtain ⟨G, hG⟩ := exists_ofNatFnCode (primrec_tvPost hgt).to_comp
  obtain ⟨C₁, hC₁⟩ := exists_ofNatFnCode primrec_tvPos₁.to_comp
  obtain ⟨C₂, hC₂⟩ := exists_ofNatFnCode primrec_tvPos₂.to_comp
  refine ⟨comp G (pair OracleCode.id (pair (comp query C₁) (comp query C₂))),
    fun w j N u => ?_⟩
  rw [eval_comp_some (eval_pair_some (eval_id _ _) (eval_pair_some
    ((eval_comp_some (hC₁ _ _)).trans (eval_query _ _))
    ((eval_comp_some (hC₂ _ _)).trans (eval_query _ _)))), hG, tvPost_value]

/-! ### The diagonal index -/

/-- **The tail index**: one computable `idx j N` whose diagonal jump bit against the name stream
fires exactly on a violation. -/
private theorem exists_tailIndex {gt : ℕ × ℕ × RatCode → ℕ → Bool} (hgt : Primrec₂ gt) :
    ∃ idx : ℕ → ℕ → ℕ, Computable₂ idx ∧
      ∀ (w : Baire) (j N : ℕ),
        (∃ t, jumpBit w (idx j N) t = 1) ↔ ∃ u, tailViol gt w j N u = true := by
  obtain ⟨V, hV⟩ := exists_tailViolCode hgt
  obtain ⟨s, hs, hsmn⟩ := smn
  set base : OracleCode := comp (rfind V) left with hbase
  refine ⟨fun j N => s (encode base) (Nat.pair j N),
    (hs.comp (Computable.const _)
      (Primrec₂.natPair.to_comp.comp Computable.fst Computable.snd)).to₂,
    fun w j N => ?_⟩
  rw [exists_jumpBit_eq_one_iff, hsmn, hbase, eval_comp_some (eval_left _ _), Nat.unpair_pair]
  exact rfind_dom_iff_exists (hV w j N)

/-! ### The semantic boundary of the leaf -/

section Semantics

variable {Z : Type} [MetricSpace Z] {P : ComputableMetricPresentation Z}

/-- **The leaf fires exactly on a genuine tail violation**, given the name contracts. -/
private theorem exists_tailViol_iff {gt : ℕ × ℕ × RatCode → ℕ → Bool}
    (hgt : ∀ a : ℕ × ℕ × RatCode,
      ((ratOfCode a.2.2 : ℚ) : ℝ) < dist (P.dense a.1) (P.dense a.2.1) ↔ ∃ t, gt a t = true)
    {w : Baire} {z : ℕ → Z} (hz : ∀ n, P.NamesPoint (Baire.track n w) (z n)) (j N : ℕ) :
    (∃ u, tailViol gt w j N u = true) ↔
      ∃ m, N ≤ m ∧ (2 : ℝ)⁻¹ ^ (j + 1) < dist (z m) (z N) := by
  have hthr : ∀ k : ℕ, ((ratOfCode (stabilityThresholdCode j k) : ℚ) : ℝ)
      = (2 : ℝ)⁻¹ ^ (j + 1) + ((2 : ℝ)⁻¹ ^ k + (2 : ℝ)⁻¹ ^ k) := by
    intro k
    rw [ratOfCode_stabilityThresholdCode]
    push_cast
    ring
  have happrox : ∀ n k, dist (P.dense (w (Nat.pair n k))) (z n) ≤ (2 : ℝ)⁻¹ ^ k :=
    fun n k => hz n k
  constructor
  · rintro ⟨u, hu⟩
    rw [tailViol] at hu
    by_cases hN : N ≤ u.unpair.1
    · rw [ite_eq_left hN] at hu
      set m := u.unpair.1
      set k := u.unpair.2.unpair.1
      have hlt := (hgt _).mpr ⟨_, hu⟩
      simp only [hthr] at hlt
      refine ⟨m, hN, ?_⟩
      have h1 := happrox m k
      have h2 := happrox N k
      have htri := dist_triangle4 (P.dense (w (Nat.pair m k))) (z m) (z N)
        (P.dense (w (Nat.pair N k)))
      rw [dist_comm (z N)] at htri
      linarith
    · rw [ite_eq_right hN] at hu
      exact absurd hu Bool.false_ne_true
  · rintro ⟨m, hNm, hlt⟩
    set q : ℝ := (2 : ℝ)⁻¹ ^ (j + 1)
    set D : ℝ := dist (z m) (z N)
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by linarith : 0 < (D - q) / 4)
      (by norm_num : (2 : ℝ)⁻¹ < 1)
    have h1 := happrox m k
    have h2 := happrox N k
    have htri := dist_triangle4 (z m) (P.dense (w (Nat.pair m k)))
      (P.dense (w (Nat.pair N k))) (z N)
    rw [dist_comm (z m) (P.dense _)] at htri
    have hcert : ((ratOfCode (stabilityThresholdCode j k) : ℚ) : ℝ)
        < dist (P.dense (w (Nat.pair m k))) (P.dense (w (Nat.pair N k))) := by
      rw [hthr]
      linarith
    obtain ⟨t, ht⟩ := (hgt (w (Nat.pair m k), w (Nat.pair N k),
      stabilityThresholdCode j k)).mp hcert
    refine ⟨Nat.pair m (Nat.pair k t), ?_⟩
    rw [tailViol, Nat.unpair_pair, Nat.unpair_pair, ite_eq_left hNm]
    exact ht

end Semantics

/-! ### The decoder -/

/-- The answer-side search leaf: `0` exactly when the jump column of `idx j N` reads `0`. -/
private def okPost (v : ℕ) : ℕ := if v = 0 then 0 else 1

private theorem primrec_okPost : Primrec okPost :=
  Primrec.ite (PrimrecRel.comp Primrec.eq Primrec.id (Primrec.const 0)) (Primrec.const 0)
    (Primrec.const 1)

/-- The output position: coordinate `j + 1` of track `N`, in the echo half of the answer. -/
private def outPos (y : ℕ) : ℕ := 2 * Nat.pair y.unpair.2 (y.unpair.1 + 1)

private theorem primrec_outPos : Primrec outPos :=
  Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec₂.natPair.comp primrec_unpairSnd (Primrec.succ.comp primrec_unpairFst))

variable {Z : Type} [MetricSpace Z]

/-- **The limit decoder.** From the `Lim` answer alone, one fixed code decodes a fast Cauchy
name of the limit of a convergent sequence of named points. -/
theorem exists_limitDecoder (P : ComputableMetricPresentation Z) :
    ∃ H : OracleCode, ∀ (w a : Baire) (z : ℕ → Z) (zlim : Z),
      (∀ n, P.NamesPoint (Baire.track n w) (z n)) →
      Tendsto z atTop (𝓝 zlim) →
      Lim.accepts (limTable w) a →
      ∃ r ∈ H.evalStream a, P.NamesPoint r zlim := by
  classical
  obtain ⟨gt, hgtprim, hgtiff⟩ := repred_exists_primrec_stages P.gtSemidec
  have hgt : ∀ a : ℕ × ℕ × RatCode,
      ((ratOfCode a.2.2 : ℚ) : ℝ) < dist (P.dense a.1) (P.dense a.2.1) ↔
        ∃ t, gt a t = true := hgtiff
  obtain ⟨idx, hidx, hidxspec⟩ := exists_tailIndex hgtprim
  have hcol : Computable fun x : ℕ => 2 * idx x.unpair.1 x.unpair.2 + 1 :=
    Computable.succ.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2)
      (hidx.comp primrec_unpairFst.to_comp primrec_unpairSnd.to_comp))
  obtain ⟨C₁, hC₁⟩ := exists_ofNatFnCode hcol
  obtain ⟨G, hG⟩ := exists_ofNatFnCode primrec_okPost.to_comp
  obtain ⟨C₂, hC₂⟩ := exists_ofNatFnCode primrec_outPos.to_comp
  set L : OracleCode := comp G (comp query C₁) with hL
  set H : OracleCode := comp query (comp C₂ (pair OracleCode.id (rfind L))) with hH
  refine ⟨H, fun w a z zlim hz hlim hacc => ?_⟩
  -- the search leaf is total, `0` exactly on a quiet jump column
  have hLval : ∀ j N, L.eval a (Nat.pair j N)
      = Part.some (if decide (a (2 * idx j N + 1) = 0) = true then 0 else 1) := by
    intro j N
    rw [hL, eval_comp_some ((eval_comp_some (hC₁ _ _)).trans (eval_query _ _)), hG]
    simp only [okPost, Nat.unpair_pair, decide_eq_true_eq]
  -- a quiet column is exactly the tail bound
  have hquiet : ∀ j N, a (2 * idx j N + 1) = 0 ↔
      ∀ m, N ≤ m → dist (z m) (z N) ≤ (2 : ℝ)⁻¹ ^ (j + 1) := by
    intro j N
    rw [odd_of_lim_accepts_eq_zero hacc, hidxspec, exists_tailViol_iff hgt hz]
    push Not
    rfl
  -- the search halts: convergent sequences are Cauchy
  have hdom : ∀ j, ((rfind L).eval a j).Dom := by
    intro j
    rw [rfind_dom_iff_exists (hLval j)]
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq ((2 : ℝ)⁻¹ ^ (j + 1))
      (by positivity)
    exact ⟨N, decide_eq_true ((hquiet j N).mpr fun m hm => (hN m hm).le)⟩
  set sel : ℕ → ℕ := fun j => ((rfind L).eval a j).get (hdom j) with hsel
  have hselmem : ∀ j, sel j ∈ (rfind L).eval a j := fun j => Part.get_mem _
  have hselok : ∀ j, a (2 * idx j (sel j) + 1) = 0 := fun j =>
    of_decide_eq_true (viol_of_mem_eval_rfind (hLval j) (hselmem j))
  set r : Baire := fun j => a (2 * Nat.pair (sel j) (j + 1)) with hr
  refine ⟨r, mem_evalStream.mpr fun j => ?_, fun j => ?_⟩
  · have hs : (rfind L).eval a j = Part.some (sel j) := Part.eq_some_iff.mpr (hselmem j)
    rw [hH, eval_comp_some ((eval_comp_some (eval_pair_some (eval_id _ _) hs)).trans
      (hC₂ _ _)), eval_query]
    simp only [outPos, Nat.unpair_pair, r]
    exact Part.mem_some _
  · -- the selected track's tail stays within `2⁻⁽ʲ⁺¹⁾`, so does the limit
    set N := sel j
    have htail := (hquiet j N).mp (hselok j)
    have hlimN : dist zlim (z N) ≤ (2 : ℝ)⁻¹ ^ (j + 1) :=
      le_of_tendsto (hlim.dist tendsto_const_nhds)
        (eventually_atTop.mpr ⟨N, fun m hm => htail m hm⟩)
    -- the emitted coordinate is coordinate `j + 1` of track `N`
    have hecho : r j = w (Nat.pair N (j + 1)) := by
      have := congrFun (evenPart_of_lim_accepts hacc) (Nat.pair N (j + 1))
      rwa [Baire.evenPart_apply] at this
    have hname : dist (P.dense (r j)) (z N) ≤ (2 : ℝ)⁻¹ ^ (j + 1) := by
      rw [hecho]
      exact hz N (j + 1)
    calc dist (P.dense (r j)) zlim ≤ dist (P.dense (r j)) (z N) + dist (z N) zlim :=
          dist_triangle _ _ _
      _ ≤ (2 : ℝ)⁻¹ ^ (j + 1) + (2 : ℝ)⁻¹ ^ (j + 1) := by
          rw [dist_comm (z N)]
          exact add_le_add hname hlimN
      _ = (2 : ℝ)⁻¹ ^ j := by
          rw [pow_succ]
          ring

end ComputableAnalysis
