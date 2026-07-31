/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecArith
import ComputableAnalysis.ForMathlib.PrimrecContainers
import ComputableAnalysis.Measure.Conditioning
import ComputableAnalysis.Measure.CantorJoint
import ComputableAnalysis.Measure.DiracDecode
import ComputableAnalysis.Weihrauch.Principles.Limit
import ComputableAnalysis.Weihrauch.StrongReduction
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# The calibration lower bound: `Lim ≤sW Disintegrate`

Part C1's lower half. The reduction encodes a `Lim` table into a joint law on
`Cantor × Cantor` whose unique continuous disintegration reads the limit stream off the
accumulation point `0^ω`, so an oracle for continuous disintegration answers `Lim`.

Everything except the headline is private: the calibration construction is a witness, not
an interface.

**The construction.** `unaryEncode` embeds a Baire point as the Cantor point
`1^(q 0) 0 1^(q 1) 0 ⋯`, injectively, with coordinate `k` depending only on `q 0, …, q k`.
`encodingMap` sends the clopen shell of points whose first `true` is at `t` constantly to
the stage-`t` guess, and the accumulation point `0^ω` to the limit's encoding; column
stabilization is exactly what makes it continuous. `calibPoint` bundles the resulting
continuous kernel `δ ∘ encodingMap`, and `calibPoint_accepts` shows it is accepted at the
graph pushforward `calibJoint` of a discrete full-support base.

**The reduction pair.** The preprocessor emits a weak name of the joint law from the `Lim`
input alone: the base measure is atomic on finite-shell points, where the encoding map
reads a guess depending on the input only, so the joint law does not depend on the limit.
The postprocessor evaluates the accepted kernel at a fixed name of `0^ω`, decodes the
resulting Dirac measure through `exists_diracDecodeCode`, and reads the limit off block by
block with `unaryDecode`. Neither half looks at the other's data, which is what makes the
reduction strong.
-/

namespace ComputableAnalysis

open MeasureTheory ProbabilityTheory Encodable Denumerable OracleCode

open scoped PiNatInstances ENNReal

/-! ### Definitional unfolding of `Lim.accepts`

Re-derived here because the copy in `Limit.lean` is private to that file. -/

/-! ### The unary-block embedding `Baire ↪ Cantor` (decode-correctness core) -/

/-- Cumulative block starts: block `n` of `unaryEncode q` occupies positions
`[unaryCum q n, unaryCum q n + q n)`, followed by a `false` separator. -/
private def unaryCum (q : Baire) : ℕ → ℕ
  | 0 => 0
  | n + 1 => unaryCum q n + q n + 1

private theorem unaryCum_succ (q : Baire) (n : ℕ) :
    unaryCum q (n + 1) = unaryCum q n + q n + 1 := rfl

private theorem unaryCum_mono (q : Baire) : Monotone (unaryCum q) :=
  monotone_nat_of_le_succ fun n => by rw [unaryCum_succ]; omega

private theorem le_unaryCum (q : Baire) (n : ℕ) : n ≤ unaryCum q n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => rw [unaryCum_succ]; omega

/-- Agreement of two Baire points below `n` gives equal cumulative block starts. -/
private theorem unaryCum_eq_of_agree {q q' : Baire} {n : ℕ} (h : ∀ i, i < n → q i = q' i) :
    unaryCum q n = unaryCum q' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unaryCum_succ, unaryCum_succ, ih fun i hi => h i (by omega), h n (by omega)]

/-- The unary-block encoding of a Baire point as a Cantor point:
`1^(q 0) 0 1^(q 1) 0 ⋯`. -/
private def unaryEncode (q : Baire) : Cantor := fun k =>
  (List.range (k + 1)).any fun n =>
    decide (unaryCum q n ≤ k ∧ k < unaryCum q n + q n)

private theorem unaryEncode_eq_true_iff {q : Baire} {k : ℕ} :
    unaryEncode q k = true ↔ ∃ n, unaryCum q n ≤ k ∧ k < unaryCum q n + q n := by
  unfold unaryEncode
  rw [List.any_eq_true]
  constructor
  · rintro ⟨n, -, hn⟩
    exact ⟨n, of_decide_eq_true hn⟩
  · rintro ⟨n, hn⟩
    have hle := le_unaryCum q n
    exact ⟨n, List.mem_range.mpr (by omega), decide_eq_true hn⟩

/-- Coordinate `k` of `unaryEncode q` depends only on `q 0, …, q k`: the witnessing block
index `n` satisfies `n ≤ k` because `n ≤ unaryCum q n ≤ k`. -/
private theorem unaryEncode_apply_eq_of_agree {q q' : Baire} {k : ℕ} (h : ∀ i, i ≤ k → q i = q' i) :
    unaryEncode q k = unaryEncode q' k := by
  have key : ∀ v v' : Baire, (∀ i, i ≤ k → v i = v' i) →
      unaryEncode v k = true → unaryEncode v' k = true := by
    intro v v' hvv hk
    obtain ⟨n, h1, h2⟩ := unaryEncode_eq_true_iff.mp hk
    have hnk : n ≤ k := le_trans (le_unaryCum v n) h1
    have hcum : unaryCum v n = unaryCum v' n :=
      unaryCum_eq_of_agree fun i hi => hvv i (by omega)
    refine unaryEncode_eq_true_iff.mpr ⟨n, hcum ▸ h1, ?_⟩
    rw [← hcum, ← hvv n hnk]
    exact h2
  rcases Bool.eq_false_or_eq_true (unaryEncode q k) with hq | hq
  · rw [hq, key q q' h hq]
  · rcases Bool.eq_false_or_eq_true (unaryEncode q' k) with hq' | hq'
    · rw [key q' q (fun i hi => (h i hi).symm) hq'] at hq
      exact absurd hq (by simp)
    · rw [hq, hq']

/-- Positions inside block `n` are `true`. -/
private theorem unaryEncode_apply_mem (q : Baire) (n j : ℕ) (hj : j < q n) :
    unaryEncode q (unaryCum q n + j) = true :=
  unaryEncode_eq_true_iff.mpr ⟨n, by omega, by omega⟩

/-- The separator after block `n` is `false`. -/
private theorem unaryEncode_apply_sep (q : Baire) (n : ℕ) :
    unaryEncode q (unaryCum q n + q n) = false := by
  refine Bool.eq_false_iff.mpr fun h => ?_
  obtain ⟨m, h1, h2⟩ := unaryEncode_eq_true_iff.mp h
  rcases lt_trichotomy m n with hm | rfl | hm
  · have hcum := unaryCum_mono q (show m + 1 ≤ n by omega)
    rw [unaryCum_succ] at hcum
    omega
  · omega
  · have hcum := unaryCum_mono q (show n + 1 ≤ m by omega)
    rw [unaryCum_succ] at hcum
    omega

/-- Blocks are read off uniquely: the embedding is injective, so the block-scanning
decoder is correct. -/
private theorem unaryEncode_injective : Function.Injective unaryEncode := by
  intro q q' h
  have blocks : ∀ n, unaryCum q n = unaryCum q' n → q n = q' n := by
    intro n hc
    rcases lt_trichotomy (q n) (q' n) with hlt | heq | hgt
    · have h1 := unaryEncode_apply_sep q n
      have h2 := unaryEncode_apply_mem q' n (q n) hlt
      have hk := congrFun h (unaryCum q n + q n)
      rw [h1, hc, h2] at hk
      exact absurd hk (by simp)
    · exact heq
    · have h1 := unaryEncode_apply_sep q' n
      have h2 := unaryEncode_apply_mem q n (q' n) hgt
      have hk := congrFun h (unaryCum q n + q' n)
      rw [h2, hc, h1] at hk
      exact absurd hk (by simp)
  have key : ∀ n, unaryCum q n = unaryCum q' n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [unaryCum_succ, unaryCum_succ, ih, blocks n ih]
  funext n
  exact blocks n (key n)

/-! ### The encoding map -/

open Classical in
/-- The shell-encoding map: the shell `{x | first true at t}` goes constantly to the
stage-`t` unary guess; the accumulation point `0^ω` to the limit's encoding. -/
private noncomputable def encodingMap (p q : Baire) : Cantor → Cantor := fun x =>
  if h : ∃ t, x t = true then unaryEncode fun n => p (Nat.pair n (Nat.find h))
  else unaryEncode q

/-- At the accumulation point the encoding map reads the limit stream. -/
private theorem encodingMap_allFalse (p q : Baire) :
    encodingMap p q (fun _ => false) = unaryEncode q := by
  unfold encodingMap
  exact dif_neg (by simp)

/-- On a shell point (`Nat.find h` its first `true`), the encoding map reads the
corresponding stage guess. -/
private theorem encodingMap_of_true (p q : Baire) {x : Cantor} (h : ∃ t, x t = true) :
    encodingMap p q x = unaryEncode fun n => p (Nat.pair n (Nat.find h)) := by
  unfold encodingMap
  rw [dif_pos h]

/-- **KEY LEMMA 1**: continuity of the encoding map. Away from `0^ω` the map is locally
constant on each clopen shell; at `0^ω` column stabilization (`hLim`) forces convergence,
because coordinate `k` of a unary guess depends only on argument coordinates `0, …, k`. -/
private theorem continuous_encodingMap (p q : Baire) (hLim : Lim.accepts p q) :
    Continuous (encodingMap p q) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨L, hL⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  -- It suffices to make `encodingMap p q y` agree with `encodingMap p q x` on `0, …, L`.
  suffices hsuff : ∃ δ > 0, ∀ y : Cantor, dist y x < δ →
      ∀ i, i ≤ L → encodingMap p q y i = encodingMap p q x i by
    obtain ⟨δ, hδ, hδy⟩ := hsuff
    refine ⟨δ, hδ, fun y hy => ?_⟩
    have hmem : encodingMap p q y ∈ PiNat.cylinder (encodingMap p q x) (L + 1) := fun i hi =>
      hδy y hy i (by omega)
    calc dist (encodingMap p q y) (encodingMap p q x)
        ≤ (1 / 2 : ℝ) ^ (L + 1) := PiNat.mem_cylinder_iff_dist_le.mp hmem
      _ ≤ (1 / 2 : ℝ) ^ L := by
          rw [pow_succ]
          nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) L]
      _ < ε := hL
  by_cases hx : ∃ t, x t = true
  · -- `x` is in the shell of `t₀ = Nat.find hx`; nearby points share that shell.
    refine ⟨(1 / 2 : ℝ) ^ (Nat.find hx), by positivity, fun y hy _ _ => ?_⟩
    have ht0 : x (Nat.find hx) = true := Nat.find_spec hx
    have hbelow : ∀ i, i < Nat.find hx → x i = false := fun i hi => by
      have := Nat.find_min hx hi
      simpa using this
    have hagree : ∀ i, i ≤ Nat.find hx → y i = x i := fun i hi =>
      PiNat.apply_eq_of_dist_lt hy hi
    have hy0 : ∃ t, y t = true := ⟨Nat.find hx, by rw [hagree _ le_rfl]; exact ht0⟩
    have hfind : Nat.find hy0 = Nat.find hx := by
      refine le_antisymm (Nat.find_le (by rw [hagree _ le_rfl]; exact ht0)) ?_
      refine Nat.le_find_iff hy0 (Nat.find hx) |>.mpr fun i hi => ?_
      rw [hagree i (le_of_lt hi)]
      simpa using hbelow i hi
    rw [encodingMap_of_true p q hx, encodingMap_of_true p q hy0, hfind]
  · -- `x = 0^ω`; column stabilization pins the image on `0, …, L`.
    push Not at hx
    have hxfalse : ∀ i, x i = false := fun i => by
      simpa using hx i
    -- stage past which every column `n ≤ L` has stabilized
    choose s hs using fun n => Lim.accepts_iff.mp hLim n
    set S : ℕ := (Finset.range (L + 1)).sup s with hS_def
    refine ⟨(1 / 2 : ℝ) ^ S, by positivity, fun y hy i hiL => ?_⟩
    have hxi : encodingMap p q x i = unaryEncode q i := by
      rw [show x = (fun _ => false) from funext hxfalse, encodingMap_allFalse]
    rw [hxi]
    by_cases hy0 : ∃ t, y t = true
    · -- `y` has first `true` at some `t₀ > S`, so its guess agrees with `q` below `L`.
      rw [encodingMap_of_true p q hy0]
      set t₀ : ℕ := Nat.find hy0 with ht0_def
      have hbelowS : ∀ j, j ≤ S → y j = false := by
        intro j hj
        have := PiNat.apply_eq_of_dist_lt hy hj
        rw [this]
        exact hxfalse j
      have hSt0 : S < t₀ := by
        by_contra hle
        push Not at hle
        have := Nat.find_spec hy0
        rw [hbelowS t₀ hle] at this
        exact Bool.noConfusion this
      refine unaryEncode_apply_eq_of_agree fun n hni => ?_
      have hnL : n ≤ L := le_trans hni hiL
      have hsn : s n ≤ t₀ := by
        have : s n ≤ S := Finset.le_sup (Finset.mem_range.mpr (by omega))
        omega
      exact hs n t₀ hsn
    · push Not at hy0
      rw [show y = (fun _ => false) from funext fun j => by simpa using hy0 j,
        encodingMap_allFalse]

/-! ### The continuous disintegration kernel `δ ∘ encodingMap` -/

/-- The continuous Markov kernel `x ↦ δ_(encodingMap p q x)`: weak continuity from KEY
LEMMA 1 composed with continuity of the Dirac embedding (`continuous_diracProba`), and
Giry measurability from `Measure.measurable_dirac`. -/
private noncomputable def calibKernel (p q : Baire) (hLim : Lim.accepts p q) :
    ContinuousMarkovKernel Cantor Cantor where
  law x := diracProba (encodingMap p q x)
  continuous_law := continuous_diracProba.comp (continuous_encodingMap p q hLim)
  measurable_toMeasure := by
    change Measurable fun x => Measure.dirac (encodingMap p q x)
    exact Measure.measurable_dirac.comp (continuous_encodingMap p q hLim).measurable

/-- The continuous-kernel point of the calibration reduction: the carrier form of
`calibKernel` (definitionally `continuousKernelEquiv.symm (calibKernel …)`, unfolded so the
law is available by reflection). -/
private noncomputable def calibPoint (p q : Baire) (hLim : Lim.accepts p q) :
    ContinuousKernelPoint cantorPresentation cantorPresentation :=
  ⟨(calibKernel p q hLim).toRealizableFun cantorPresentation cantorPresentation,
    (calibKernel p q hLim).continuous_law, (calibKernel p q hLim).measurable_toMeasure⟩

/-- The law of `calibPoint` at `x` is the Dirac mass at `encodingMap p q x`. -/
private theorem calibPoint_toMeasure (p q : Baire) (hLim : Lim.accepts p q) (x : Cantor) :
    ((calibPoint p q hLim).val.toFun x).toMeasure = Measure.dirac (encodingMap p q x) := rfl

/-! ### The joint law and the accepted disintegration -/

/-- The joint law of the calibration reduction over a base measure: the graph pushforward
of `base` under `x ↦ (x, encodingMap p q x)`. -/
private noncomputable def calibJoint (p q : Baire) (base : ProbabilityMeasure Cantor)
    (hLim : Lim.accepts p q) : ProbabilityMeasure (Cantor × Cantor) :=
  ⟨base.toMeasure.map fun x => (x, encodingMap p q x),
    Measure.isProbabilityMeasure_map
      (measurable_id.prodMk (continuous_encodingMap p q hLim).measurable).aemeasurable⟩

/-- The first marginal of the calibration joint law is the base measure (graph then
`fst` is the identity pushforward). -/
private theorem calibJoint_fst (p q : Baire) (base : ProbabilityMeasure Cantor)
    (hLim : Lim.accepts p q) :
    (calibJoint p q base hLim).toMeasure.fst = base.toMeasure := by
  change (base.toMeasure.map fun x => (x, encodingMap p q x)).fst = base.toMeasure
  rw [Measure.fst_map_prodMk (continuous_encodingMap p q hLim).measurable]
  exact Measure.map_id

/-- The induced kernel of `calibPoint` is the deterministic kernel of `encodingMap`. -/
private theorem inducedKernel_calibPoint (p q : Baire) (hLim : Lim.accepts p q) :
    inducedKernel (calibPoint p q hLim)
      = Kernel.deterministic (encodingMap p q) (continuous_encodingMap p q hLim).measurable := by
  ext x : 1
  rw [inducedKernel_apply, calibPoint_toMeasure,
    Kernel.deterministic_apply (continuous_encodingMap p q hLim).measurable]

/-- **KEY LEMMA 2**: the calibration kernel point is `Disintegrate`-accepted at the
calibration joint law over any full-support base. Full first-marginal support comes from
`calibJoint_fst`; the version identity is `compProd_deterministic` on the graph
pushforward. -/
private theorem calibPoint_accepts (p q : Baire) (base : ProbabilityMeasure Cantor)
    (hLim : Lim.accepts p q) (hbase : base.toMeasure.support = Set.univ) :
    (Disintegrate cantorPresentation cantorPresentation).accepts
      (calibJoint p q base hLim) (calibPoint p q hLim) := by
  have hg : Measurable (encodingMap p q) := (continuous_encodingMap p q hLim).measurable
  refine ⟨?_, inferInstance, ⟨?_⟩⟩
  · change (calibJoint p q base hLim).toMeasure.fst.support = Set.univ
    rw [calibJoint_fst, hbase]
  · rw [calibJoint_fst, inducedKernel_calibPoint, Measure.compProd_deterministic hg]
    rfl

/-! ### The discrete full-support base measure

A discrete atomic probability measure whose atoms are finite-shell dense points. Because
`encodingMap p q` reads a `p`-only guess at every finite-shell point, the calibration
joint over this base is a *fixed* measure computable from `p` alone (independent of the
limit `q`). Full support because the atoms are dense. REUSABLE: a candidate prerequisite
unit (discrete full-support Cantor measure with a computable weak name). -/

/-- The `i`-th base atom: the dense point of the `false`-extended word with a forced
trailing `true`, giving a first `true` at the word's length. -/
private noncomputable def baseAtom (i : ℕ) : Cantor := wordPoint (denseWord i ++ [true])

/-- Each base atom is a dense point of the Cantor presentation (at a computable index). -/
private theorem baseAtom_eq_densePoint (i : ℕ) :
    baseAtom i = densePoint (encode (denseWord i ++ [true])) := by
  rw [baseAtom, densePoint, denseWord_encode]

/-- The geometric mixture `∑ 2^{-(i+1)} δ_{baseAtom i}` as a raw measure. -/
private noncomputable def baseMeasureM : Measure Cantor :=
  Measure.sum fun i => (2 : ℝ≥0∞)⁻¹ ^ (i + 1) • Measure.dirac (baseAtom i)

/-- The geometric tail sums to `1`. -/
private theorem tsum_ehalf_one : ∑' k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (k + 1) = 1 := by
  rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

private instance : IsProbabilityMeasure baseMeasureM := by
  constructor
  rw [baseMeasureM, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact tsum_ehalf_one

/-- The discrete full-support base measure of the calibration reduction. -/
private noncomputable def calibBase : ProbabilityMeasure Cantor := ⟨baseMeasureM, inferInstance⟩

/-- Openness-positivity of the base measure: every nonempty open set contains a base atom
(density), which carries positive geometric weight. -/
private theorem isOpenPosMeasure_baseMeasureM : baseMeasureM.IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  set i := encode (streamTake x n) with hi
  have hmemcyl : baseAtom i ∈ PiNat.cylinder x n := by
    intro j hj
    rw [baseAtom, hi, denseWord_encode, wordPoint_apply,
      List.getD_eq_getElem _ _ (by simp only [List.length_append, length_streamTake,
        List.length_cons, List.length_nil]; omega),
      List.getElem_append_left (by rw [length_streamTake]; exact hj), getElem_streamTake]
  have hdist : dist (baseAtom i) x ≤ (1 / 2 : ℝ) ^ n :=
    PiNat.mem_cylinder_iff_dist_le.mp hmemcyl
  have hmemU : baseAtom i ∈ U := hball (Metric.mem_ball.mpr (lt_of_le_of_lt hdist hn))
  refine fun h0 => ?_
  have hle : (2 : ℝ≥0∞)⁻¹ ^ (i + 1) ≤ baseMeasureM U := by
    rw [baseMeasureM, Measure.sum_apply _ hU.measurableSet]
    calc (2 : ℝ≥0∞)⁻¹ ^ (i + 1)
        = ((2 : ℝ≥0∞)⁻¹ ^ (i + 1) • Measure.dirac (baseAtom i)) U := by
          rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem hmemU, mul_one]
      _ ≤ ∑' j, ((2 : ℝ≥0∞)⁻¹ ^ (j + 1) • Measure.dirac (baseAtom j)) U := ENNReal.le_tsum i
  rw [h0, le_zero_iff] at hle
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by norm_num)) hle

/-- **Full support of the base measure**: openness-positivity plus `support_eq_univ`. -/
private theorem calibBase_support : calibBase.toMeasure.support = Set.univ := by
  haveI := isOpenPosMeasure_baseMeasureM
  change baseMeasureM.support = Set.univ
  exact Measure.support_eq_univ

/-! ### The block-scanning unary decoder (inverse of `unaryEncode` on its range) -/

open Classical in
/-- The length of the maximal run of `true`s of `z` starting at position `k` (`0` when `z`
is `true` from `k` on, which never happens on the range of `unaryEncode`). -/
private noncomputable def runLength (z : Cantor) (k : ℕ) : ℕ :=
  if h : ∃ j, z (k + j) = false then Nat.find h else 0

/-- Decoded cumulative block starts. -/
private noncomputable def decCum (z : Cantor) : ℕ → ℕ
  | 0 => 0
  | n + 1 => decCum z n + runLength z (decCum z n) + 1

/-- **The unary decoder**: `unaryDecode z n` is the length of the `n`-th run of `true`s of
`z`, delimited by `false` separators. -/
private noncomputable def unaryDecode (z : Cantor) (n : ℕ) : ℕ := runLength z (decCum z n)

/-- On the range of `unaryEncode`, `runLength` at a block start reads the block length. -/
private theorem runLength_unaryEncode (q : Baire) (n : ℕ) :
    runLength (unaryEncode q) (unaryCum q n) = q n := by
  have hex : ∃ j, unaryEncode q (unaryCum q n + j) = false :=
    ⟨q n, unaryEncode_apply_sep q n⟩
  rw [runLength, dif_pos hex]
  refine le_antisymm (Nat.find_le (unaryEncode_apply_sep q n)) ?_
  refine (Nat.le_find_iff hex _).mpr fun j hj => ?_
  rw [unaryEncode_apply_mem q n j hj]
  simp

private theorem decCum_unaryEncode (q : Baire) (n : ℕ) :
    decCum (unaryEncode q) n = unaryCum q n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [decCum, ih, runLength_unaryEncode q n, unaryCum_succ]

/-- **Decode-correctness**: `unaryDecode` inverts `unaryEncode`. -/
private theorem unaryDecode_unaryEncode (q : Baire) : unaryDecode (unaryEncode q) = q := by
  funext n
  rw [unaryDecode, decCum_unaryEncode, runLength_unaryEncode q n]

/-! ### The joint law is atomic, and does not depend on the limit

Each base atom lies on a finite shell, where the encoding map reads a guess assembled from
the input alone. So the joint law is a fixed geometric mixture of point masses that the
limit never enters — which is what lets the preprocessor emit a name for it. -/

/-- The word of the `i`-th base atom, ending in its forced `true`. -/
private def baseWord (i : ℕ) : List Bool := denseWord i ++ [true]

private theorem baseAtom_eq_wordPoint (i : ℕ) : baseAtom i = wordPoint (baseWord i) := rfl

/-- The position of the first `true` in the `i`-th base atom: the shell it lies on. -/
private def shellIdx (i : ℕ) : ℕ := (baseWord i).findIdx (fun b => b)

private theorem shellIdx_lt_length (i : ℕ) : shellIdx i < (baseWord i).length :=
  List.findIdx_lt_length_of_exists ⟨true, by simp [baseWord], rfl⟩

private theorem baseAtom_shellIdx (i : ℕ) : baseAtom i (shellIdx i) = true := by
  rw [baseAtom_eq_wordPoint, wordPoint_apply, List.getD_eq_getElem _ _ (shellIdx_lt_length i)]
  exact List.findIdx_getElem (w := shellIdx_lt_length i)

private theorem baseAtom_of_lt_shellIdx {i j : ℕ} (hj : j < shellIdx i) :
    baseAtom i j = false := by
  have hj' : j < (baseWord i).findIdx (fun b => b) := hj
  obtain ⟨hlen, hall⟩ := (List.lt_findIdx_iff _ _ _).mp hj'
  rw [baseAtom_eq_wordPoint, wordPoint_apply, List.getD_eq_getElem _ _ hlen]
  exact hall j le_rfl

private theorem baseAtom_exists_true (i : ℕ) : ∃ t, baseAtom i t = true :=
  ⟨shellIdx i, baseAtom_shellIdx i⟩

private theorem find_baseAtom (i : ℕ) : Nat.find (baseAtom_exists_true i) = shellIdx i :=
  le_antisymm (Nat.find_le (baseAtom_shellIdx i))
    ((Nat.le_find_iff _ _).mpr fun j hj => by rw [baseAtom_of_lt_shellIdx hj]; simp)

/-- The guess the encoding map reads at the `i`-th base atom — a function of the input
alone, with the limit nowhere in it. -/
private def atomGuess (p : Baire) (i : ℕ) : Baire := fun m => p (Nat.pair m (shellIdx i))

private theorem encodingMap_baseAtom (p q : Baire) (i : ℕ) :
    encodingMap p q (baseAtom i) = unaryEncode (atomGuess p i) := by
  rw [encodingMap_of_true p q (baseAtom_exists_true i), find_baseAtom]
  rfl

/-- The `i`-th atom of the joint law, as a single Cantor point along the interleaving
identification: the base atom on the even track, its encoded guess on the odd track. -/
private noncomputable def atomPoint (p : Baire) (i : ℕ) : Cantor :=
  Cantor.interleave (baseAtom i) (unaryEncode (atomGuess p i))

private theorem deinterleave_atomPoint (p q : Baire) (i : ℕ) :
    cantorDeinterleave (atomPoint p i) = (baseAtom i, encodingMap p q (baseAtom i)) := by
  rw [atomPoint, cantorDeinterleave_interleave, encodingMap_baseAtom]

/-- The geometric mixture of the atoms, as a raw measure. -/
private noncomputable def calibNuM (p : Baire) : Measure Cantor :=
  Measure.sum fun i => (2 : ℝ≥0∞)⁻¹ ^ (i + 1) • Measure.dirac (atomPoint p i)

private instance (p : Baire) : IsProbabilityMeasure (calibNuM p) := by
  constructor
  rw [calibNuM, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact tsum_ehalf_one

/-- The single Cantor measure whose joint law along the interleaving identification is the
calibration joint law. -/
private noncomputable def calibNu (p : Baire) : ProbabilityMeasure Cantor :=
  ⟨calibNuM p, inferInstance⟩

/-- **The joint law is the interleaving image of an atomic Cantor measure.** Both sides are
geometric mixtures over the same index, and deinterleaving the `i`-th atom returns exactly
the graph point of the `i`-th base atom. -/
private theorem jointOfCantor_calibNu (p q : Baire) (hLim : Lim.accepts p q) :
    jointOfCantor (calibNu p) = calibJoint p q calibBase hLim := by
  have hgraph : Measurable fun x : Cantor => (x, encodingMap p q x) :=
    measurable_id.prodMk (continuous_encodingMap p q hLim).measurable
  refine ProbabilityMeasure.toMeasure_injective (Measure.ext fun s hs => ?_)
  rw [toMeasure_jointOfCantor, Measure.map_apply measurable_cantorDeinterleave hs]
  change calibNuM p _ = (baseMeasureM.map fun x => (x, encodingMap p q x)) s
  rw [Measure.map_apply hgraph hs, calibNuM, baseMeasureM,
    Measure.sum_apply _ (measurable_cantorDeinterleave hs), Measure.sum_apply _ (hgraph hs)]
  refine tsum_congr fun i => ?_
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    Measure.dirac_apply' _ (measurable_cantorDeinterleave hs),
    Measure.dirac_apply' _ (hgraph hs)]
  have hmem : atomPoint p i ∈ cantorDeinterleave ⁻¹' s ↔
      baseAtom i ∈ (fun x : Cantor => (x, encodingMap p q x)) ⁻¹' s := by
    simp only [Set.mem_preimage, deinterleave_atomPoint p q i]
  by_cases h : atomPoint p i ∈ cantorDeinterleave ⁻¹' s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mp h)]
    simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem fun hc => h (hmem.mpr hc)]

/-! ### Reading the atoms off a finite prefix of the input

At precision `n` only the atoms `i < n` are inspected, and each of those reads the input at
finitely many places determined by the cylinder word and `n`. These are the prefix forms of
the atom coordinates, together with the agreement lemmas that identify them with the real
thing once the prefix is long enough. -/

private theorem listSum_range_map {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

/-- Cumulative block starts in closed form. -/
private theorem unaryCum_eq_sum (g : Baire) (n : ℕ) :
    unaryCum g n = n + ∑ m ∈ Finset.range n, g m := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unaryCum_succ, ih, Finset.sum_range_succ]; omega

/-- The stage-`m` guess of atom `i`, read off a prefix of the input. -/
private def guessL (L : List ℕ) (i m : ℕ) : ℕ := L.getD (Nat.pair m (shellIdx i)) 0

/-- Cumulative block starts of atom `i`'s guess, from a prefix. -/
private def cumL (L : List ℕ) (i n : ℕ) : ℕ := n + ((List.range n).map (guessL L i)).sum

/-- Coordinate `j` of the encoded guess of atom `i`, from a prefix. -/
private def encL (L : List ℕ) (i j : ℕ) : Bool :=
  (List.range (j + 1)).any fun n => decide (cumL L i n ≤ j ∧ j < cumL L i n + guessL L i n)

/-- Coordinate `k` of atom `i`, from a prefix: the base word on the even track, the encoded
guess on the odd track. -/
private def atomL (L : List ℕ) (i k : ℕ) : Bool :=
  if k % 2 = 0 then (baseWord i).getD (k / 2) false else encL L i (k / 2)

/-- Whether atom `i` lies in the cylinder of `w`, from a prefix. -/
private def memCylL (L : List ℕ) (i : ℕ) (w : List Bool) : Bool :=
  (List.range w.length).all fun k => atomL L i k == w.getD k false

private theorem any_congr_mem {f g : ℕ → Bool} :
    ∀ {l : List ℕ}, (∀ n ∈ l, f n = g n) → l.any f = l.any g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
        any_congr_mem fun c hc => h c (List.mem_cons_of_mem _ hc)]

private theorem all_congr_mem {f g : ℕ → Bool} :
    ∀ {l : List ℕ}, (∀ n ∈ l, f n = g n) → l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
      rw [List.all_cons, List.all_cons, h a List.mem_cons_self,
        all_congr_mem fun c hc => h c (List.mem_cons_of_mem _ hc)]

private theorem cumL_eq {L : List ℕ} {p : Baire} {i j : ℕ}
    (hL : ∀ m, m ≤ j → guessL L i m = atomGuess p i m) {n : ℕ} (hn : n ≤ j) :
    cumL L i n = unaryCum (atomGuess p i) n := by
  rw [cumL, unaryCum_eq_sum, listSum_range_map]
  congr 1
  exact Finset.sum_congr rfl fun m hm =>
    hL m (le_trans (le_of_lt (Finset.mem_range.mp hm)) hn)

private theorem encL_eq {L : List ℕ} {p : Baire} {i j : ℕ}
    (hL : ∀ m, m ≤ j → guessL L i m = atomGuess p i m) :
    encL L i j = unaryEncode (atomGuess p i) j := by
  rw [encL, unaryEncode]
  refine any_congr_mem fun n hn => ?_
  have hnj : n ≤ j := Nat.lt_succ_iff.mp (List.mem_range.mp hn)
  rw [cumL_eq hL hnj, hL n hnj]

private theorem atomL_eq {L : List ℕ} {p : Baire} {i k : ℕ}
    (hL : ∀ m, m ≤ k → guessL L i m = atomGuess p i m) :
    atomL L i k = atomPoint p i k := by
  rw [atomL, atomPoint, Cantor.interleave]
  by_cases hk : k % 2 = 0
  · rw [if_pos hk, if_pos hk, baseAtom_eq_wordPoint, wordPoint_apply]
  · rw [if_neg hk, if_neg hk]
    exact encL_eq fun m hm => hL m (le_trans hm (Nat.div_le_self k 2))

private theorem memCylL_eq {L : List ℕ} {p : Baire} {i : ℕ} {w : List Bool}
    (hL : ∀ m, m ≤ w.length → guessL L i m = atomGuess p i m) :
    memCylL L i w = true ↔ atomPoint p i ∈ (cylinder w : Set Cantor) := by
  have hstep : ∀ k ∈ List.range w.length,
      (atomL L i k == w.getD k false) = (decide (atomPoint p i k = w.getD k false)) := by
    intro k hk
    rw [atomL_eq fun m hm => hL m (le_trans hm (le_of_lt (List.mem_range.mp hk)))]
    cases atomPoint p i k <;> cases w.getD k false <;> simp
  rw [memCylL, all_congr_mem hstep, List.all_eq_true]
  constructor
  · intro h k hk
    have := of_decide_eq_true (h k (List.mem_range.mpr hk))
    rwa [List.getD_eq_getElem _ _ hk] at this
  · intro h k hk
    have hk' := List.mem_range.mp hk
    rw [decide_eq_true_iff, List.getD_eq_getElem _ _ hk']
    exact h k hk'

/-! ### The oracle use bound

At precision `n` the mass of the cylinder of `w` inspects atoms `i < n`, and atom `i` reads
the input only at `Nat.pair m (shellIdx i)` for `m ≤ w.length`. That is a finite set of
places determined by `w` and `n` alone. -/

private theorem le_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | [], _, h => absurd h (by simp)
  | a :: l, x, h => by
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact le_trans (le_foldr_max h') (le_max_right _ _)

/-- The prefix of the input that the level-`n` mass of the cylinder of `w` reads. -/
private def useBound (w : List Bool) (n : ℕ) : ℕ :=
  ((List.range n).flatMap fun i =>
    (List.range (w.length + 1)).map fun m => Nat.pair m (shellIdx i) + 1).foldr max 0

private theorem lt_useBound {w : List Bool} {n i m : ℕ} (hi : i < n) (hm : m ≤ w.length) :
    Nat.pair m (shellIdx i) < useBound w n := by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_foldr_max ?_)
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi,
    List.mem_map.mpr ⟨m, List.mem_range.mpr (by omega), rfl⟩⟩

private theorem guessL_streamTake {p : Baire} {w : List Bool} {n i : ℕ} (hi : i < n)
    {m : ℕ} (hm : m ≤ w.length) :
    guessL (streamTake p (useBound w n)) i m = atomGuess p i m := by
  rw [guessL, streamTake_getD p (lt_useBound hi hm), atomGuess]

/-! ### The exact cylinder-mass approximation

The mass of a cylinder under the atomic measure is a geometric series whose `i`-th term is
either `2^-(i+1)` or `0`. Keeping the atoms `i < n` leaves a tail bounded by exactly `2^-n`,
and the retained part is a dyadic multiple of `2^-n`. -/

private theorem tsum_split (f : ℕ → ℝ≥0∞) (n : ℕ) :
    ∑' i, f i = (∑ i ∈ Finset.range n, f i) + ∑' i, f (i + n) := by
  have hpt : ∀ i, f i = (if i < n then f i else 0) + (if i < n then 0 else f i) := by
    intro i; by_cases h : i < n <;> simp [h]
  have hsupp : Function.support (fun i => if i < n then (0 : ℝ≥0∞) else f i) ⊆
      Set.range (fun j : ℕ => j + n) := by
    intro i hi
    by_cases h : i < n
    · exact absurd (by simp [h] : (if i < n then (0 : ℝ≥0∞) else f i) = 0) hi
    · exact ⟨i - n, Nat.sub_add_cancel (Nat.le_of_not_lt h)⟩
  rw [tsum_congr hpt, ENNReal.tsum_add]
  congr 1
  · refine (tsum_eq_sum (s := Finset.range n) (f := fun a => if a < n then f a else 0)
      fun b hb => if_neg (by simpa using hb)).trans ?_
    exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
  · rw [← Function.Injective.tsum_eq (g := fun j : ℕ => j + n)
      (fun a b h => Nat.add_right_cancel h) hsupp]
    exact tsum_congr fun j => if_neg (by omega)

private theorem tsum_tail_half (n : ℕ) :
    ∑' i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + n + 1) = (2 : ℝ≥0∞)⁻¹ ^ n := by
  have hpt : ∀ i : ℕ, (2 : ℝ≥0∞)⁻¹ ^ (i + n + 1) = (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞)⁻¹ ^ (i + 1) := by
    intro i
    rw [← pow_add]
    ring_nf
  rw [tsum_congr hpt, ENNReal.tsum_mul_left, tsum_ehalf_one, mul_one]

/-- The retained part of the mass: the atoms `i < n` that lie in the cylinder. -/
private noncomputable def headE (p : Baire) (w : List Bool) (n : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range n,
    (2 : ℝ≥0∞)⁻¹ ^ (i + 1) * (cylinder w : Set Cantor).indicator 1 (atomPoint p i)

private theorem measure_cylinder_calibNu (p : Baire) (w : List Bool) :
    calibNuM p (cylinder w)
      = ∑' i, (2 : ℝ≥0∞)⁻¹ ^ (i + 1) *
          (cylinder w : Set Cantor).indicator 1 (atomPoint p i) := by
  rw [calibNuM, Measure.sum_apply _ (measurableSet_cylinder w)]
  exact tsum_congr fun i => by
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_cylinder w)]

/-- **The truncation estimate**: dropping the atoms past `n` costs exactly `2^-n`. -/
private theorem abs_headE_sub_cylMass_le (p : Baire) (w : List Bool) (n : ℕ) :
    |(headE p w n).toReal - cylMass (calibNu p) w| ≤ (2 : ℝ)⁻¹ ^ n := by
  set f : ℕ → ℝ≥0∞ := fun i =>
    (2 : ℝ≥0∞)⁻¹ ^ (i + 1) * (cylinder w : Set Cantor).indicator 1 (atomPoint p i) with hf
  have hbound : ∀ i, f i ≤ (2 : ℝ≥0∞)⁻¹ ^ (i + 1) := by
    intro i
    have hind : (cylinder w : Set Cantor).indicator (1 : Cantor → ℝ≥0∞) (atomPoint p i)
        ≤ 1 := by
      by_cases h : atomPoint p i ∈ (cylinder w : Set Cantor)
      · rw [Set.indicator_of_mem h]; simp
      · rw [Set.indicator_of_notMem h]; exact zero_le_one
    calc f i = (2 : ℝ≥0∞)⁻¹ ^ (i + 1) *
          (cylinder w : Set Cantor).indicator 1 (atomPoint p i) := rfl
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (i + 1) * 1 := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ ^ (i + 1) := mul_one _
  have htotal : calibNuM p (cylinder w) = ∑' i, f i := measure_cylinder_calibNu p w
  have hsplit : (∑' i, f i) = headE p w n + ∑' i, f (i + n) := tsum_split f n
  have htail : (∑' i, f (i + n)) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    refine le_of_le_of_eq (ENNReal.tsum_le_tsum fun i => hbound (i + n)) ?_
    exact tsum_tail_half n
  have hfin : calibNuM p (cylinder w) ≠ ⊤ := measure_ne_top _ _
  have hheadfin : headE p w n ≠ ⊤ := by
    refine ne_top_of_le_ne_top hfin ?_
    rw [htotal, hsplit]
    exact le_self_add
  have htailfin : (∑' i, f (i + n)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) htail
  have hmass : cylMass (calibNu p) w = (headE p w n).toReal + (∑' i, f (i + n)).toReal := by
    rw [cylMass, show (calibNu p).toMeasure = calibNuM p from rfl, htotal, hsplit,
      ENNReal.toReal_add hheadfin htailfin]
  rw [hmass]
  have hnonneg : 0 ≤ (∑' i, f (i + n)).toReal := ENNReal.toReal_nonneg
  have hle : (∑' i, f (i + n)).toReal ≤ (2 : ℝ)⁻¹ ^ n := by
    have := ENNReal.toReal_mono (by simp) htail
    simpa using this
  rw [abs_le]
  constructor <;> linarith

/-! ### The mass as a dyadic rational code -/

/-- The numerator of the level-`n` mass: the atoms `i < n` lying in the cylinder, weighted
so that the common denominator is `2^n`. -/
private def massNum (L : List ℕ) (w : List Bool) (n : ℕ) : ℕ :=
  ((List.range n).map fun i => if memCylL L i w then 2 ^ (n - 1 - i) else 0).sum

/-- The level-`n` mass of the cylinder of `w`, as a rational code. -/
private def massCode (L : List ℕ) (w : List Bool) (n : ℕ) : RatCode :=
  Nat.pair (Nat.pair (massNum L w n) 0) (2 ^ n - 1)

private theorem ratOfCode_massCode (L : List ℕ) (w : List Bool) (n : ℕ) :
    ratOfCode (massCode L w n) = (massNum L w n : ℚ) / 2 ^ n := by
  have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
  rw [ratOfCode, massCode]
  simp only [Nat.unpair_pair, Nat.cast_zero, sub_zero]
  congr 1
  rw [Nat.cast_sub h1]
  push_cast
  ring

private theorem two_pow_div (n i : ℕ) (hi : i < n) :
    ((2 : ℝ) ^ (n - 1 - i)) / 2 ^ n = ((2 : ℝ)⁻¹) ^ (i + 1) := by
  have hsum : (n - 1 - i) + (i + 1) = n := by omega
  have h2 : ((2 : ℝ) ^ (n - 1 - i)) * 2 ^ (i + 1) = 2 ^ n := by rw [← pow_add, hsum]
  rw [inv_pow, div_eq_iff (by positivity : ((2 : ℝ) ^ n) ≠ 0), inv_mul_eq_div,
    eq_div_iff (by positivity : ((2 : ℝ) ^ (i + 1)) ≠ 0)]
  exact h2

/-- The retained mass is exactly the dyadic rational the code names. -/
private theorem headE_toReal_eq {L : List ℕ} {p : Baire} {w : List Bool} {n : ℕ}
    (hL : ∀ i, i < n → ∀ m, m ≤ w.length → guessL L i m = atomGuess p i m) :
    (headE p w n).toReal = (massNum L w n : ℝ) / 2 ^ n := by
  have hterm : ∀ i ∈ Finset.range n,
      ((2 : ℝ≥0∞)⁻¹ ^ (i + 1) *
        (cylinder w : Set Cantor).indicator (1 : Cantor → ℝ≥0∞) (atomPoint p i)) ≠ ⊤ := by
    intro i _
    refine ENNReal.mul_ne_top (by simp) ?_
    by_cases h : atomPoint p i ∈ (cylinder w : Set Cantor)
    · rw [Set.indicator_of_mem h]; simp
    · rw [Set.indicator_of_notMem h]; simp
  rw [headE, ENNReal.toReal_sum hterm]
  have hcast : (massNum L w n : ℝ)
      = ∑ i ∈ Finset.range n, (if memCylL L i w then (2 : ℝ) ^ (n - 1 - i) else 0) := by
    rw [massNum, listSum_range_map]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by by_cases h : memCylL L i w <;> simp [h]
  rw [hcast, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i < n := Finset.mem_range.mp hi
  have hmem : memCylL L i w = true ↔ atomPoint p i ∈ (cylinder w : Set Cantor) :=
    memCylL_eq (hL i hin)
  by_cases h : atomPoint p i ∈ (cylinder w : Set Cantor)
  · rw [Set.indicator_of_mem h, if_pos (hmem.mpr h), two_pow_div n i hin]
    simp
  · rw [Set.indicator_of_notMem h, if_neg (fun hc => h (hmem.mp hc))]
    simp

/-- **The level-`n` mass approximation.** The code names a rational within `2^-n` of the
cylinder mass, reading the input only where `useBound` says. -/
private theorem abs_ratOfCode_massCode_sub_cylMass_le (p : Baire) (w : List Bool) (n : ℕ) :
    |((ratOfCode (massCode (streamTake p (useBound w n)) w n) : ℚ) : ℝ)
        - cylMass (calibNu p) w| ≤ (2 : ℝ)⁻¹ ^ n := by
  have hL : ∀ i, i < n → ∀ m, m ≤ w.length →
      guessL (streamTake p (useBound w n)) i m = atomGuess p i m :=
    fun _ hi _ hm => guessL_streamTake hi hm
  rw [ratOfCode_massCode]
  push_cast
  rw [← headE_toReal_eq hL]
  exact abs_headE_sub_cylMass_le p w n

/-! ### Fold-shaped executable twins

`List.sum`, `List.any` and `List.all` are the semantic forms the estimates above are stated
in. The primitive-recursion witnesses go through these fold-shaped twins, each tied to its
semantic form by an agreement lemma, so no definition is duplicated without a bridge. -/

private def foldSum (l : List ℕ) : ℕ := l.foldr (fun a b => a + b) 0

private theorem foldSum_eq : ∀ l : List ℕ, foldSum l = l.sum
  | [] => rfl
  | a :: l => by
      have ih := foldSum_eq l
      unfold foldSum at ih ⊢
      rw [List.foldr_cons, List.sum_cons, ih]

private theorem primrec_foldSum : Primrec foldSum :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

/-! ### The primitive recursion witnesses

The coded layer is sealed while the witnesses are built: without this the unifier unfolds
the fold bodies during composition and the elaboration explodes. -/

attribute [local irreducible] guessL cumL encL atomL memCylL massNum massCode useBound

private theorem primrec_baseWord : Primrec baseWord :=
  Primrec.list_append.comp primrec_denseWord (Primrec.const [true])

private theorem primrec_shellIdx : Primrec shellIdx :=
  Primrec.list_findIdx primrec_baseWord Primrec.snd

private theorem primrec_guessL :
    Primrec fun v : (List ℕ × ℕ) × ℕ => guessL v.1.1 v.1.2 v.2 := by
  refine ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
    (Primrec₂.natPair.comp Primrec.snd
      (primrec_shellIdx.comp (Primrec.snd.comp Primrec.fst)))).of_eq fun v => ?_
  rw [guessL]

private theorem primrec_cumL : Primrec fun v : (List ℕ × ℕ) × ℕ => cumL v.1.1 v.1.2 v.2 := by
  have hmap : Primrec fun v : (List ℕ × ℕ) × ℕ =>
      (List.range v.2).map fun m => guessL v.1.1 v.1.2 m :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      ((primrec_guessL.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)
  refine (Primrec.nat_add.comp Primrec.snd (primrec_foldSum.comp hmap)).of_eq fun v => ?_
  rw [cumL, foldSum_eq]

private theorem primrec_encL : Primrec fun v : (List ℕ × ℕ) × ℕ => encL v.1.1 v.1.2 v.2 := by
  have hcum : Primrec fun w : ((List ℕ × ℕ) × ℕ) × ℕ => cumL w.1.1.1 w.1.1.2 w.2 :=
    primrec_cumL.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hg : Primrec fun w : ((List ℕ × ℕ) × ℕ) × ℕ => guessL w.1.1.1 w.1.1.2 w.2 :=
    primrec_guessL.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hj : Primrec fun w : ((List ℕ × ℕ) × ℕ) × ℕ => w.1.2 := Primrec.snd.comp Primrec.fst
  have hpred : Primrec₂ fun (v : (List ℕ × ℕ) × ℕ) (n : ℕ) =>
      decide (cumL v.1.1 v.1.2 n ≤ v.2 ∧ v.2 < cumL v.1.1 v.1.2 n + guessL v.1.1 v.1.2 n) := by
    have hp : PrimrecPred fun w : ((List ℕ × ℕ) × ℕ) × ℕ =>
        cumL w.1.1.1 w.1.1.2 w.2 ≤ w.1.2 ∧
          w.1.2 < cumL w.1.1.1 w.1.1.2 w.2 + guessL w.1.1.1 w.1.1.2 w.2 :=
      PrimrecPred.and (Primrec.nat_le.comp hcum hj)
        (Primrec.nat_lt.comp hj (Primrec.nat_add.comp hcum hg))
    obtain ⟨_, hp'⟩ := hp
    exact Primrec.of_eq hp' fun _ => by simp
  refine (primrec_list_any (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    hpred).of_eq fun v => ?_
  rw [encL]

private theorem primrec_atomL : Primrec fun v : (List ℕ × ℕ) × ℕ => atomL v.1.1 v.1.2 v.2 := by
  have hhalf : Primrec fun v : (List ℕ × ℕ) × ℕ => v.2 / 2 :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have heven : Primrec fun v : (List ℕ × ℕ) × ℕ =>
      (baseWord v.1.2).getD (v.2 / 2) false :=
    (Primrec.list_getD false).comp (primrec_baseWord.comp (Primrec.snd.comp Primrec.fst)) hhalf
  have hodd : Primrec fun v : (List ℕ × ℕ) × ℕ => encL v.1.1 v.1.2 (v.2 / 2) :=
    primrec_encL.comp (Primrec.fst.pair hhalf)
  refine (Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    heven hodd).of_eq fun v => ?_
  rw [atomL]

private theorem primrec_memCylL :
    Primrec fun v : (List ℕ × ℕ) × List Bool => memCylL v.1.1 v.1.2 v.2 := by
  have hatom : Primrec fun x : ((List ℕ × ℕ) × List Bool) × ℕ =>
      atomL x.1.1.1 x.1.1.2 x.2 :=
    primrec_atomL.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hgetd : Primrec fun x : ((List ℕ × ℕ) × List Bool) × ℕ =>
      x.1.2.getD x.2 false :=
    (Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  refine (primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
    (Primrec.to₂ (Primrec.beq.comp hatom hgetd))).of_eq fun v => ?_
  rw [memCylL]

/-- Powers of two, primitively — the shared proof lives in `ForMathlib/PrimrecArith.lean`. -/
private theorem primrec_pow2 : Primrec fun k : ℕ => 2 ^ k := primrec_pow 2

private theorem primrec_massNum :
    Primrec fun v : (List ℕ × List Bool) × ℕ => massNum v.1.1 v.1.2 v.2 := by
  have hmem : Primrec fun x : ((List ℕ × List Bool) × ℕ) × ℕ =>
      memCylL x.1.1.1 x.2 x.1.1.2 :=
    primrec_memCylL.comp
      (((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd).pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have hwt : Primrec fun x : ((List ℕ × List Bool) × ℕ) × ℕ =>
      (2 : ℕ) ^ (x.1.2 - 1 - x.2) :=
    primrec_pow2.comp
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1))
        Primrec.snd)
  have hstep : Primrec fun x : ((List ℕ × List Bool) × ℕ) × ℕ =>
      if memCylL x.1.1.1 x.2 x.1.1.2 then (2 : ℕ) ^ (x.1.2 - 1 - x.2) else 0 := by
    refine (Primrec.cond hmem hwt (Primrec.const 0)).of_eq fun x => ?_
    by_cases h : memCylL x.1.1.1 x.2 x.1.1.2 <;> simp [h]
  refine (primrec_foldSum.comp
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) hstep.to₂)).of_eq fun v => ?_
  rw [massNum, foldSum_eq]

private theorem primrec_massCode :
    Primrec fun v : (List ℕ × List Bool) × ℕ => massCode v.1.1 v.1.2 v.2 := by
  refine (Primrec₂.natPair.comp (Primrec₂.natPair.comp primrec_massNum (Primrec.const 0))
    (Primrec.nat_sub.comp (primrec_pow2.comp Primrec.snd) (Primrec.const 1))).of_eq fun v => ?_
  rw [massCode]

private theorem primrec_useBound : Primrec fun v : List Bool × ℕ => useBound v.1 v.2 := by
  have hinner : Primrec₂ fun (v : List Bool × ℕ) (i : ℕ) =>
      (List.range (v.1.length + 1)).map fun m => Nat.pair m (shellIdx i) + 1 :=
    (Primrec.list_map
      (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp
        (Primrec.fst.comp Primrec.fst))))
      ((Primrec.succ.comp (Primrec₂.natPair.comp Primrec.snd
        (primrec_shellIdx.comp (Primrec.snd.comp Primrec.fst)))).to₂)).to₂
  have hflat : Primrec fun v : List Bool × ℕ =>
      (List.range v.2).flatMap fun i =>
        (List.range (v.1.length + 1)).map fun m => Nat.pair m (shellIdx i) + 1 :=
    Primrec.list_flatMap (Primrec.list_range.comp Primrec.snd) hinner
  refine (Primrec.list_foldr hflat (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun v => ?_
  rw [useBound]

/-! ### The preprocessor `K`

One fixed code emits the cylinder-mass name of the calibration measure from the input, and
one fixed realizer from `computableMap_jointOfCantor` turns that into the weak name of the
joint law on the product. Neither depends on the input, so the composite is a single code
uniform in `p`. -/

/-- Names of the unit interval, unpacked into rational approximation (re-derived here
because the copy in `Real.lean` is private to that file). -/
private theorem unitIntervalRep_names_iff' {r : Baire} {x : Set.Icc (0 : ℝ) 1} :
    unitIntervalRep.Names r x ↔
      ∀ n : ℕ, |((ratOfCode (r n) : ℚ) : ℝ) - x.val| ≤ (2 : ℝ)⁻¹ ^ n := by
  constructor
  · intro h n
    have h1 : realPresentation.NamesPoint r x.val :=
      realPresentation.cauchyRep_names_iff.mp (Representation.subtype_names_iff.mp h)
    have := h1 n
    rwa [Real.dist_eq] at this
  · intro h
    refine Representation.subtype_names_iff.mpr
      (realPresentation.cauchyRep_names_iff.mpr fun n => ?_)
    rw [Real.dist_eq]
    exact h n

/-- **The cylinder-mass name of the calibration measure**, from the input alone. -/
private theorem exists_calibMassCode :
    ∃ c : OracleCode, ∀ p : Baire, ∃ F ∈ c.evalStream p, MeasureNames F (calibNu p) := by
  have hb : Primrec₂ fun (v : ℕ) (_ : ℕ) =>
      useBound (denseWord v.unpair.1) v.unpair.2 :=
    (primrec_useBound.comp
      ((primrec_denseWord.comp
        ((Primrec.fst.comp Primrec.unpair).comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst))).to₂
  have hg : Primrec fun v : ℕ =>
      massCode (ofNat (List ℕ) v.unpair.2) (denseWord v.unpair.1.unpair.1)
        v.unpair.1.unpair.2 := by
    have hcoord : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
    exact primrec_massCode.comp
      ((((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)).pair
        (primrec_denseWord.comp (Primrec.fst.comp (Primrec.unpair.comp hcoord)))).pair
        (Primrec.snd.comp (Primrec.unpair.comp hcoord)))
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode hb hg
  refine ⟨c, fun p => ?_⟩
  refine ⟨fun v => massCode (streamTake p (useBound (denseWord v.unpair.1) v.unpair.2))
      (denseWord v.unpair.1) v.unpair.2, ?_, ?_⟩
  · refine OracleCode.mem_evalStream.mpr fun v => ?_
    rw [hc p v]
    refine Part.mem_some_iff.mpr ?_
    rw [Nat.unpair_pair, Denumerable.ofNat_encode]
  · intro s
    refine unitIntervalRep_names_iff'.mpr fun n => ?_
    simp only [Nat.unpair_pair, denseWord_encode]
    exact abs_ratOfCode_massCode_sub_cylMass_le p s n

/-- **The preprocessor.** A single code sends the `Lim` input to a weak name of the
calibration joint law on the product — the same code for every input, and the limit is
nowhere in it. -/
private theorem exists_calibK :
    ∃ K : OracleCode, ∀ (p q : Baire) (hLim : Lim.accepts p q),
      ∃ k ∈ K.evalStream p,
        (weakMeasureRep (cantorPresentation.prod cantorPresentation)).Names k
          (calibJoint p q calibBase hLim) := by
  obtain ⟨c, hc⟩ := exists_calibMassCode
  obtain ⟨c₂, hc₂⟩ := computableMap_jointOfCantor
  refine ⟨c₂.subst c, fun p q hLim => ?_⟩
  obtain ⟨F, hF, hFname⟩ := hc p
  obtain ⟨k, hk, hkname⟩ := hc₂ F (calibNu p) (cantorMeasureRep_names_iff.mpr hFname)
  refine ⟨k, ?_, ?_⟩
  · rw [OracleCode.evalStream_subst hF]
    exact hk
  · rw [← jointOfCantor_calibNu p q hLim]
    exact hkname

/-! ### Separator positions

**The pinned convention.** The search test inspects coordinates `0 … k` through
`streamTake · (k + 1)`, so the least successful *search index* for block `n` is `sepPos q n`
itself — the `−1` conversion happens once, inside the test's prefix length, and nowhere
else. The block lengths are then read off as gaps between consecutive separators. -/

/-- The position of the `n`-th separator of `unaryEncode q`. -/
private def sepPos (q : Baire) (n : ℕ) : ℕ := unaryCum q n + q n

private theorem sepPos_zero (q : Baire) : sepPos q 0 = q 0 := by
  rw [sepPos, show unaryCum q 0 = 0 from rfl, Nat.zero_add]

private theorem sepPos_succ (q : Baire) (n : ℕ) :
    sepPos q (n + 1) = sepPos q n + 1 + q (n + 1) := by
  rw [sepPos, sepPos, unaryCum_succ]

private theorem sepPos_strictMono (q : Baire) : StrictMono (sepPos q) :=
  strictMono_nat_of_lt_succ fun n => by rw [sepPos_succ]; omega

/-- **The gap equations.** Block `0` ends at the first separator, and every later block is
the gap between consecutive separators. -/
private theorem gap_zero (q : Baire) : q 0 = sepPos q 0 := (sepPos_zero q).symm

private theorem gap_succ (q : Baire) (n : ℕ) :
    q (n + 1) = sepPos q (n + 1) - sepPos q n - 1 := by
  rw [sepPos_succ]
  omega

private theorem unaryEncode_sepPos (q : Baire) (n : ℕ) : unaryEncode q (sepPos q n) = false :=
  unaryEncode_apply_sep q n

/-- The separators are exactly the `false` positions: every coordinate lies in some block or
is that block's separator. -/
private theorem exists_sepPos_of_false {q : Baire} {j : ℕ} (h : unaryEncode q j = false) :
    ∃ m, j = sepPos q m := by
  have hP0 : unaryCum q 0 ≤ j := Nat.zero_le j
  set m := Nat.findGreatest (fun m => unaryCum q m ≤ j) j with hm
  have hmle : unaryCum q m ≤ j :=
    Nat.findGreatest_spec (P := fun m => unaryCum q m ≤ j) (Nat.zero_le j) hP0
  have hnext : j < unaryCum q (m + 1) := by
    by_cases hle : m + 1 ≤ j
    · have hng := Nat.findGreatest_is_greatest (by omega : m < m + 1) hle
      omega
    · have hmj : m ≤ j := Nat.findGreatest_le j
      have hcum := le_unaryCum q (m + 1)
      omega
  rw [unaryCum_succ] at hnext
  refine ⟨m, ?_⟩
  by_contra hne
  have hlt : j < unaryCum q m + q m := by
    rw [sepPos] at hne
    omega
  have hin := unaryEncode_apply_mem q m (j - unaryCum q m) (by omega)
  rw [show unaryCum q m + (j - unaryCum q m) = j from by omega] at hin
  rw [hin] at h
  exact Bool.noConfusion h

/-- Coordinates that are not separators sit inside a block, hence are `true`. -/
private theorem unaryEncode_eq_true_of_ne_sepPos {q : Baire} {j : ℕ}
    (h : ∀ m, j ≠ sepPos q m) : unaryEncode q j = true := by
  rcases Bool.eq_false_or_eq_true (unaryEncode q j) with hj | hj
  · exact hj
  · obtain ⟨m, hm⟩ := exists_sepPos_of_false hj
    exact absurd hm (h m)

/-! ### Counting separators in a prefix -/

/-- The search test's counter: how many entries of the prefix are not `1`, i.e. how many
coordinates the decoded stream makes `false`. -/
private def countF (L : List ℕ) : ℕ := L.foldr (fun a b => (if a = 1 then 0 else 1) + b) 0

private theorem countF_append : ∀ L₁ L₂ : List ℕ, countF (L₁ ++ L₂) = countF L₁ + countF L₂
  | [], L₂ => by rw [List.nil_append]; unfold countF; rw [List.foldr_nil]; omega
  | a :: L₁, L₂ => by
      have ih := countF_append L₁ L₂
      unfold countF at ih ⊢
      rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih]
      omega

private theorem countF_streamTake_succ (w : Baire) (k : ℕ) :
    countF (streamTake w (k + 1))
      = countF (streamTake w k) + (if w k = 1 then 0 else 1) := by
  rw [streamTake_succ, countF_append]
  congr 1

/-- Over an interval containing no separator the count does not move. -/
private theorem countF_const_of_no_sep {w q : Baire}
    (hw : ∀ k, w k = 1 ↔ unaryEncode q k = true) {a : ℕ} :
    ∀ {b : ℕ}, a ≤ b → (∀ j, a ≤ j → j < b → ∀ m, j ≠ sepPos q m) →
      countF (streamTake w b) = countF (streamTake w a)
  | 0, hab, _ => by
      rw [Nat.le_zero.mp hab]
  | b + 1, hab, hsep => by
      rcases Nat.eq_or_lt_of_le hab with heq | hlt
      · rw [heq]
      · have hb : a ≤ b := by omega
        have hprev : countF (streamTake w b) = countF (streamTake w a) :=
          countF_const_of_no_sep hw hb fun j hj₁ hj₂ => hsep j hj₁ (by omega)
        have htrue : unaryEncode q b = true :=
          unaryEncode_eq_true_of_ne_sepPos fun m => hsep b hb (by omega) m
        rw [countF_streamTake_succ, hprev, if_pos ((hw b).mpr htrue), Nat.add_zero]

/-- At the `n`-th separator the prefix count is exactly `n + 1`. -/
private theorem countF_sepPos {w q : Baire} (hw : ∀ k, w k = 1 ↔ unaryEncode q k = true) :
    ∀ n : ℕ, countF (streamTake w (sepPos q n + 1)) = n + 1
  | 0 => by
      have hzero : countF (streamTake w (sepPos q 0)) = countF (streamTake w 0) := by
        refine countF_const_of_no_sep hw (Nat.zero_le _) fun j _ hj m hm => ?_
        exact absurd (hm ▸ hj) (by simpa using (sepPos_strictMono q).le_iff_le.mpr (Nat.zero_le m))
      have hsep : ¬ (w (sepPos q 0) = 1) := by
        rw [hw]
        rw [unaryEncode_sepPos]
        exact Bool.noConfusion
      rw [countF_streamTake_succ, hzero, if_neg hsep]
      unfold countF
      rw [streamTake, List.ofFn_zero, List.foldr_nil]
  | n + 1 => by
      have hgap : countF (streamTake w (sepPos q (n + 1)))
          = countF (streamTake w (sepPos q n + 1)) := by
        refine countF_const_of_no_sep hw (by rw [sepPos_succ]; omega) fun j hj₁ hj₂ m hm => ?_
        have h1 : sepPos q n < sepPos q m := by omega
        have h2 : sepPos q m < sepPos q (n + 1) := by omega
        have hn : n < m := (sepPos_strictMono q).lt_iff_lt.mp h1
        have hm' : m < n + 1 := (sepPos_strictMono q).lt_iff_lt.mp h2
        omega
      have hsep : ¬ (w (sepPos q (n + 1)) = 1) := by
        rw [hw, unaryEncode_sepPos]
        exact Bool.noConfusion
      rw [countF_streamTake_succ, hgap, countF_sepPos hw n, if_neg hsep]

/-- Before the `n`-th separator the prefix count has not yet reached `n + 1`. -/
private theorem countF_le_of_lt_sepPos {w q : Baire}
    (hw : ∀ k, w k = 1 ↔ unaryEncode q k = true) :
    ∀ {n j : ℕ}, j < sepPos q n → countF (streamTake w (j + 1)) ≤ n
  | 0, j, hj => by
      have hzero : countF (streamTake w (j + 1)) = countF (streamTake w 0) := by
        refine countF_const_of_no_sep hw (Nat.zero_le _) fun i _ hi m hm => ?_
        have : sepPos q 0 ≤ sepPos q m := (sepPos_strictMono q).monotone (Nat.zero_le m)
        omega
      rw [hzero]
      unfold countF
      rw [streamTake, List.ofFn_zero, List.foldr_nil]
  | n + 1, j, hj => by
      rcases lt_or_ge j (sepPos q n) with hlt | hge
      · exact le_trans (countF_le_of_lt_sepPos hw hlt) (Nat.le_succ n)
      · have hgap : countF (streamTake w (j + 1)) = countF (streamTake w (sepPos q n + 1)) := by
          refine countF_const_of_no_sep hw (by omega) fun i hi₁ hi₂ m hm => ?_
          have h1 : sepPos q n < sepPos q m := by omega
          have h2 : sepPos q m < sepPos q (n + 1) := by omega
          have := (sepPos_strictMono q).lt_iff_lt.mp h1
          have := (sepPos_strictMono q).lt_iff_lt.mp h2
          omega
        rw [hgap, countF_sepPos hw n]

/-! ### The block decoder -/

private theorem primrec_countF : Primrec countF :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_add.comp
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
        (Primrec.const 0) (Primrec.const 1))
      (Primrec.snd.comp Primrec.snd)).to₂)

/-- **The block decoder.** One code recovers the Baire point from any `cantorRep` name of
its unary encoding: search for the `n`-th separator, then read block `n` as the gap to its
predecessor. -/
private theorem exists_unaryDecodeCode :
    ∃ c : OracleCode, ∀ w q : Baire,
      (∀ k, w k = 1 ↔ unaryEncode q k = true) → q ∈ c.evalStream w := by
  have hb : Primrec₂ fun (coord : ℕ) (_ : ℕ) => coord.unpair.2 + 1 :=
    (Primrec.succ.comp ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)).to₂
  have hg : Primrec fun v : ℕ =>
      if countF (ofNat (List ℕ) v.unpair.2) = v.unpair.1.unpair.1 + 1 then 0 else 1 :=
    Primrec.ite
      (Primrec.eq.comp (primrec_countF.comp
          ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.succ.comp ((Primrec.fst.comp Primrec.unpair).comp
          (Primrec.fst.comp Primrec.unpair))))
      (Primrec.const 0) (Primrec.const 1)
  obtain ⟨S, hSiff, _⟩ := exists_prefixSearchCode hb hg
  obtain ⟨predC, hpred⟩ := exists_ofNatFnCode (g := fun v => v - 1)
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp
  obtain ⟨combineC, hcombine⟩ := exists_ofNatFnCode
    (g := fun v => if v.unpair.1 = 0 then v.unpair.2.unpair.1
      else v.unpair.2.unpair.1 - v.unpair.2.unpair.2 - 1)
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 0))
      ((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair))
      (Primrec.nat_sub.comp
        (Primrec.nat_sub.comp
          ((Primrec.fst.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair))
          ((Primrec.snd.comp Primrec.unpair).comp (Primrec.snd.comp Primrec.unpair)))
        (Primrec.const 1))).to_comp
  refine ⟨.comp combineC (.pair OracleCode.id
    (.pair (.comp S OracleCode.id) (.comp S predC))), fun w q hw => ?_⟩
  -- the search finds exactly the `n`-th separator
  have hsearch : ∀ n : ℕ, S.eval w n = Part.some (sepPos q n) := by
    intro n
    refine Part.eq_some_iff.mpr ((hSiff w n (sepPos q n)).mpr ⟨?_, fun j hj => ?_⟩)
    · simp only [SearchSuccess, Nat.unpair_pair, Denumerable.ofNat_encode]
      exact if_pos (countF_sepPos hw n)
    · simp only [SearchSuccess, Nat.unpair_pair, Denumerable.ofNat_encode]
      have hle := countF_le_of_lt_sepPos hw hj
      have hne : ¬ (countF (streamTake w (j + 1)) = n + 1) := by omega
      simp [hne]
  refine OracleCode.mem_evalStream.mpr fun n => ?_
  have hid : (OracleCode.id : OracleCode).eval w n = Part.some n := OracleCode.eval_id w n
  have h1 : (OracleCode.comp S OracleCode.id).eval w n = Part.some (sepPos q n) :=
    (OracleCode.eval_comp_some hid).trans (hsearch n)
  have h2 : (OracleCode.comp S predC).eval w n = Part.some (sepPos q (n - 1)) :=
    (OracleCode.eval_comp_some (hpred w n)).trans (hsearch (n - 1))
  have h3 : (OracleCode.pair (.comp S OracleCode.id) (.comp S predC)).eval w n
      = Part.some (Nat.pair (sepPos q n) (sepPos q (n - 1))) :=
    OracleCode.eval_pair_some h1 h2
  have h4 : (OracleCode.pair OracleCode.id
      (.pair (.comp S OracleCode.id) (.comp S predC))).eval w n
      = Part.some (Nat.pair n (Nat.pair (sepPos q n) (sepPos q (n - 1)))) :=
    OracleCode.eval_pair_some hid h3
  rw [OracleCode.eval_comp_some h4, hcombine]
  refine Part.mem_some_iff.mpr ?_
  cases n with
  | zero => simpa using gap_zero q
  | succ m => simpa using gap_succ q m

/-! ### The postprocessor `H`

Four fixed codes in sequence: the constant name of `0^ω`, the advised evaluator, the Dirac
decoder of unit 40, and the block decoder. The limit enters only the correctness proof — the
code itself depends on nothing but the kernel-answer name it is handed. -/

/-- The fixed name of the accumulation point: every coordinate decodes to the empty word,
whose dense point is `0^ω` exactly. -/
private def zeroName : Baire := fun _ => encode ([] : List Bool)

private theorem wordPoint_nil : wordPoint ([] : List Bool) = (fun _ => false : Cantor) := by
  funext n
  rw [wordPoint_apply]
  rfl

private theorem zeroName_names :
    cantorPresentation.cauchyRep.Names zeroName (fun _ => false : Cantor) := by
  refine cantorPresentation.cauchyRep_names_iff.mpr fun n => ?_
  have hdense : cantorPresentation.dense (zeroName n) = (fun _ => false : Cantor) := by
    rw [zeroName]
    change densePoint (encode ([] : List Bool)) = _
    rw [densePoint, denseWord_encode, wordPoint_nil]
  rw [hdense, dist_self]
  positivity

/-- **The postprocessor.** A single code sends the accepted kernel's name to the limit
stream: evaluate at `0^ω`, decode the resulting Dirac measure, read off the blocks. -/
private theorem exists_calibH :
    ∃ H : OracleCode, ∀ (p q : Baire) (hLim : Lim.accepts p q) (a : Baire),
      (continuousKernelSpace cantorPresentation cantorPresentation).rep.Names a
          (calibPoint p q hLim) →
        ∃ qo ∈ H.evalStream a, baireRep.Names qo q := by
  obtain ⟨e, he⟩ := computableMap_funRep_eval cantorPresentation.cauchyRep
    (weakMeasureRep cantorPresentation)
  obtain ⟨D, hD⟩ := exists_diracDecodeCode
  obtain ⟨Dec, hDec⟩ := exists_unaryDecodeCode
  refine ⟨Dec.subst (D.subst (e.subst (OracleCode.pairCode .query
    (OracleCode.const (encode ([] : List Bool)))))), fun p q hLim a ha => ?_⟩
  -- the interleaved argument: the answer on the even track, the fixed zero name on the odd
  have hquery : a ∈ (OracleCode.query : OracleCode).evalStream a :=
    OracleCode.mem_evalStream.mpr fun n => by
      rw [OracleCode.eval_query]; exact Part.mem_some _
  have hconst : zeroName ∈ (OracleCode.const (encode ([] : List Bool))).evalStream a :=
    OracleCode.mem_evalStream.mpr fun n => by
      rw [OracleCode.eval_const]; exact Part.mem_some _
  have hpair : Baire.interleave a zeroName ∈
      (OracleCode.pairCode .query (OracleCode.const (encode ([] : List Bool)))).evalStream a :=
    OracleCode.pairCode_spec hquery hconst
  have hprod : ((funRep cantorPresentation.cauchyRep
      (weakMeasureRep cantorPresentation)).prod cantorPresentation.cauchyRep).Names
      (Baire.interleave a zeroName)
      ((calibPoint p q hLim).val, (fun _ => false : Cantor)) := by
    refine Representation.prod_names_iff.mpr ⟨?_, ?_⟩
    · rw [Baire.evenPart_interleave]
      exact Representation.subtype_names_iff.mp ha
    · rw [Baire.oddPart_interleave]
      exact zeroName_names
  obtain ⟨out, hout, houtname⟩ := he _ _ hprod
  -- the value at the accumulation point is exactly the Dirac measure at the encoded limit
  have hval : (calibPoint p q hLim).val.toFun (fun _ => false : Cantor)
      = diracProba (unaryEncode q) :=
    ProbabilityMeasure.toMeasure_injective (by
      rw [calibPoint_toMeasure, encodingMap_allFalse]
      rfl)
  obtain ⟨w, hw, hwname⟩ := hD out (unaryEncode q) (by rw [← hval]; exact houtname)
  -- a `cantorRep` name reads the bits of the encoding
  obtain ⟨hle, hmem⟩ := hwname
  have heq : (fun n => w n == 1) = unaryEncode q := hmem
  have hbits : ∀ k, w k = 1 ↔ unaryEncode q k = true := by
    intro k
    have hk := congrFun heq k
    constructor
    · intro h; rw [← hk, h]; rfl
    · intro h; rw [← hk] at h; simpa using h
  refine ⟨q, ?_, Part.mem_some q⟩
  rw [OracleCode.evalStream_subst (OracleCode.evalStream_subst
    (OracleCode.evalStream_subst hpair ▸ hout) ▸ hw)]
  exact hDec w q hbits

/-! ### The headline -/

/-- **The calibration lower bound.** `Lim` strong-Weihrauch reduces to continuous
disintegration on `Cantor × Cantor`: an oracle for the disintegration operator answers the
limit problem.

The preprocessor sends the `Lim` input to a weak name of the calibration joint law, which it
can do from the input alone because the base measure is atomic on finite shells, where the
encoding map reads a guess with no limit in it. The postprocessor evaluates whatever kernel
the oracle returns at the accumulation point and reads the limit off the resulting Dirac
measure. Correctness rests on the accepted output being unique
(`disintegrate_accepts_unique`, under the full-support hypothesis supplied by
`calibBase_support`), which pins the oracle's answer to `calibPoint`. Neither half of the
pair sees the other's data, which is what makes the reduction strong. -/
theorem lim_le_disintegrate :
    Lim ≤sW Disintegrate cantorPresentation cantorPresentation := by
  haveI : Nonempty Cantor := ⟨fun _ => false⟩
  obtain ⟨K, hK⟩ := exists_calibK
  obtain ⟨H, hH⟩ := exists_calibH
  refine strongReduction_iff_exists_reductionPair.mpr ⟨K, H, fun p x hpx hdom => ?_⟩
  obtain rfl : x = p := baireRep_names_iff.mp hpx
  obtain ⟨q, hq⟩ := hdom
  obtain ⟨k, hkK, hkname⟩ := hK x q hq
  refine ⟨k, hkK, calibJoint x q calibBase hq, hkname,
    ⟨calibPoint x q hq, calibPoint_accepts x q calibBase hq calibBase_support⟩,
    fun a y' hay' hacc => ?_⟩
  have huniq : y' = calibPoint x q hq :=
    disintegrate_accepts_unique hacc (calibPoint_accepts x q calibBase hq calibBase_support)
  subst huniq
  obtain ⟨qo, hqoH, hqoname⟩ := hH x q hq a hay'
  exact ⟨qo, hqoH, q, hqoname, hq⟩

end ComputableAnalysis
