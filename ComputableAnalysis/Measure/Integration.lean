/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.WeakRepresentation
import ComputableAnalysis.Metric.Real
import ComputableAnalysis.TypeTwo.Universal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Computability.Halting

/-!
# Bounded-Lipschitz integration as a computable map

Unit 31: over the generic contract `[MetricSpace X] [MeasurableSpace X] [BorelSpace X]`
with a `ComputableMetricPresentation X`, integration of bounded-**Lipschitz** integrands
against weakly represented probability measures is a single computable operation (the
restriction to bounded-Lipschitz — never bounded-continuous — is provably necessary:
escaping mass makes unbounded integration LP-discontinuous, and Type-2 computability
implies continuity):

* `IntegrandName P Φ L B φ` — the integrand-name layout: head numerals `Φ 0 = L`
  (Lipschitz constant) and `Φ 1 = B` (uniform bound), and for every dense-point index
  `m` the component `fun n => Φ (2 + Nat.pair m n)` is a coded-rational approximation
  stream of `φ (P.dense m)` at the pinned rate `((2:ℝ)⁻¹) ^ n`.
* `BoundedLipschitzFun X` — the carrier: a real-valued function bundled with the mere
  existence of natural-number Lipschitz and uniform bounds (`CoeFun` + `@[ext]`; the
  certificate is propositional).
* `blRep P` — the bounded-Lipschitz representation: `Φ` names `f` iff
  `IntegrandName P Φ (Φ 0) (Φ 1) f.toFun`, with the `@[simp]` characterization
  `blRep_names_iff`.  Single-valuedness: the value streams determine `φ` on the dense
  set exactly, and Lipschitz continuity plus density (`DenseRange.equalizer`) extend the
  agreement everywhere.
* `computableMap_integrateBL : ComputableMap ((blRep P).prod (weakMeasureRep P)) realRep
  fun q => ∫ x, q.1 x ∂q.2.toMeasure` — **the frozen operation**; no completeness
  hypothesis, and the realizer code is independent of `X` and `P`.

The engine stays private: the generic Prokhorov stability estimate
`|∫ φ dμ − ∫ φ dν| ≤ (K + 2B) · levyProkhorovDist μ ν`, the total realizer built on the
three-stage adaptive prefix chain (`OracleCode.exists_prefixChainCode`) with stage
`k = n + 1 + (L + 2B)` and an oracle-free coded-rational postprocessor, and the
parity-swap precomposition aligning the product name packing (integrand even, measure
odd) with the engine packing (measure even, integrand odd).

Implementation note: unit 27 keeps its evaluation lemmas for `atomicOfList` private, so
this file re-proves the two branch evaluations against private *definitionally equal*
copies of the clamped-weight helpers (`wRaw`, `wSumL`), the same discipline as unit 28;
the coded-rational arithmetic layer is likewise an intentional private duplication.
-/

namespace ComputableAnalysis

open MeasureTheory Metric Encodable Denumerable OracleCode
open scoped NNReal

/-! ### The generic Prokhorov stability estimate (private engine)

`|∫ φ dμ − ∫ φ dν| ≤ (K + 2B) · levyProkhorovDist μ ν` for a `K`-Lipschitz integrand
`φ` bounded by `B`: mathlib's one-sided bounded-continuous LP estimate applied to the
nonnegative shift `φ + B`, with the thickening error controlled through the Lipschitz
modulus by comparing superlevel-set integrals. -/

section GenericProkhorovStability

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω]

omit [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] in
/-- A probability measure forces the space to be nonempty. -/
private theorem nonempty_of_prob (μ : Measure Ω) [IsProbabilityMeasure μ] : Nonempty Ω := by
  by_contra h
  rw [not_nonempty_iff] at h
  have h1 : μ Set.univ = 1 := measure_univ
  rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
  exact zero_ne_one h1

/-- One-sided generic Prokhorov stability. -/
private theorem integral_sub_integral_le_of_levyProkhorovEDist_lt
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ : Ω → ℝ} {K : ℝ≥0} {B : ℝ} (hLip : LipschitzWith K φ) (hB : ∀ x, |φ x| ≤ B)
    {ε : ℝ} (hε : 0 < ε) (hd : levyProkhorovEDist μ ν < ENNReal.ofReal ε) :
    ∫ x, φ x ∂μ - ∫ x, φ x ∂ν ≤ ((K : ℝ) + 2 * B) * ε := by
  have hne : Nonempty Ω := nonempty_of_prob μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB hne.some)
  have hφc : Continuous φ := hLip.continuous
  have hφm : StronglyMeasurable φ := hφc.stronglyMeasurable
  -- the nonnegative shift as a bounded continuous function
  set f : BoundedContinuousFunction Ω ℝ :=
    .ofNormedAddCommGroup (fun x => φ x + B) (hφc.add continuous_const) (2 * B)
      (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        obtain ⟨h1, h2⟩ := abs_le.mp (hB x)
        constructor <;> linarith) with hf_def
  have hfeq : ∀ x, f x = φ x + B := fun _ => rfl
  have hfnorm : ‖f‖ ≤ 2 * B :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by linarith) _
  have hf0 : (0 : ℝ) ≤ ‖f‖ := norm_nonneg f
  have hfnn : ∀ x, 0 ≤ f x := fun x => by
    rw [hfeq]
    obtain ⟨h1, -⟩ := abs_le.mp (hB x)
    linarith
  have hφintμ : Integrable φ μ :=
    ⟨hφm.aestronglyMeasurable, .of_bounded (C := B)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)⟩
  have hφintν : Integrable φ ν :=
    ⟨hφm.aestronglyMeasurable, .of_bounded (C := B)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)⟩
  have hreal_univ : ∀ (κ : Measure Ω) [IsProbabilityMeasure κ], κ.real Set.univ = 1 :=
    fun κ _ => by rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  have hIfμ : ∫ x, f x ∂μ = (∫ x, φ x ∂μ) + B := by
    simp only [hfeq]
    rw [integral_add hφintμ (integrable_const B), integral_const, hreal_univ μ, one_smul]
  have hIfν : ∫ x, f x ∂ν = (∫ x, φ x ∂ν) + B := by
    simp only [hfeq]
    rw [integral_add hφintν (integrable_const B), integral_const, hreal_univ ν, one_smul]
  -- step 1: the mathlib LP bound
  have step1 := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt μ ν hε hd f
    (Filter.Eventually.of_forall hfnn)
  -- the superlevel measure function of `f` under `ν`
  set g : ℝ → ℝ := fun s => ν.real {a | s ≤ f a} with hg_def
  have hganti : Antitone g := fun s₁ s₂ h =>
    measureReal_mono (fun a (ha : s₂ ≤ f a) => h.trans ha) (measure_ne_top _ _)
  have hg0 : ∀ s, 0 ≤ g s := fun _ => measureReal_nonneg
  have hg1 : ∀ s, g s ≤ 1 := fun s => by
    rw [hg_def]
    exact (measureReal_mono (Set.subset_univ _) (measure_ne_top _ _)).trans_eq
      (hreal_univ ν)
  -- step 2: thickenings of superlevel sets land in shifted superlevel sets
  have hLε0 : 0 ≤ (K : ℝ) * ε := mul_nonneg K.coe_nonneg hε.le
  have hthick : ∀ t : ℝ,
      ν.real (thickening ε {a | t ≤ f a}) ≤ g (t - (K : ℝ) * ε) := by
    intro t
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    obtain ⟨z, hz, hdist⟩ := Metric.mem_thickening_iff.mp hx
    have h1 : dist (φ x) (φ z) ≤ (K : ℝ) * dist x z := hLip.dist_le_mul x z
    rw [Real.dist_eq] at h1
    have h2 : (K : ℝ) * dist x z ≤ (K : ℝ) * ε :=
      mul_le_mul_of_nonneg_left hdist.le K.coe_nonneg
    have h3 := (abs_le.mp (h1.trans h2)).1
    change t - (K : ℝ) * ε ≤ f x
    have hzf : t ≤ f z := hz
    rw [hfeq] at hzf ⊢
    linarith
  -- step 3: compare the two `t`-integrals over `Ioc 0 ‖f‖`
  have intble_thick :
      IntegrableOn (fun t => ν.real (thickening ε {a | t ≤ f a})) (Set.Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := ν.real Set.univ) measure_Ioc_lt_top.ne
    · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
      exact fun _ _ hst => measure_mono <| thickening_subset_of_subset ε fun _ h => hst.trans h
    · apply Filter.Eventually.of_forall fun t => ?_
      simp only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact ENNReal.toReal_mono (by finiteness) <| measure_mono (Set.subset_univ _)
  have hganti' : Antitone fun t => g (t - (K : ℝ) * ε) := fun t₁ t₂ h =>
    hganti (by linarith)
  have intble_shift : IntegrableOn (fun t => g (t - (K : ℝ) * ε)) (Set.Ioc 0 ‖f‖) := by
    apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
    · exact hganti'.measurable.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _)]
        exact hg1 _
  have step3 : (∫ t in Set.Ioc 0 ‖f‖, ν.real (thickening ε {a | t ≤ f a}))
      ≤ ∫ t in Set.Ioc 0 ‖f‖, g (t - (K : ℝ) * ε) :=
    setIntegral_mono_on intble_thick intble_shift measurableSet_Ioc fun t _ => hthick t
  -- steps 4–8: the shifted integral is at most `K ε + ∫ f dν`
  have hgIntble : ∀ a b : ℝ, IntervalIntegrable g MeasureTheory.volume a b :=
    fun _ _ => hganti.intervalIntegrable
  have step4 : ∫ t in Set.Ioc 0 ‖f‖, g (t - (K : ℝ) * ε)
      = ∫ t in (0 : ℝ)..‖f‖, g (t - (K : ℝ) * ε) :=
    (intervalIntegral.integral_of_le hf0).symm
  have step5 : ∫ t in (0 : ℝ)..‖f‖, g (t - (K : ℝ) * ε)
      = ∫ t in (0 - (K : ℝ) * ε)..(‖f‖ - (K : ℝ) * ε), g t :=
    intervalIntegral.integral_comp_sub_right g ((K : ℝ) * ε)
  have step6 : ∫ t in (0 - (K : ℝ) * ε)..(‖f‖ - (K : ℝ) * ε), g t
      ≤ ∫ t in (0 - (K : ℝ) * ε)..‖f‖, g t :=
    intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun s => hg0 s) (hgIntble _ _)
  have step7 : ∫ t in (0 - (K : ℝ) * ε)..‖f‖, g t
      = (∫ t in (0 - (K : ℝ) * ε)..(0 : ℝ), g t) + ∫ t in (0 : ℝ)..‖f‖, g t :=
    (intervalIntegral.integral_add_adjacent_intervals (hgIntble _ _) (hgIntble _ _)).symm
  have step8 : ∫ t in (0 - (K : ℝ) * ε)..(0 : ℝ), g t ≤ (K : ℝ) * ε := by
    have h1 : ∫ t in (0 - (K : ℝ) * ε)..(0 : ℝ), g t
        ≤ ∫ _t in (0 - (K : ℝ) * ε)..(0 : ℝ), (1 : ℝ) :=
      intervalIntegral.integral_mono_on (by linarith) (hgIntble _ _)
        intervalIntegrable_const fun s _ => hg1 s
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at h1
    linarith
  have step9 : ∫ t in (0 : ℝ)..‖f‖, g t = ∫ x, f x ∂ν := by
    rw [intervalIntegral.integral_of_le hf0]
    exact (BoundedContinuousFunction.integral_eq_integral_meas_le f ν
      (Filter.Eventually.of_forall hfnn)).symm
  -- assembly
  have hchain : ∫ x, f x ∂μ ≤ (∫ x, f x ∂ν) + (K : ℝ) * ε + ε * ‖f‖ := by
    linarith [step1, step3, step4, step5, step6, step7, step8, step9]
  have hεnorm : ε * ‖f‖ ≤ ε * (2 * B) := mul_le_mul_of_nonneg_left hfnorm hε.le
  rw [hIfμ, hIfν] at hchain
  nlinarith [hchain, hεnorm]

/-- **The generic Prokhorov stability estimate** (private engine):
`|∫ φ dμ − ∫ φ dν| ≤ (K + 2B) · levyProkhorovDist μ ν`. -/
private theorem abs_integral_sub_integral_le_levyProkhorovDist
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {φ : Ω → ℝ} {K : ℝ≥0} {B : ℝ} (hLip : LipschitzWith K φ) (hB : ∀ x, |φ x| ≤ B) :
    |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ ((K : ℝ) + 2 * B) * levyProkhorovDist μ ν := by
  have hne : Nonempty Ω := nonempty_of_prob μ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB hne.some)
  have hC0 : 0 ≤ (K : ℝ) + 2 * B := by positivity
  set d : ℝ := levyProkhorovDist μ ν with hd_def
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have key : ∀ ε : ℝ, d < ε → |∫ x, φ x ∂μ - ∫ x, φ x ∂ν| ≤ ((K : ℝ) + 2 * B) * ε := by
    intro ε hdε
    have hε0 : 0 < ε := lt_of_le_of_lt hd0 hdε
    have hedist : levyProkhorovEDist μ ν < ENNReal.ofReal ε :=
      (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr hdε
    have hedist' : levyProkhorovEDist ν μ < ENNReal.ofReal ε := by
      rwa [levyProkhorovEDist_comm]
    have h1 := integral_sub_integral_le_of_levyProkhorovEDist_lt μ ν hLip hB hε0 hedist
    have h2 := integral_sub_integral_le_of_levyProkhorovEDist_lt ν μ hLip hB hε0 hedist'
    rw [abs_le]
    constructor <;> linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hstep : d < d + δ / (((K : ℝ) + 2 * B) + 1) := by
    have : 0 < δ / (((K : ℝ) + 2 * B) + 1) := div_pos hδ (by linarith)
    linarith
  have h3 := key _ hstep
  have h4 : ((K : ℝ) + 2 * B) * (δ / (((K : ℝ) + 2 * B) + 1)) ≤ δ := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < ((K : ℝ) + 2 * B) + 1)]
    nlinarith
  calc |∫ x, φ x ∂μ - ∫ x, φ x ∂ν|
      ≤ ((K : ℝ) + 2 * B) * (d + δ / (((K : ℝ) + 2 * B) + 1)) := h3
    _ = ((K : ℝ) + 2 * B) * d + ((K : ℝ) + 2 * B) * (δ / (((K : ℝ) + 2 * B) + 1)) := by
        ring
    _ ≤ ((K : ℝ) + 2 * B) * d + δ := by linarith

end GenericProkhorovStability

/-! ### Clamped weights: definitionally equal copies of unit 27's private helpers -/

/-- The clamped rational weight of a weight code (definitionally equal to the private
helper inside `atomicOfList`). -/
private def wRaw (c : ℕ) : ℚ := max 0 (min 1 (ratOfCode c))

private theorem wRaw_nonneg (c : ℕ) : 0 ≤ wRaw c := le_max_left _ _

/-- The (rational) total clamped weight of a decoded atom list (definitionally equal to
the private helper inside `atomicOfList`). -/
private def wSumL (l : List (ℕ × ℕ)) : ℚ := (l.map fun pr => wRaw pr.2).sum

private theorem wSumL_nonneg (l : List (ℕ × ℕ)) : 0 ≤ wSumL l :=
  List.sum_nonneg fun x hx => by
    obtain ⟨pr, -, rfl⟩ := List.mem_map.mp hx
    exact wRaw_nonneg _

/-- A mapped list sum as a `Fin` sum over positions. -/
private theorem listSum_map_eq_finSum {β M : Type*} [AddCommMonoid M] (l : List β)
    (g : β → M) : (l.map g).sum = ∑ i : Fin l.length, g l[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

private theorem sum_normWt {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) :
    ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) = 1 := by
  have : ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
      = (((∑ i : Fin l.length, wRaw l[i].2) / wSumL l : ℚ) : ℝ) := by
    push_cast
    rw [Finset.sum_div]
  rw [this]
  have hsum : ∑ i : Fin l.length, wRaw l[i].2 = wSumL l :=
    (listSum_map_eq_finSum l fun pr => wRaw pr.2).symm
  rw [hsum, div_self h0]
  norm_num

private theorem normWt_nonneg {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) (i : Fin l.length) :
    (0 : ℝ) ≤ ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) := by
  have hpos : (0 : ℚ) < wSumL l := lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
  exact_mod_cast div_nonneg (wRaw_nonneg _) hpos.le

/-! ### Evaluation of the decoded atomics

The two branch evaluations of unit 27's `atomicOfList`, restated over the private
copies above; the proofs cross the definitional equality (unit 28's discipline). -/

section AtomicEval

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

omit [BorelSpace X] in
/-- Nonzero total weight: the decoded atomic is the renormalized weighted Dirac sum. -/
private theorem toMeasure_atomicOfList_of_ne {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) :
    (atomicOfList P l).toMeasure
      = ∑ i : Fin l.length,
          ENNReal.ofReal ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            • Measure.dirac (P.dense l[i].1) := by
  rw [atomicOfList]
  split
  · next h => exact absurd h h0
  · next h => rfl

omit [BorelSpace X] in
/-- Zero total weight: the decoded atomic is the default Dirac at dense point `0`. -/
private theorem toMeasure_atomicOfList_of_eq {l : List (ℕ × ℕ)} (h0 : wSumL l = 0) :
    (atomicOfList P l).toMeasure = Measure.dirac (P.dense 0) := by
  rw [atomicOfList]
  split
  · next h => rfl
  · next h => exact absurd h0 h

end AtomicEval

/-! ### The integrand-name layout -/

section IntegrandLayer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The integrand-name layout** over a presentation `P`: head numerals `L` (Lipschitz
constant) and `B` (uniform bound) at `Φ 0`, `Φ 1`, and for every dense-point index `m`
the component `fun n => Φ (2 + Nat.pair m n)` is a fast rational approximation stream of
`φ (P.dense m)`. -/
structure IntegrandName (P : ComputableMetricPresentation X) (Φ : Baire) (L B : ℕ)
    (φ : X → ℝ) : Prop where
  /-- The first head coordinate carries the Lipschitz constant. -/
  headL : Φ 0 = L
  /-- The second head coordinate carries the uniform bound. -/
  headB : Φ 1 = B
  /-- The named function is Lipschitz with the head constant. -/
  lip : LipschitzWith (L : ℝ≥0) φ
  /-- The named function is uniformly bounded by the head bound. -/
  bound : ∀ x, |φ x| ≤ (B : ℝ)
  /-- The value streams approximate the dense-point values at the pinned rate. -/
  approx : ∀ m n : ℕ,
    |((ratOfCode (Φ (2 + Nat.pair m n)) : ℚ) : ℝ) - φ (P.dense m)| ≤ (2 : ℝ)⁻¹ ^ n

variable (P : ComputableMetricPresentation X)

/-! #### Measurability, integrability, and atomic integrals -/

private theorem stronglyMeasurable_of_lipschitz {K : ℝ≥0} {φ : X → ℝ}
    (h : LipschitzWith K φ) : StronglyMeasurable φ :=
  h.continuous.stronglyMeasurable

omit [MetricSpace X] [BorelSpace X] in
private theorem integrable_of_abs_le {φ : X → ℝ} {B : ℝ} (hφm : StronglyMeasurable φ)
    (hB : ∀ x, |φ x| ≤ B) (μ : Measure X) [IsFiniteMeasure μ] : Integrable φ μ :=
  ⟨hφm.aestronglyMeasurable, .of_bounded (C := B)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)⟩

omit [MetricSpace X] [BorelSpace X] in
/-- Integrals against finite atomic measures are finite weighted sums (generic). -/
private theorem integral_sum_smul_dirac {k : ℕ} (a : Fin k → ℝ) (ha : ∀ i, 0 ≤ a i)
    (x : Fin k → X) {φ : X → ℝ} {B : ℝ}
    (hφm : StronglyMeasurable φ) (hB : ∀ y, |φ y| ≤ B) :
    ∫ y, φ y ∂(∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) = ∑ i, a i * φ (x i) := by
  rw [integral_finsetSum_measure fun i _ =>
    (integrable_of_abs_le hφm hB (Measure.dirac (x i))).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, integral_dirac' _ _ hφm, smul_eq_mul,
    ENNReal.toReal_ofReal (ha i)]

omit [BorelSpace X] in
/-- The integral against a decoded atomic measure with nonzero total weight. -/
private theorem integral_atomicOfList {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) {φ : X → ℝ}
    {B : ℝ} (hφm : StronglyMeasurable φ) (hB : ∀ y, |φ y| ≤ B) :
    ∫ y, φ y ∂(atomicOfList P l).toMeasure
      = ∑ i : Fin l.length,
          ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) * φ (P.dense l[i].1) := by
  rw [toMeasure_atomicOfList_of_ne P h0]
  exact integral_sum_smul_dirac _ (normWt_nonneg h0) _ hφm hB

omit [BorelSpace X] in
/-- The integral against a decoded atomic measure with zero total weight. -/
private theorem integral_atomicOfList_zero {l : List (ℕ × ℕ)} (h0 : wSumL l = 0)
    {φ : X → ℝ} (hφm : StronglyMeasurable φ) :
    ∫ y, φ y ∂(atomicOfList P l).toMeasure = φ (P.dense 0) := by
  rw [toMeasure_atomicOfList_of_eq P h0]
  exact integral_dirac' _ _ hφm

/-! #### The rational integral approximant read off the names -/

/-- The rational integral approximant of the integrand name `Φ` against the atom list
`l` at precision `n`. -/
private def integralApprox (Φ : Baire) (l : List (ℕ × ℕ)) (n : ℕ) : ℚ :=
  if wSumL l = 0 then ratOfCode (Φ (2 + Nat.pair 0 n))
  else ∑ i : Fin l.length,
    (wRaw l[i].2 / wSumL l) * ratOfCode (Φ (2 + Nat.pair l[i].1 n))

/-- **The name-level computation is correct at every precision.** -/
private theorem abs_integralApprox_sub_integral_le {Φ : Baire} {L B : ℕ} {φ : X → ℝ}
    (hname : IntegrandName P Φ L B φ) (l : List (ℕ × ℕ)) (n : ℕ) :
    |((integralApprox Φ l n : ℚ) : ℝ) - ∫ y, φ y ∂(atomicOfList P l).toMeasure|
      ≤ (2 : ℝ)⁻¹ ^ n := by
  have hφm : StronglyMeasurable φ := stronglyMeasurable_of_lipschitz hname.lip
  by_cases h0 : wSumL l = 0
  · rw [integralApprox, if_pos h0, integral_atomicOfList_zero P h0 hφm]
    exact hname.approx 0 n
  · rw [integralApprox, if_neg h0, integral_atomicOfList P h0 hφm hname.bound]
    have hpos : (0 : ℚ) < wSumL l := lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
    have hw0 : ∀ i : Fin l.length, (0 : ℝ) ≤ ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) :=
      normWt_nonneg h0
    have hw1 : ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) = 1 :=
      sum_normWt h0
    have hcast : ((∑ i : Fin l.length,
          (wRaw l[i].2 / wSumL l) * ratOfCode (Φ (2 + Nat.pair l[i].1 n)) : ℚ) : ℝ)
        = ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            * ((ratOfCode (Φ (2 + Nat.pair l[i].1 n)) : ℚ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, ← Finset.sum_sub_distrib]
    calc |∑ i : Fin l.length,
          (((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
              * ((ratOfCode (Φ (2 + Nat.pair l[i].1 n)) : ℚ) : ℝ)
            - ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) * φ (P.dense l[i].1))|
        = |∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            * (((ratOfCode (Φ (2 + Nat.pair l[i].1 n)) : ℚ) : ℝ)
              - φ (P.dense l[i].1))| := by
          congr 1
          exact Finset.sum_congr rfl fun i _ => (mul_sub _ _ _).symm
      _ ≤ ∑ i : Fin l.length, |((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            * (((ratOfCode (Φ (2 + Nat.pair l[i].1 n)) : ℚ) : ℝ)
              - φ (P.dense l[i].1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ) * (2 : ℝ)⁻¹ ^ n := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (hw0 i)]
          exact mul_le_mul_of_nonneg_left (hname.approx _ n) (hw0 i)
      _ = (∑ i : Fin l.length, ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)) * (2 : ℝ)⁻¹ ^ n :=
          (Finset.sum_mul _ _ _).symm
      _ = (2 : ℝ)⁻¹ ^ n := by rw [hw1, one_mul]

end IntegrandLayer

/-! ### Coded rational arithmetic (private engine; the known intentional duplication —
units 27/28 carry their own private copies) -/

section CodedRationalArithmetic

/-- The canonical code of `1`. -/
private def oneCode : ℕ := Nat.pair (Nat.pair 1 0) 0

private theorem ratOfCode_oneCode : ratOfCode oneCode = 1 := by
  simp [ratOfCode, oneCode]

/-- Addition of rational codes. -/
private def addCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.1 * (m₁.unpair.2 + 1))
      (m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.2 * (m₁.unpair.2 + 1)))
    ((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1)

private theorem ratOfCode_addCode (m₁ m₂ : ℕ) :
    ratOfCode (addCode m₁ m₂) = ratOfCode m₁ + ratOfCode m₂ := by
  have hden : (((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1 : ℕ) : ℚ) + 1
      = ((m₁.unpair.2 : ℚ) + 1) * ((m₂.unpair.2 : ℚ) + 1) := by
    have h1 : 1 ≤ (m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    push_cast [h1]
    ring
  have h₁ : ((m₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((m₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  simp only [ratOfCode, addCode, Nat.unpair_pair, hden]
  field_simp
  push_cast
  ring

/-- Multiplication of rational codes. -/
private def mulCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (m₁.unpair.1.unpair.1 * m₂.unpair.1.unpair.1
        + m₁.unpair.1.unpair.2 * m₂.unpair.1.unpair.2)
      (m₁.unpair.1.unpair.1 * m₂.unpair.1.unpair.2
        + m₁.unpair.1.unpair.2 * m₂.unpair.1.unpair.1))
    ((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1)

private theorem ratOfCode_mulCode (m₁ m₂ : ℕ) :
    ratOfCode (mulCode m₁ m₂) = ratOfCode m₁ * ratOfCode m₂ := by
  have hden : (((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1 : ℕ) : ℚ) + 1
      = ((m₁.unpair.2 : ℚ) + 1) * ((m₂.unpair.2 : ℚ) + 1) := by
    have h1 : 1 ≤ (m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    push_cast [h1]
    ring
  have h₁ : ((m₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((m₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  simp only [ratOfCode, mulCode, Nat.unpair_pair, hden]
  field_simp
  push_cast
  ring

/-- Clamp a rational code into `[0,1]`. -/
private def clampCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 then zeroCode
  else if m.unpair.1.unpair.2 + m.unpair.2 + 1 ≤ m.unpair.1.unpair.1 then oneCode
  else m

private theorem ratOfCode_clampCode (m : ℕ) :
    ratOfCode (clampCode m) = max 0 (min 1 (ratOfCode m)) := by
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  by_cases h1 : m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2
  · have hab : (m.unpair.1.unpair.1 : ℚ) ≤ (m.unpair.1.unpair.2 : ℚ) := by exact_mod_cast h1
    have hr : ratOfCode m ≤ 0 := by
      unfold ratOfCode
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    rw [clampCode, if_pos h1, ratOfCode_zeroCode, eq_comm,
      max_eq_left ((min_le_right _ _).trans hr)]
  · by_cases h2 : m.unpair.1.unpair.2 + m.unpair.2 + 1 ≤ m.unpair.1.unpair.1
    · have hcast : (m.unpair.1.unpair.2 : ℚ) + (m.unpair.2 : ℚ) + 1
          ≤ (m.unpair.1.unpair.1 : ℚ) := by exact_mod_cast h2
      have hr : 1 ≤ ratOfCode m := by
        unfold ratOfCode
        rw [le_div_iff₀ hden]
        linarith
      rw [clampCode, if_neg h1, if_pos h2, ratOfCode_oneCode, eq_comm,
        min_eq_left hr, max_eq_right zero_le_one]
    · have hba : (m.unpair.1.unpair.2 : ℚ) ≤ (m.unpair.1.unpair.1 : ℚ) := by
        exact_mod_cast (Nat.lt_of_not_le h1).le
      have hac : (m.unpair.1.unpair.1 : ℚ)
          ≤ (m.unpair.1.unpair.2 : ℚ) + (m.unpair.2 : ℚ) := by
        exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le h2)
      have hr0 : 0 ≤ ratOfCode m := by
        unfold ratOfCode
        exact div_nonneg (by linarith) hden.le
      have hr1 : ratOfCode m ≤ 1 := by
        unfold ratOfCode
        rw [div_le_one hden]
        linarith
      rw [clampCode, if_neg h1, if_neg h2, eq_comm, min_eq_right hr1, max_eq_right hr0]

/-- The clamped weight is the decoded clamp code. -/
private theorem wRaw_eq_ratOfCode_clampCode (c : ℕ) : wRaw c = ratOfCode (clampCode c) :=
  (ratOfCode_clampCode c).symm

/-- Sum of a list of rational codes. -/
private def sumCode (l : List ℕ) : ℕ :=
  l.foldr addCode 0

private theorem ratOfCode_sumCode (l : List ℕ) :
    ratOfCode (sumCode l) = (l.map ratOfCode).sum := by
  induction l with
  | nil =>
    simp only [sumCode, List.foldr_nil, List.map_nil, List.sum_nil]
    simp [ratOfCode]
  | cons a l ih =>
    simp only [sumCode, List.foldr_cons, List.map_cons, List.sum_cons, ratOfCode_addCode]
    rw [← ih]
    rfl

/-- The sign of a coded rational is the sign of the `ℕ` numerator difference. -/
private theorem ratOfCode_nonpos_iff (m : ℕ) :
    ratOfCode m ≤ 0 ↔ m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 := by
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  constructor
  · intro h
    by_contra hab
    have hba : (m.unpair.1.unpair.2 : ℚ) < (m.unpair.1.unpair.1 : ℚ) := by
      exact_mod_cast Nat.lt_of_not_le hab
    have : 0 < ratOfCode m := by
      unfold ratOfCode
      exact div_pos (by linarith) hden
    linarith
  · intro h
    have hab : (m.unpair.1.unpair.1 : ℚ) ≤ (m.unpair.1.unpair.2 : ℚ) := by exact_mod_cast h
    unfold ratOfCode
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

private theorem ratOfCode_pos_iff (m : ℕ) :
    0 < ratOfCode m ↔ m.unpair.1.unpair.2 < m.unpair.1.unpair.1 := by
  rw [← not_le, ratOfCode_nonpos_iff, not_le]

/-- Division of rational codes by a divisor with positive coded value. -/
private def divCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1))
      (m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1)))
    ((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1)

private theorem ratOfCode_divCode (m₁ m₂ : ℕ)
    (h : m₂.unpair.1.unpair.2 < m₂.unpair.1.unpair.1) :
    ratOfCode (divCode m₁ m₂) = ratOfCode m₁ / ratOfCode m₂ := by
  have hD : 1 ≤ (m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hden : (((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1 : ℕ)
        : ℚ) + 1
      = ((m₁.unpair.2 : ℚ) + 1)
          * ((m₂.unpair.1.unpair.1 : ℚ) - (m₂.unpair.1.unpair.2 : ℚ)) := by
    rw [Nat.cast_sub hD, Nat.cast_mul, Nat.cast_sub h.le]
    push_cast
    ring
  have h₁ : ((m₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((m₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₃ : ((m₂.unpair.1.unpair.1 : ℚ) - (m₂.unpair.1.unpair.2 : ℚ)) ≠ 0 := by
    have : (m₂.unpair.1.unpair.2 : ℚ) < (m₂.unpair.1.unpair.1 : ℚ) := by exact_mod_cast h
    linarith
  simp only [ratOfCode, divCode, Nat.unpair_pair, hden]
  field_simp
  push_cast
  ring

private theorem primrec_unpairFst : Primrec fun m : ℕ => m.unpair.1 :=
  Primrec.fst.comp Primrec.unpair

private theorem primrec_unpairSnd : Primrec fun m : ℕ => m.unpair.2 :=
  Primrec.snd.comp Primrec.unpair

section PrimrecFacts

open Primrec

private theorem primrec₂_addCode : Primrec₂ addCode := by
  have a₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp fst
  have b₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp fst
  have a₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp snd
  have b₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp snd
  have d₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp fst)
  have d₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp snd)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (nat_add.comp (nat_mul.comp a₁ d₂) (nat_mul.comp a₂ d₁))
      (nat_add.comp (nat_mul.comp b₁ d₂) (nat_mul.comp b₂ d₁)))
    (nat_sub.comp (nat_mul.comp d₁ d₂) (const 1))

private theorem primrec₂_mulCode : Primrec₂ mulCode := by
  have a₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp fst
  have b₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp fst
  have a₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp snd
  have b₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp snd
  have d₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp fst)
  have d₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp snd)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (nat_add.comp (nat_mul.comp a₁ a₂) (nat_mul.comp b₁ b₂))
      (nat_add.comp (nat_mul.comp a₁ b₂) (nat_mul.comp b₁ a₂)))
    (nat_sub.comp (nat_mul.comp d₁ d₂) (const 1))

private theorem primrec_clampCode : Primrec clampCode := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  exact Primrec.ite (Primrec.nat_le.comp ha hb) (const zeroCode)
    (Primrec.ite
      (Primrec.nat_le.comp
        (succ.comp (nat_add.comp hb primrec_unpairSnd)) ha)
      (const oneCode) Primrec.id)

private theorem primrec_sumCode : Primrec sumCode :=
  (list_foldr Primrec.id (const 0)
    (primrec₂_addCode.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun _ => rfl

private theorem primrec₂_divCode : Primrec₂ divCode := by
  have a₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp fst
  have b₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp fst
  have a₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp snd
  have b₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp snd
  have d₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp fst)
  have d₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp snd)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (nat_mul.comp a₁ d₂) (nat_mul.comp b₁ d₂))
    (nat_sub.comp (nat_mul.comp d₁ (nat_sub.comp a₂ b₂)) (const 1))

end PrimrecFacts

end CodedRationalArithmetic

/-! ### Small helpers -/

/-- Extracting a coordinate from an encoded stream prefix. -/
private theorem streamTake_getD (p : Baire) {j m : ℕ} (h : j < m) :
    (streamTake p m).getD j 0 = p j := by
  rw [List.getD_eq_getElem _ _ (by rw [length_streamTake]; exact h), getElem_streamTake]

/-- The largest dense-word index of an atom list (prefix-length bound). -/
private def maxIdx (l : List (ℕ × ℕ)) : ℕ := l.foldr (fun pr acc => max pr.1 acc) 0

private theorem fst_le_maxIdx : ∀ {l : List (ℕ × ℕ)} {pr : ℕ × ℕ},
    pr ∈ l → pr.1 ≤ maxIdx l := by
  intro l
  induction l with
  | nil => intro pr h; cases h
  | cons a t ih =>
    intro pr h
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem primrec_maxIdx : Primrec maxIdx :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun _ => rfl

private theorem pair_le_pair_left {a b : ℕ} (h : a ≤ b) (c : ℕ) :
    Nat.pair a c ≤ Nat.pair b c := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact (Nat.pair_lt_pair_left c h).le
  · exact le_rfl

/-! ### The integration realizer's stage function, bounds, and postprocessor

The head-access assembly rides unit 26's `OracleCode.exists_prefixChainCode`: the needed
prefix length depends on data at coordinates 1 and 3 (the packed heads) and then on the
atom-list code at a computed coordinate, so three prefix reads are chained, each stage's
bound recomputed primitively from the previous stage's encoded prefix. -/

/-- The stage of the measure name consumed at output precision `n`:
`k = n + 1 + (L + 2B)`, so that `(L + 2B) · (2⁻¹)^k ≤ (2⁻¹)^(n+1)`. -/
private def stageOf (n L B : ℕ) : ℕ := n + 1 + (L + 2 * B)

/-- Stage-1 → stage-2 bound: from the length-4 prefix read the heads `L = F 1`,
`B = F 3` and cover the atom-list coordinate `2 · stageOf n L B`. -/
private def bound₁ (n h : ℕ) : ℕ :=
  2 * stageOf n ((ofNat (List ℕ) h).getD 1 0) ((ofNat (List ℕ) h).getD 3 0) + 4

/-- Stage-2 → stage-3 bound: additionally cover all integrand-value coordinates of the
decoded atom list at value precision `n + 1` (through `maxIdx`). -/
private def bound₂ (n h : ℕ) : ℕ :=
  2 * (2 + Nat.pair (maxIdx (ofNat (List (ℕ × ℕ))
        ((ofNat (List ℕ) h).getD
          (2 * stageOf n ((ofNat (List ℕ) h).getD 1 0) ((ofNat (List ℕ) h).getD 3 0)) 0)))
      (n + 1)) + 2
    + (2 * stageOf n ((ofNat (List ℕ) h).getD 1 0) ((ofNat (List ℕ) h).getD 3 0) + 4)

private theorem primrec₂_bound₁ : Primrec₂ bound₁ := by
  have hu : Primrec fun p : ℕ × ℕ => ofNat (List ℕ) p.2 :=
    (Primrec.ofNat (List ℕ)).comp Primrec.snd
  have hL : Primrec fun p : ℕ × ℕ => (ofNat (List ℕ) p.2).getD 1 0 :=
    (Primrec.list_getD 0).comp hu (Primrec.const 1)
  have hB : Primrec fun p : ℕ × ℕ => (ofNat (List ℕ) p.2).getD 3 0 :=
    (Primrec.list_getD 0).comp hu (Primrec.const 3)
  have hk : Primrec fun p : ℕ × ℕ =>
      stageOf p.1 ((ofNat (List ℕ) p.2).getD 1 0) ((ofNat (List ℕ) p.2).getD 3 0) :=
    Primrec.nat_add.comp (Primrec.succ.comp Primrec.fst)
      (Primrec.nat_add.comp hL (Primrec.nat_mul.comp (Primrec.const 2) hB))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hk) (Primrec.const 4)

private theorem primrec₂_bound₂ : Primrec₂ bound₂ := by
  have hu : Primrec fun p : ℕ × ℕ => ofNat (List ℕ) p.2 :=
    (Primrec.ofNat (List ℕ)).comp Primrec.snd
  have hL : Primrec fun p : ℕ × ℕ => (ofNat (List ℕ) p.2).getD 1 0 :=
    (Primrec.list_getD 0).comp hu (Primrec.const 1)
  have hB : Primrec fun p : ℕ × ℕ => (ofNat (List ℕ) p.2).getD 3 0 :=
    (Primrec.list_getD 0).comp hu (Primrec.const 3)
  have hk : Primrec fun p : ℕ × ℕ =>
      stageOf p.1 ((ofNat (List ℕ) p.2).getD 1 0) ((ofNat (List ℕ) p.2).getD 3 0) :=
    Primrec.nat_add.comp (Primrec.succ.comp Primrec.fst)
      (Primrec.nat_add.comp hL (Primrec.nat_mul.comp (Primrec.const 2) hB))
  have hmax : Primrec fun p : ℕ × ℕ =>
      maxIdx (ofNat (List (ℕ × ℕ)) ((ofNat (List ℕ) p.2).getD
        (2 * stageOf p.1 ((ofNat (List ℕ) p.2).getD 1 0)
          ((ofNat (List ℕ) p.2).getD 3 0)) 0)) :=
    primrec_maxIdx.comp ((Primrec.ofNat (List (ℕ × ℕ))).comp
      ((Primrec.list_getD 0).comp hu
        (Primrec.nat_mul.comp (Primrec.const 2) hk)))
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.const 2)
          (Primrec₂.natPair.comp hmax (Primrec.succ.comp Primrec.fst))))
      (Primrec.const 2))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hk) (Primrec.const 4))

/-! #### The oracle-free postprocessor -/

/-- The decoded stage-3 prefix of the packed input `w = Nat.pair n (encode prefix)`. -/
private def prefList (w : ℕ) : List ℕ := ofNat (List ℕ) w.unpair.2

/-- The stage recomputed from the prefix heads. -/
private def stageIdx (w : ℕ) : ℕ :=
  stageOf w.unpair.1 ((prefList w).getD 1 0) ((prefList w).getD 3 0)

/-- The decoded atom list, read at coordinate `2 · stageIdx w` of the prefix. -/
private def atomListOf (w : ℕ) : List (ℕ × ℕ) :=
  ofNat (List (ℕ × ℕ)) ((prefList w).getD (2 * stageIdx w) 0)

/-- The interleaved coordinate of the integrand value at dense index `m`, value
precision `n + 1` (with `n = w.unpair.1`). -/
private def valPos (w m : ℕ) : ℕ := 2 * (2 + Nat.pair m (w.unpair.1 + 1)) + 1

/-- The denominator code: sum of clamped weight codes. -/
private def denCode (w : ℕ) : ℕ := sumCode ((atomListOf w).map fun pr => clampCode pr.2)

/-- The numerator code: sum of clamped-weight·value codes. -/
private def numCode (w : ℕ) : ℕ :=
  sumCode ((atomListOf w).map fun pr =>
    mulCode (clampCode pr.2) ((prefList w).getD (valPos w pr.1) 0))

/-- The oracle-free postprocessor of the generic integration realizer. -/
private def integPost (w : ℕ) : ℕ :=
  if (denCode w).unpair.1.unpair.1 ≤ (denCode w).unpair.1.unpair.2 then
    (prefList w).getD (valPos w 0) 0
  else divCode (numCode w) (denCode w)

private theorem primrec_prefList : Primrec prefList :=
  (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd

private theorem primrec_stageIdx : Primrec stageIdx :=
  Primrec.nat_add.comp (Primrec.succ.comp primrec_unpairFst)
    (Primrec.nat_add.comp ((Primrec.list_getD 0).comp primrec_prefList (Primrec.const 1))
      (Primrec.nat_mul.comp (Primrec.const 2)
        ((Primrec.list_getD 0).comp primrec_prefList (Primrec.const 3))))

private theorem primrec_atomListOf : Primrec atomListOf :=
  (Primrec.ofNat (List (ℕ × ℕ))).comp ((Primrec.list_getD 0).comp primrec_prefList
    (Primrec.nat_mul.comp (Primrec.const 2) primrec_stageIdx))

private theorem primrec_denCode : Primrec denCode :=
  primrec_sumCode.comp (Primrec.list_map primrec_atomListOf
    ((primrec_clampCode.comp (Primrec.snd.comp Primrec.snd)).to₂))

private theorem primrec_numCode : Primrec numCode :=
  primrec_sumCode.comp (Primrec.list_map primrec_atomListOf
    ((primrec₂_mulCode.comp (primrec_clampCode.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.list_getD 0).comp (primrec_prefList.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.nat_add.comp (Primrec.const 2)
            (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd)
              (Primrec.succ.comp (primrec_unpairFst.comp Primrec.fst)))))))).to₂))

private theorem primrec_integPost : Primrec integPost := by
  have hdenA : Primrec fun w : ℕ => (denCode w).unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp primrec_denCode
  have hdenB : Primrec fun w : ℕ => (denCode w).unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp primrec_denCode
  have hzero : Primrec fun w : ℕ => (prefList w).getD (valPos w 0) 0 :=
    (Primrec.list_getD 0).comp primrec_prefList
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp (Primrec.const 2)
          (Primrec₂.natPair.comp (Primrec.const 0)
            (Primrec.succ.comp primrec_unpairFst)))))
  exact Primrec.ite (Primrec.nat_le.comp hdenA hdenB) hzero
    (primrec₂_divCode.comp primrec_numCode primrec_denCode)

/-! ### Correctness of the postprocessor on interleaved names -/

/-- The chained postprocessor value on `Baire.interleave M Φ` is exactly the rational
`integralApprox Φ l (n + 1)` for the stage-`stageOf n L B` atom list `l`. -/
private theorem ratOfCode_postValue (M Φ : Baire) {L B : ℕ}
    (hL : Φ 0 = L) (hB : Φ 1 = B) (n : ℕ) :
    ratOfCode (integPost (Nat.pair n (encode (streamTake (Baire.interleave M Φ)
        (bound₂ n (encode (streamTake (Baire.interleave M Φ)
          (bound₁ n (encode (streamTake (Baire.interleave M Φ) 4))))))))))
      = integralApprox Φ (ofNat (List (ℕ × ℕ)) (M (stageOf n L B))) (n + 1) := by
  set F : Baire := Baire.interleave M Φ with hF_def
  have hF1 : F 1 = L := by
    have h := Baire.interleave_odd M Φ 0
    rw [hF_def]
    simpa [hL] using h
  have hF3 : F 3 = B := by
    have h := Baire.interleave_odd M Φ 1
    rw [hF_def]
    simpa [hB] using h
  set k : ℕ := stageOf n L B with hk_def
  set l : List (ℕ × ℕ) := ofNat (List (ℕ × ℕ)) (M k) with hl_def
  have hFk : F (2 * k) = M k := Baire.interleave_even M Φ k
  have hb1 : bound₁ n (encode (streamTake F 4)) = 2 * k + 4 := by
    simp only [bound₁, ofNat_encode]
    rw [streamTake_getD F (by omega : (1 : ℕ) < 4),
      streamTake_getD F (by omega : (3 : ℕ) < 4), hF1, hF3]
  have hb2 : bound₂ n (encode (streamTake F (2 * k + 4)))
      = 2 * (2 + Nat.pair (maxIdx l) (n + 1)) + 2 + (2 * k + 4) := by
    simp only [bound₂, ofNat_encode]
    rw [streamTake_getD F (by omega : (1 : ℕ) < 2 * k + 4),
      streamTake_getD F (by omega : (3 : ℕ) < 2 * k + 4), hF1, hF3,
      streamTake_getD F (by omega : 2 * k < 2 * k + 4), hFk]
  rw [hb1, hb2]
  set m₂ : ℕ := 2 * (2 + Nat.pair (maxIdx l) (n + 1)) + 2 + (2 * k + 4) with hm₂_def
  set w : ℕ := Nat.pair n (encode (streamTake F m₂)) with hw_def
  have hpl : prefList w = streamTake F m₂ := by
    simp [prefList, hw_def]
  have hn1 : w.unpair.1 = n := by simp [hw_def]
  have hsi : stageIdx w = k := by
    simp only [stageIdx, hpl, hn1]
    rw [streamTake_getD F (by omega : (1 : ℕ) < m₂),
      streamTake_getD F (by omega : (3 : ℕ) < m₂), hF1, hF3]
  have hal : atomListOf w = l := by
    simp only [atomListOf, hsi, hpl]
    rw [streamTake_getD F (by omega : 2 * k < m₂), hFk]
  have hval : ∀ pr : ℕ × ℕ, pr ∈ l →
      (streamTake F m₂).getD (2 * (2 + Nat.pair pr.1 (n + 1)) + 1) 0
        = Φ (2 + Nat.pair pr.1 (n + 1)) := by
    intro pr hpr
    have hple : Nat.pair pr.1 (n + 1) ≤ Nat.pair (maxIdx l) (n + 1) :=
      pair_le_pair_left (fst_le_maxIdx hpr) _
    rw [streamTake_getD F (by omega : 2 * (2 + Nat.pair pr.1 (n + 1)) + 1 < m₂)]
    exact Baire.interleave_odd M Φ _
  have hval0 : (streamTake F m₂).getD (2 * (2 + Nat.pair 0 (n + 1)) + 1) 0
      = Φ (2 + Nat.pair 0 (n + 1)) := by
    have hple : Nat.pair 0 (n + 1) ≤ Nat.pair (maxIdx l) (n + 1) :=
      pair_le_pair_left (Nat.zero_le _) _
    rw [streamTake_getD F (by omega : 2 * (2 + Nat.pair 0 (n + 1)) + 1 < m₂)]
    exact Baire.interleave_odd M Φ _
  have hden : ratOfCode (sumCode (l.map fun pr => clampCode pr.2)) = wSumL l := by
    rw [ratOfCode_sumCode, List.map_map, wSumL]
    exact congrArg List.sum (List.map_congr_left fun pr _ => by
      change ratOfCode (clampCode pr.2) = wRaw pr.2
      rw [wRaw_eq_ratOfCode_clampCode])
  have htest : ((sumCode (l.map fun pr => clampCode pr.2)).unpair.1.unpair.1
        ≤ (sumCode (l.map fun pr => clampCode pr.2)).unpair.1.unpair.2)
      ↔ wSumL l = 0 := by
    rw [← ratOfCode_nonpos_iff, hden]
    exact ⟨fun h => le_antisymm h (wSumL_nonneg l), fun h => le_of_eq h⟩
  simp only [integPost, denCode, numCode, valPos, hal, hpl, hn1]
  by_cases h0 : wSumL l = 0
  · rw [if_pos (htest.mpr h0), hval0, integralApprox, if_pos h0]
  · rw [if_neg fun hc => h0 (htest.mp hc)]
    have hmapnum : (l.map fun pr => mulCode (clampCode pr.2)
          ((streamTake F m₂).getD (2 * (2 + Nat.pair pr.1 (n + 1)) + 1) 0))
        = l.map fun pr => mulCode (clampCode pr.2) (Φ (2 + Nat.pair pr.1 (n + 1))) :=
      List.map_congr_left fun pr hpr => by rw [hval pr hpr]
    rw [hmapnum]
    have hpos : 0 < ratOfCode (sumCode (l.map fun pr => clampCode pr.2)) := by
      rw [hden]
      exact lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
    have hnum : ratOfCode (sumCode (l.map fun pr =>
          mulCode (clampCode pr.2) (Φ (2 + Nat.pair pr.1 (n + 1)))))
        = (l.map fun pr => wRaw pr.2 * ratOfCode (Φ (2 + Nat.pair pr.1 (n + 1)))).sum := by
      rw [ratOfCode_sumCode, List.map_map]
      exact congrArg List.sum (List.map_congr_left fun pr _ => by
        change ratOfCode (mulCode (clampCode pr.2) (Φ (2 + Nat.pair pr.1 (n + 1)))) = _
        rw [ratOfCode_mulCode, ← wRaw_eq_ratOfCode_clampCode])
    rw [ratOfCode_divCode _ _ ((ratOfCode_pos_iff _).mp hpos), hnum, hden,
      integralApprox, if_neg h0,
      listSum_map_eq_finSum l fun pr =>
        wRaw pr.2 * ratOfCode (Φ (2 + Nat.pair pr.1 (n + 1))),
      Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The generic bounded-Lipschitz integration realizer (private engine) -/

section MainTheorem

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

/-- **Generic bounded-Lipschitz integration engine**: a single total oracle code which,
fed the interleaving (measure even, integrand odd) of a weak measure name — a
fast-Cauchy stream `M` of atomic indices,
`levyProkhorovDist μ (atomic P (M k)) ≤ (2⁻¹)^k` — with any bounded-Lipschitz integrand
name over `P`, outputs a `realRep` name of `∫ φ dμ`.  No completeness hypothesis; the
realizer code is independent of `X` and `P`. -/
private theorem exists_boundedLipschitzIntegration_realizer :
    ∃ c : OracleCode, (∀ (F : Baire) (v : ℕ), (c.eval F v).Dom) ∧
      ∀ (M Φ : Baire) (μ : ProbabilityMeasure X) (L B : ℕ) (φ : X → ℝ),
        (∀ k : ℕ, levyProkhorovDist μ.toMeasure (atomic P (M k)).toMeasure
          ≤ (2 : ℝ)⁻¹ ^ k) →
        IntegrandName P Φ L B φ →
        ∃ q ∈ c.evalStream (Baire.interleave M Φ),
          realRep.Names q (∫ x, φ x ∂μ.toMeasure) := by
  obtain ⟨c, hc⟩ := exists_prefixChainCode (b₀ := fun _ => 4) (b₁ := bound₁)
    (b₂ := bound₂) (g := integPost) (Primrec.const 4) primrec₂_bound₁ primrec₂_bound₂
    primrec_integPost
  refine ⟨c, fun F v => by rw [hc F v]; trivial, fun M Φ μ L B φ hM hname => ?_⟩
  refine ⟨fun v => integPost (Nat.pair v (encode (streamTake (Baire.interleave M Φ)
      (bound₂ v (encode (streamTake (Baire.interleave M Φ)
        (bound₁ v (encode (streamTake (Baire.interleave M Φ) 4))))))))),
    mem_evalStream.mpr fun v => by rw [hc (Baire.interleave M Φ) v]; exact Part.mem_some _,
    ?_⟩
  refine (realPresentation.cauchyRep_names_iff).mpr fun v => ?_
  change dist ((ratOfCode (integPost (Nat.pair v (encode (streamTake (Baire.interleave M Φ)
      (bound₂ v (encode (streamTake (Baire.interleave M Φ)
        (bound₁ v (encode (streamTake (Baire.interleave M Φ) 4)))))))))) : ℚ) : ℝ)
    (∫ x, φ x ∂μ.toMeasure) ≤ (2 : ℝ)⁻¹ ^ v
  rw [Real.dist_eq, ratOfCode_postValue M Φ hname.headL hname.headB v]
  set l : List (ℕ × ℕ) := ofNat (List (ℕ × ℕ)) (M (stageOf v L B)) with hl_def
  -- the atomic-layer estimate at value precision `v + 1`
  have h1 : |((integralApprox Φ l (v + 1) : ℚ) : ℝ)
        - ∫ y, φ y ∂(atomicOfList P l).toMeasure| ≤ (2 : ℝ)⁻¹ ^ (v + 1) :=
    abs_integralApprox_sub_integral_le P hname l (v + 1)
  -- the Prokhorov stability estimate at stage `stageOf v L B`
  have hato : (atomic P (M (stageOf v L B))) = atomicOfList P l := rfl
  have h2 : |(∫ y, φ y ∂(atomicOfList P l).toMeasure) - ∫ x, φ x ∂μ.toMeasure|
      ≤ ((L : ℝ) + 2 * B) * (2 : ℝ)⁻¹ ^ stageOf v L B := by
    have hgen := abs_integral_sub_integral_le_levyProkhorovDist
      μ.toMeasure (atomic P (M (stageOf v L B))).toMeasure hname.lip hname.bound
    rw [abs_sub_comm, hato] at hgen
    refine hgen.trans ?_
    have hcoe : (((L : ℕ) : ℝ≥0) : ℝ) = (L : ℝ) := by simp
    rw [hcoe]
    exact mul_le_mul_of_nonneg_left (hM (stageOf v L B)) (by positivity)
  -- the stage arithmetic: `(L + 2B) · (2⁻¹)^(v+1+(L+2B)) ≤ (2⁻¹)^(v+1)`
  have h3 : ((L : ℝ) + 2 * B) * (2 : ℝ)⁻¹ ^ stageOf v L B ≤ (2 : ℝ)⁻¹ ^ (v + 1) := by
    have hkey : ((L + 2 * B : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (L + 2 * B : ℕ) ≤ 1 := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
      exact_mod_cast Nat.lt_two_pow_self.le
    have hsplit : (2 : ℝ)⁻¹ ^ stageOf v L B
        = (2 : ℝ)⁻¹ ^ (v + 1) * (2 : ℝ)⁻¹ ^ (L + 2 * B : ℕ) := by
      rw [show stageOf v L B = v + 1 + (L + 2 * B) from rfl, pow_add]
    calc ((L : ℝ) + 2 * B) * (2 : ℝ)⁻¹ ^ stageOf v L B
        = (((L + 2 * B : ℕ) : ℝ) * (2 : ℝ)⁻¹ ^ (L + 2 * B : ℕ)) * (2 : ℝ)⁻¹ ^ (v + 1) := by
          rw [hsplit]
          push_cast
          ring
      _ ≤ 1 * (2 : ℝ)⁻¹ ^ (v + 1) := mul_le_mul_of_nonneg_right hkey (by positivity)
      _ = (2 : ℝ)⁻¹ ^ (v + 1) := one_mul _
  calc |((integralApprox Φ l (v + 1) : ℚ) : ℝ) - ∫ x, φ x ∂μ.toMeasure|
      ≤ |((integralApprox Φ l (v + 1) : ℚ) : ℝ)
            - ∫ y, φ y ∂(atomicOfList P l).toMeasure|
          + |(∫ y, φ y ∂(atomicOfList P l).toMeasure) - ∫ x, φ x ∂μ.toMeasure| :=
        abs_sub_le _ _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (v + 1) + (2 : ℝ)⁻¹ ^ (v + 1) := add_le_add h1 (h2.trans h3)
    _ = (2 : ℝ)⁻¹ ^ v * ((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) := by rw [pow_succ]; ring
    _ = (2 : ℝ)⁻¹ ^ v := by norm_num

end MainTheorem

/-! ### The bounded-Lipschitz carrier and its representation -/

/-- A **bounded Lipschitz function**: a real-valued function on `X` bundled with the mere
existence of natural-number Lipschitz and uniform bounds — exactly the certificates
`IntegrandName` consumes.  Opaque-structure style matching `RealizableFun`: the
certificate is propositional, so two bounded-Lipschitz functions with equal `toFun` are
equal. -/
structure BoundedLipschitzFun (X : Type*) [MetricSpace X] where
  /-- The underlying function. -/
  toFun : X → ℝ
  /-- Some natural-number Lipschitz constant and uniform bound certify the function. -/
  exists_bounds : ∃ L B : ℕ, LipschitzWith (L : ℝ≥0) toFun ∧ ∀ x, |toFun x| ≤ (B : ℝ)

section BLLayer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Apply a bounded Lipschitz function as a function. -/
instance : CoeFun (BoundedLipschitzFun X) fun _ => X → ℝ :=
  ⟨BoundedLipschitzFun.toFun⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- Extensionality: bounded Lipschitz functions with the same underlying function are
equal — the bounds certificate is proof-irrelevant. -/
@[ext]
theorem BoundedLipschitzFun.ext {f g : BoundedLipschitzFun X} (h : ∀ x, f x = g x) :
    f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  obtain rfl : f = g := funext h
  rfl

variable (P : ComputableMetricPresentation X)

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Single-valuedness of the integrand layout.**  Two bounded Lipschitz functions
sharing one name are equal: the value streams of the name converge to the values at the
dense points, so both functions agree on the dense set exactly; Lipschitz continuity
plus density (`DenseRange.equalizer`) extend the agreement everywhere. -/
private theorem blNames_unique {Φ : Baire} {f g : BoundedLipschitzFun X}
    (hf : IntegrandName P Φ (Φ 0) (Φ 1) f.toFun)
    (hg : IntegrandName P Φ (Φ 0) (Φ 1) g.toFun) : f = g := by
  have hdense : ∀ m, f.toFun (P.dense m) = g.toFun (P.dense m) := by
    intro m
    have hbound : ∀ n : ℕ,
        |f.toFun (P.dense m) - g.toFun (P.dense m)| ≤ 2 * ((2 : ℝ)⁻¹) ^ n := by
      intro n
      calc |f.toFun (P.dense m) - g.toFun (P.dense m)|
          ≤ |f.toFun (P.dense m) - ((ratOfCode (Φ (2 + Nat.pair m n)) : ℚ) : ℝ)|
              + |((ratOfCode (Φ (2 + Nat.pair m n)) : ℚ) : ℝ) - g.toFun (P.dense m)| :=
            abs_sub_le _ _ _
        _ = |((ratOfCode (Φ (2 + Nat.pair m n)) : ℚ) : ℝ) - f.toFun (P.dense m)|
              + |((ratOfCode (Φ (2 + Nat.pair m n)) : ℚ) : ℝ) - g.toFun (P.dense m)| := by
            rw [abs_sub_comm]
        _ ≤ (2 : ℝ)⁻¹ ^ n + (2 : ℝ)⁻¹ ^ n := add_le_add (hf.approx m n) (hg.approx m n)
        _ = 2 * ((2 : ℝ)⁻¹) ^ n := by ring
    have hlim : Filter.Tendsto (fun n : ℕ => 2 * ((2 : ℝ)⁻¹) ^ n) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num :
        ((2 : ℝ)⁻¹) < 1)).const_mul 2
    have hle : |f.toFun (P.dense m) - g.toFun (P.dense m)| ≤ 0 :=
      ge_of_tendsto' hlim hbound
    have h0 : |f.toFun (P.dense m) - g.toFun (P.dense m)| = 0 :=
      le_antisymm hle (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h0)
  have htofun : f.toFun = g.toFun :=
    P.denseRange.equalizer hf.lip.continuous hg.lip.continuous (funext hdense)
  exact BoundedLipschitzFun.ext fun x => congrFun htofun x

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The bounded-Lipschitz representation** over `P`: `Φ` names `f` exactly when `Φ` is
an `IntegrandName` of `f.toFun` with the name's own heads `L = Φ 0`, `B = Φ 1`.  The
heads carry SOME valid bounds; different names of the same function may carry different
bounds.  Well-defined via choice through the single-valuedness of the layout;
convention 2: a name that is not an integrand layout of any bounded Lipschitz function
stays invalid — there is no default point. -/
noncomputable def blRep : Representation (BoundedLipschitzFun X) where
  rep Φ := ⟨∃ f : BoundedLipschitzFun X, IntegrandName P Φ (Φ 0) (Φ 1) f.toFun,
    fun h => h.choose⟩
  onto f := by
    classical
    obtain ⟨L, B, hL, hB⟩ := f.exists_bounds
    have happrox : ∀ m n : ℕ, ∃ c : ℕ,
        |((ratOfCode c : ℚ) : ℝ) - f.toFun (P.dense m)| ≤ (2 : ℝ)⁻¹ ^ n := by
      intro m n
      obtain ⟨q, hq⟩ := exists_rat_near (f.toFun (P.dense m))
        (show (0 : ℝ) < (2 : ℝ)⁻¹ ^ n by positivity)
      obtain ⟨c, rfl⟩ := ratOfCode_surjective q
      exact ⟨c, by rw [abs_sub_comm]; exact hq.le⟩
    choose app happ using happrox
    set Φ : Baire := fun j =>
      if j = 0 then L else if j = 1 then B else app (j - 2).unpair.1 (j - 2).unpair.2
      with hΦ_def
    have hΦ0 : Φ 0 = L := by simp [hΦ_def]
    have hΦ1 : Φ 1 = B := by simp [hΦ_def]
    have hΦv : ∀ m n : ℕ, Φ (2 + Nat.pair m n) = app m n := by
      intro m n
      have h2 : 2 + Nat.pair m n - 2 = Nat.pair m n := by omega
      simp only [hΦ_def]
      rw [if_neg (by omega), if_neg (by omega), h2, Nat.unpair_pair]
    have hname : IntegrandName P Φ (Φ 0) (Φ 1) f.toFun :=
      { headL := rfl
        headB := rfl
        lip := by rw [hΦ0]; exact hL
        bound := by rw [hΦ1]; exact hB
        approx := fun m n => by rw [hΦv m n]; exact happ m n }
    have hdom : ∃ g : BoundedLipschitzFun X, IntegrandName P Φ (Φ 0) (Φ 1) g.toFun :=
      ⟨f, hname⟩
    exact ⟨Φ, hdom, blNames_unique P hdom.choose_spec hname⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- Names of `blRep` are exactly the integrand layouts with the name's own heads — the
frozen names characterization. -/
@[simp]
theorem blRep_names_iff {Φ : Baire} {f : BoundedLipschitzFun X} :
    (blRep P).Names Φ f ↔ IntegrandName P Φ (Φ 0) (Φ 1) f.toFun := by
  constructor
  · rintro ⟨hex, rfl⟩
    exact hex.choose_spec
  · intro h
    have hdom : ∃ g : BoundedLipschitzFun X, IntegrandName P Φ (Φ 0) (Φ 1) g.toFun :=
      ⟨f, h⟩
    exact ⟨hdom, blNames_unique P hdom.choose_spec h⟩

/-! ### The frozen operation: integration as a `ComputableMap` -/

/-- **Bounded-Lipschitz integration is a computable map** (the frozen operation):
`blRep P × weakMeasureRep P ⟶ realRep`, `(f, μ) ↦ ∫ f dμ`, over an arbitrary presented
metric space; no completeness hypothesis.  Realizer: the generic integration engine's
code precomposed (by oracle substitution) with the parity-swap stream code — product
names carry the integrand on the even track and the measure on the odd track, while the
engine consumes `Baire.interleave M Φ` (measure even, integrand odd). -/
theorem computableMap_integrateBL :
    ComputableMap ((blRep P).prod (weakMeasureRep P)) realRep
      fun q : BoundedLipschitzFun X × ProbabilityMeasure X =>
        ∫ x, q.1 x ∂q.2.toMeasure := by
  obtain ⟨c, -, hc⟩ := exists_boundedLipschitzIntegration_realizer P
  obtain ⟨cs, hcs⟩ :=
    Type2Computable.interleave type2Computable_oddPart type2Computable_evenPart
  refine ⟨c.subst cs, fun p q hpq => ?_⟩
  obtain ⟨hf, hμ⟩ := Representation.prod_names_iff.mp hpq
  have hname : IntegrandName P p.evenPart (p.evenPart 0) (p.evenPart 1) q.1.toFun :=
    (blRep_names_iff P).mp hf
  have hM : WeakMeasureNames P p.oddPart q.2 := (weakMeasureRep_names_iff P).mp hμ
  obtain ⟨r, hr, hrn⟩ := hc p.oddPart p.evenPart q.2 (p.evenPart 0) (p.evenPart 1)
    q.1.toFun hM hname
  have hs : Baire.interleave p.oddPart p.evenPart ∈ cs.evalStream p := by
    rw [OracleCode.computes_iff_evalStream.mp hcs p]
    exact Part.mem_some _
  refine ⟨r, ?_, hrn⟩
  rw [OracleCode.evalStream_subst hs]
  exact hr

end BLLayer

end ComputableAnalysis
