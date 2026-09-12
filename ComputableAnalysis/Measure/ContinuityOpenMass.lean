/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.REPredStages
import ComputableAnalysis.Measure.ContinuityOpen
import ComputableAnalysis.Metric.Real
import ComputableAnalysis.TypeTwo.Universal

/-!
# The mass of an effective continuity open

From a weak name of `µ` and an effective `µ`-continuity open, one fixed oracle code emits a
fast Cauchy name of `µ U` (`exists_contSetMassCode`). The mass is read off the atomic
approximants: the code accumulates the weights of those atoms it has *certified* to lie in an
inner approximation, by a dovetailed search over the presentation's `ltSemidec`. Whether an
atom lies in a ball is only semidecidable for a general presentation, so the accumulated
rational is a lower bound for the approximant's true mass, which is all the bracket of
`ContinuityOpen` needs.

This module provides the certificate as a first-order, primitive recursive **mask**: bit `i`
records whether atom `i` of a decoded atomic list has been certified inside the stage-`n`
inner approximation by fuel `t`, reading the open's name only through a finite prefix. It is
the input `exists_certifiedWeightCode` (in `WeakRepresentation`) accumulates over.

## Main definitions and results

* `maskOfList` — the little-endian bitmask of a Boolean list, with `testBit_maskOfList`.
* `thrCodeOfPrefix` — the coded shrunk radius `r k - 2⁻ⁿ`, read from a finite prefix.
* `exists_maskAtCode` — one primitive recursive mask that is sound (a set bit certifies
  membership), persistent in the fuel, and eventually complete on every atom genuinely inside.
* `ratBracket_of_certified`, `ratBracket_of_masks`, `exists_indices_gap` — the code-level
  bracket: any certified under-estimates on the two tracks, minus the LP error, bracket `µ U`,
  and coupled indices exist at which the bracket is arbitrarily tight.
* `exists_contSetMassCode` — the mass code: a packed search over level, stage and fuel until
  the exact coded-rational gap closes, then a prefix chain emitting the lower endpoint.

## Implementation notes

`thrCodeOfPrefix` is sealed (`local irreducible`) after its two lemmas so that the mask's
`Primrec` elaboration never unfolds the rational coding. Agreement with the stream is asserted
only at the exact prefix `streamTake u n`; behaviour on short prefixes is unspecified through
`getD`, which is what makes the mask total.
-/

open MeasureTheory Metric Encodable Denumerable

namespace ComputableAnalysis

open OracleCode

section ContinuityOpenMass

variable {X : Type} [MetricSpace X] (P : ComputableMetricPresentation X)

/-! ### Bitmasks of Boolean lists -/

/-- The bitmask of a finite Boolean list, little-endian, as a specialization of mathlib's
`Nat.ofDigits`. First-order, so `Primrec` can be stated; mathlib has no `Primrec` lemma for
`ofDigits`, which is what `primrec_maskOfList` adds. -/
def maskOfList (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map Bool.toNat)

theorem maskOfList_cons (b : Bool) (bs : List Bool) :
    maskOfList (b :: bs) = b.toNat + 2 * maskOfList bs := by
  simp [maskOfList, Nat.ofDigits_cons]

theorem maskOfList_eq_foldr (l : List Bool) :
    maskOfList l = l.foldr (fun b acc => b.toNat + 2 * acc) 0 := by
  induction l with
  | nil => rfl
  | cons b bs ih => rw [maskOfList_cons, ih, List.foldr_cons]

/-- Bit `i` is the `i`-th entry, `false` past the end: irrelevant high bits are harmless. -/
theorem testBit_maskOfList : ∀ (l : List Bool) (i : ℕ),
    (maskOfList l).testBit i = l.getD i false
  | [], i => by simp [maskOfList, Nat.zero_testBit]
  | b :: bs, 0 => by
      rw [maskOfList_cons, Nat.testBit_zero]
      cases b <;> simp [List.getD]
  | b :: bs, (i + 1) => by
      rw [maskOfList_cons, Nat.testBit_succ]
      have h : (b.toNat + 2 * maskOfList bs) / 2 = maskOfList bs := by
        cases b
        · change (0 + 2 * maskOfList bs) / 2 = maskOfList bs
          omega
        · change (1 + 2 * maskOfList bs) / 2 = maskOfList bs
          omega
      rw [h, testBit_maskOfList bs i]
      simp [List.getD]

theorem primrec_maskOfList : Primrec maskOfList := by
  have h : Primrec fun l : List Bool =>
      l.foldr (fun b acc => b.toNat + 2 * acc) 0 :=
    Primrec.list_foldr Primrec.id (Primrec.const 0)
      (Primrec.to₂ (Primrec.nat_add.comp
        (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))))
  refine h.of_eq fun l => ?_
  rw [maskOfList_eq_foldr]

/-! ### The coded shrunk radius, from a finite prefix -/

/-- The coded shrunk radius `r k - 2⁻ⁿ` read from a finite prefix of the open's name: the only
place the rational coding appears inside the mask. -/
private def thrCodeOfPrefix (pre : List ℕ) (n k : ℕ) : ℕ :=
  subCode ((pre.getD k 0).unpair.2) (halfPowCode n)

private theorem primrec_thrCodeOfPrefix :
    Primrec fun w : (List ℕ × ℕ) × ℕ => thrCodeOfPrefix w.1.1 w.1.2 w.2 :=
  primrec₂_subCode.comp
    (Primrec.snd.comp (Primrec.unpair.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)))
    (primrec_halfPowCode.comp (Primrec.snd.comp Primrec.fst))

/-- Agreement at the exact prefix, below its length. -/
private theorem ratOfCode_thrCodeOfPrefix (u : Baire) {n k : ℕ} (h : k < n) :
    ((ratOfCode (thrCodeOfPrefix (streamTake u n) n k) : ℚ) : ℝ)
      = ((ratOfCode ((u k).unpair.2) : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ n := by
  rw [thrCodeOfPrefix, streamTake_getD u h, ratOfCode_subCode, ratOfCode_halfPowCode]
  push_cast
  ring

attribute [local irreducible] thrCodeOfPrefix

/-! ### The mask -/

/-- The mask's inner test: is atom `j` certified by some ball among the first `n`, at fuel
`t`, reading the open's name only through the prefix? Named so its `Primrec` proof elaborates
against a determined goal. -/
private def macCert (g : ℕ × ℕ × ℕ → ℕ → Bool) (pre : List ℕ) (n j t : ℕ) : Bool :=
  (List.range n).any fun k =>
    g (j, (pre.getD k 0).unpair.1, thrCodeOfPrefix pre n k) t

private theorem primrec_macCert {g : ℕ × ℕ × ℕ → ℕ → Bool} (hgprim : Primrec₂ g) :
    Primrec fun w : (List ℕ × ℕ) × ℕ × ℕ => macCert g w.1.1 w.1.2 w.2.1 w.2.2 := by
  have hpre : Primrec fun y : ((List ℕ × ℕ) × ℕ × ℕ) × ℕ => y.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun y : ((List ℕ × ℕ) × ℕ × ℕ) × ℕ => y.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hj : Primrec fun y : ((List ℕ × ℕ) × ℕ × ℕ) × ℕ => y.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec fun y : ((List ℕ × ℕ) × ℕ × ℕ) × ℕ => y.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec fun y : ((List ℕ × ℕ) × ℕ × ℕ) × ℕ => y.2 := Primrec.snd
  exact primrec_list_any (Primrec.list_range.comp (Primrec.snd.comp Primrec.fst))
    ((hgprim.comp
      (Primrec.pair hj
        (Primrec.pair
          (Primrec.fst.comp (Primrec.unpair.comp ((Primrec.list_getD 0).comp hpre hk)))
          (primrec_thrCodeOfPrefix.comp (Primrec.pair (Primrec.pair hpre hn) hk))))
      ht).to₂)

/-- The finite-prefix mask: bit `i` records whether atom `i` of the decoded list is
certified. -/
private def macOf (g : ℕ × ℕ × ℕ → ℕ → Bool) (l : List (ℕ × ℕ)) (pre : List ℕ) (n t : ℕ) : ℕ :=
  maskOfList ((List.range l.length).map fun i => macCert g pre n (l.getD i (0, 0)).1 t)

private theorem primrec_macOf {g : ℕ × ℕ × ℕ → ℕ → Bool} (hgprim : Primrec₂ g) :
    Primrec fun w : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => macOf g w.1.1 w.1.2 w.2.1 w.2.2 := by
  have hl : Primrec fun y : ((List (ℕ × ℕ) × List ℕ) × ℕ × ℕ) × ℕ => y.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hpre : Primrec fun y : ((List (ℕ × ℕ) × List ℕ) × ℕ × ℕ) × ℕ => y.1.1.2 :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hn : Primrec fun y : ((List (ℕ × ℕ) × List ℕ) × ℕ × ℕ) × ℕ => y.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec fun y : ((List (ℕ × ℕ) × List ℕ) × ℕ × ℕ) × ℕ => y.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec fun y : ((List (ℕ × ℕ) × List ℕ) × ℕ × ℕ) × ℕ => y.2 := Primrec.snd
  refine primrec_maskOfList.comp (Primrec.list_map
    (Primrec.list_range.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))) ?_)
  exact ((primrec_macCert hgprim).comp
    (Primrec.pair (Primrec.pair hpre hn)
      (Primrec.pair (Primrec.fst.comp ((Primrec.list_getD ((0, 0) : ℕ × ℕ)).comp hl hi))
        ht))).to₂

/-- **The certified mask.** One primitive recursive mask over decoded atomic list, finite
prefix of the open's name, stage and fuel: a set bit certifies that the atom lies in the
stage-`n` inner approximation, bits persist as the fuel grows, and every atom genuinely inside
is certified at some common fuel. Stated on indices below the list length only; high bits
are irrelevant and ignored by the accumulator. -/
theorem exists_maskAtCode :
    ∃ mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ,
      Primrec (fun w : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac w.1.1 w.1.2 w.2.1 w.2.2) ∧
      ∀ (l : List (ℕ × ℕ)) (u : Baire) (n : ℕ),
        (∀ t i, i < l.length →
            (mac l (streamTake u n) n t).testBit i = true →
              P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
          ∧ (∀ t t' i, t ≤ t' → i < l.length →
              (mac l (streamTake u n) n t).testBit i = true →
              (mac l (streamTake u n) n t').testBit i = true)
          ∧ ∃ t, ∀ i, i < l.length →
              P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n →
              (mac l (streamTake u n) n t).testBit i = true := by
  classical
  obtain ⟨g, hgprim, hsound, hpers, hev⟩ := repred_exists_primrec_cumulative P.ltSemidec
  refine ⟨macOf g, primrec_macOf hgprim, fun l u n => ?_⟩
  -- bit `i` of the mask is exactly the certificate on atom `i`
  have hbit : ∀ (t i : ℕ), i < l.length →
      (macOf g l (streamTake u n) n t).testBit i
        = macCert g (streamTake u n) n (l.getD i (0, 0)).1 t := by
    intro t i hi
    rw [macOf, testBit_maskOfList, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
    rfl
  have hcert_sound : ∀ j t, macCert g (streamTake u n) n j t = true →
      P.dense j ∈ innerApprox P u n := by
    intro j t hc
    obtain ⟨k, hk, hgk⟩ := List.any_eq_true.mp hc
    have hkn : k < n := List.mem_range.mp hk
    refine (mem_innerApprox_iff u n _).mpr ⟨k, hkn, ?_⟩
    have h := hsound _ _ hgk
    rw [ratOfCode_thrCodeOfPrefix u hkn, streamTake_getD u hkn] at h
    exact h
  have hcert_pers : ∀ j t t', t ≤ t' → macCert g (streamTake u n) n j t = true →
      macCert g (streamTake u n) n j t' = true := by
    intro j t t' htt' hc
    obtain ⟨k, hk, hgk⟩ := List.any_eq_true.mp hc
    exact List.any_eq_true.mpr ⟨k, hk, hpers _ _ _ htt' hgk⟩
  have hcert_ev : ∀ j, P.dense j ∈ innerApprox P u n →
      ∃ t, macCert g (streamTake u n) n j t = true := by
    intro j hj
    obtain ⟨k, hkn, hdist⟩ := (mem_innerApprox_iff u n _).mp hj
    have hp : dist (P.dense j) (P.dense (((streamTake u n).getD k 0).unpair.1))
        < ((ratOfCode (thrCodeOfPrefix (streamTake u n) n k) : ℚ) : ℝ) := by
      rw [ratOfCode_thrCodeOfPrefix u hkn, streamTake_getD u hkn]
      exact hdist
    obtain ⟨t, ht⟩ := hev (j, ((streamTake u n).getD k 0).unpair.1,
      thrCodeOfPrefix (streamTake u n) n k) hp
    exact ⟨t, List.any_eq_true.mpr ⟨k, List.mem_range.mpr hkn, ht⟩⟩
  refine ⟨fun t i hi hset => hcert_sound _ t ((hbit t i hi) ▸ hset),
    fun t t' i htt' hi hset => ?_, ?_⟩
  · rw [hbit t' i hi]
    exact hcert_pers _ _ _ htt' ((hbit t i hi) ▸ hset)
  · set L : List ℕ := ((List.range l.length).map fun i => (l.getD i (0, 0)).1).filter
      fun j => decide (P.dense j ∈ innerApprox P u n) with hL
    have hLp : ∀ j ∈ L, P.dense j ∈ innerApprox P u n := by
      intro j hj
      rw [hL, List.mem_filter] at hj
      exact of_decide_eq_true hj.2
    obtain ⟨t, ht⟩ := exists_common_stage_of_persistent hcert_pers hcert_ev L hLp
    refine ⟨t, fun i hi hmem => ?_⟩
    rw [hbit t i hi]
    refine ht _ ?_
    rw [hL, List.mem_filter]
    exact ⟨List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, decide_eq_true hmem⟩

end ContinuityOpenMass

section ContinuityOpenMassSearch

variable {X : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {P : ComputableMetricPresentation X}

/-! ### The code-level bracket and the packed search

The search operates on exact coded-rational endpoints computed from finite prefixes, with a
primitive recursive comparison; convergence of the bracket is used only for termination. A
candidate packs the inner-approximation level, the weak-name stage and the dovetail fuel; the
search returns the least packed natural, which carries no semantic ordering, so soundness is
proved for every successful candidate. -/

omit [BorelSpace X] in
private theorem toReal_full {μ : ProbabilityMeasure X} {uv : Baire} (h : ContinuityOpenNames P μ
    uv) :
    (μ.toMeasure (openOf P uv.evenPart)).toReal
      + (μ.toMeasure (openOf P uv.oddPart)).toReal = 1 := by
  rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), h.full, ENNReal.toReal_one]

/-- **The bracket is valid for ANY certified under-estimates.** `cU` and `cV` are whatever the
dovetail has certified on the two tracks — any reals bounded above by the corresponding atomic
masses. Subtracting the LP error gives a genuine bracket for `µ U`.

This is the right formulation of the code-level bracket: the certification machinery
(accumulating weights of atoms certified inside, and its convergence) never enters the
VALIDITY proof, only the choice of `cU`/`cV`. So steps 1 and 4 of the chain are confined to
producing the endpoints, and cannot affect soundness. Certifying too little costs tightness,
never correctness — which is exactly why positive information alone suffices. -/
theorem ratBracket_of_certified {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {m n : ℕ} (hnm : n ≤ m) {cU cV : ℝ}
    (hcU : ENNReal.ofReal cU ≤ (atomic P (p (m + 1))).toMeasure (innerApprox P uv.evenPart n))
    (hcV : ENNReal.ofReal cV ≤ (atomic P (p (m + 1))).toMeasure (innerApprox P uv.oddPart n)) :
    cU - (2 : ℝ)⁻¹ ^ m ≤ (μ.toMeasure (openOf P uv.evenPart)).toReal ∧
      (μ.toMeasure (openOf P uv.evenPart)).toReal ≤ 1 - (cV - (2 : ℝ)⁻¹ ^ m) := by
  have hpow : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ m := by positivity
  -- a certified under-estimate is below the true mass plus the LP error, on either track
  have key : ∀ (w : Baire) (c : ℝ),
      ENNReal.ofReal c ≤ (atomic P (p (m + 1))).toMeasure (innerApprox P w n) →
      c ≤ (μ.toMeasure (openOf P w)).toReal + (2 : ℝ)⁻¹ ^ m := by
    intro w c hc
    have hchain := hc.trans (atomic_le_of_weakName hp (u := w) hnm)
    have hfin : μ.toMeasure (openOf P w) + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
    have hR := ENNReal.toReal_mono hfin hchain
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpow] at hR
    calc c ≤ max c 0 := le_max_left _ _
      _ = (ENNReal.ofReal c).toReal := ENNReal.toReal_ofReal'.symm
      _ ≤ _ := hR
  have hU := key uv.evenPart cU hcU
  have hV := key uv.oddPart cV hcV
  have hsum := toReal_full h
  exact ⟨by linarith, by linarith⟩

/-- **The bracket at explicit coded-rational endpoints.** Composing the certified-weight
interface with `ratBracket_of_certified`: given bitmasks whose set bits name atoms verified to
lie in the respective inner approximations, the two endpoints are literal `ratOfCode` values
and they bracket `µ U`.

This is the guardrail realized. The endpoints entering the gap test are `ratOfCode` applied to
codes the accumulator computed; no real quantity appears in anything the search evaluates, and
`ratBracket_of_certified` only certifies values already chosen. -/
theorem ratBracket_of_masks {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    (hacc : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    {m n : ℕ} (hnm : n ≤ m) (maskU maskV : ℕ)
    (hU : ∀ i, i < (atoms (p (m + 1))).length → maskU.testBit i = true →
      P.dense ((atoms (p (m + 1))).getD i (0, 0)).1 ∈ innerApprox P uv.evenPart n)
    (hV : ∀ i, i < (atoms (p (m + 1))).length → maskV.testBit i = true →
      P.dense ((atoms (p (m + 1))).getD i (0, 0)).1 ∈ innerApprox P uv.oddPart n) :
    ((ratOfCode (acc (p (m + 1)) maskU) : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ m
        ≤ (μ.toMeasure (openOf P uv.evenPart)).toReal ∧
      (μ.toMeasure (openOf P uv.evenPart)).toReal
        ≤ 1 - (((ratOfCode (acc (p (m + 1)) maskV) : ℚ) : ℝ) - (2 : ℝ)⁻¹ ^ m) := by
  refine ratBracket_of_certified hp h hnm ?_ ?_
  · exact hacc (p (m + 1)) maskU (innerApprox P uv.evenPart n)
      (measurableSet_innerApprox uv.evenPart n) hU
  · exact hacc (p (m + 1)) maskV (innerApprox P uv.oddPart n)
      (measurableSet_innerApprox uv.oddPart n) hV

/-- **The analytic choice of indices.** Everything the search needs to terminate, in the
explicit index discipline: pick `n` from convergence of BOTH inner approximations, take the
candidate level to be `L = n + 1`, then pick the stage `m` past `n` with error-budget slack.
`n < m` is what `le_atomic_of_weakName` consumes, and it delivers `L ≤ m` — exactly
`Q2Success`'s existing conjunct, which therefore needs no strengthening.

The bound is stated on the ATOMIC masses at level `L`, since those are what accumulator
exactness pins the coded endpoints to. The `2 * 2⁻ᵐ` is the two stages' Lévy–Prokhorov error,
one per track, as it appears in `q2Upper - q2Lower`. -/
theorem exists_indices_gap {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv) (j : ℕ) :
    ∃ n m : ℕ, n < m ∧
      (1 : ℝ) - ((atomic P (p (m + 1))).toMeasure (innerApprox P uv.oddPart (n + 1))).toReal
          - ((atomic P (p (m + 1))).toMeasure (innerApprox P uv.evenPart (n + 1))).toReal
          + 2 * (2 : ℝ)⁻¹ ^ m
        < (2 : ℝ)⁻¹ ^ j := by
  have hjpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ j := by positivity
  -- convergence of the two tracks fixes the level
  obtain ⟨n, hn⟩ :=
    ((tendsto_gap h).eventually (gt_mem_nhds (show (0:ℝ) < (2 : ℝ)⁻¹ ^ j / 2 by linarith))).exists
  -- the stage must clear the level and leave room for four copies of the LP error
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show (0:ℝ) < (2 : ℝ)⁻¹ ^ j / 8 by linarith)
    (by norm_num : (2:ℝ)⁻¹ < 1)
  refine ⟨n, max k (n + 1), lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _), ?_⟩
  set m := max k (n + 1) with hm
  have hmk : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ k :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left _ _)
  have hmpow : (2 : ℝ)⁻¹ ^ m < (2 : ℝ)⁻¹ ^ j / 8 := lt_of_le_of_lt hmk hk
  have hnm : n < m := lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)
  -- the two lower bounds, one per track
  have key : ∀ w : Baire, μ.toMeasure (innerApprox P w n)
      ≤ (atomic P (p (m + 1))).toMeasure (innerApprox P w (n + 1))
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) := fun w => le_atomic_of_weakName hp hnm
  have toRealKey : ∀ w : Baire, (μ.toMeasure (innerApprox P w n)).toReal
      ≤ ((atomic P (p (m + 1))).toMeasure (innerApprox P w (n + 1))).toReal
        + (2 : ℝ)⁻¹ ^ m := by
    intro w
    have hfin : (atomic P (p (m + 1))).toMeasure (innerApprox P w (n + 1))
        + ENNReal.ofReal ((2 : ℝ)⁻¹ ^ m) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
    have hR := ENNReal.toReal_mono hfin (key w)
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (2 : ℝ)⁻¹ ^ m)] at hR
  have hU := toRealKey uv.evenPart
  have hV := toRealKey uv.oddPart
  rw [lowerU, lowerV] at hn
  linarith

/-- Approximation level of a packed candidate. -/
private def q2Level (w : ℕ) : ℕ := w.unpair.1

/-- Weak-name stage of a packed candidate. -/
private def q2Stage (w : ℕ) : ℕ := w.unpair.2.unpair.1

/-- Dovetail fuel of a packed candidate. -/
private def q2Fuel (w : ℕ) : ℕ := w.unpair.2.unpair.2

@[simp] private theorem q2Level_pack (n m t : ℕ) : q2Level (Nat.pair n (Nat.pair m t)) = n := by
  simp [q2Level]

@[simp] private theorem q2Stage_pack (n m t : ℕ) : q2Stage (Nat.pair n (Nat.pair m t)) = m := by
  simp [q2Stage]

@[simp] private theorem q2Fuel_pack (n m t : ℕ) : q2Fuel (Nat.pair n (Nat.pair m t)) = t := by
  simp [q2Fuel]

/-- The mask the dovetail has certified on a track at a packed candidate.

The atom list is the package's `atoms`, not the raw decoded list: the mask is read at the
positions the accumulator sums over, which is what lets a complete mask be exact. -/
private def q2Mask (atoms : ℕ → List (ℕ × ℕ)) (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ)
    (p : Baire) (u : Baire) (w : ℕ) : ℕ :=
  mac (atoms (p (q2Stage w + 1))) (streamTake u (q2Level w)) (q2Level w) (q2Fuel w)

/-- **The decoded lower endpoint**: the certified weight of the atoms the dovetail has placed
inside `U`'s inner approximation, less the stage's Lévy–Prokhorov error. A rational computed
from codes — no real quantity occurs in anything the search evaluates. -/
private def q2Lower (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) : ℚ :=
  ratOfCode (acc (p (q2Stage w + 1)) (q2Mask atoms mac p uv.evenPart w)) - (2 : ℚ)⁻¹ ^ q2Stage w

/-- The decoded upper endpoint, obtained from the odd track through full mass. -/
private def q2Upper (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (w : ℕ) : ℚ :=
  1 - (ratOfCode (acc (p (q2Stage w + 1)) (q2Mask atoms mac p uv.oddPart w))
    - (2 : ℚ)⁻¹ ^ q2Stage w)

/-- **The packed search predicate.** Level below stage, and the decoded bracket narrower than
`2⁻ʲ`. Both conjuncts are decidable rational arithmetic on codes. -/
private def Q2Success (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (p uv : Baire) (j w : ℕ) : Prop :=
  q2Level w ≤ q2Stage w ∧
    q2Upper atoms acc mac p uv w - q2Lower atoms acc mac p uv w < (2 : ℚ)⁻¹ ^ j

/-- **The bracket at a packed candidate.** Needs only the level-below-stage conjunct; the gap
test is not used, so certifying too little costs tightness and never correctness. -/
private theorem q2_bracket {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    (hacc : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hmac : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    {w : ℕ} (hnm : q2Level w ≤ q2Stage w) :
    ((q2Lower atoms acc mac p uv w : ℚ) : ℝ) ≤ (μ.toMeasure (openOf P uv.evenPart)).toReal
      ∧ (μ.toMeasure (openOf P uv.evenPart)).toReal
        ≤ ((q2Upper atoms acc mac p uv w : ℚ) : ℝ) := by
  obtain ⟨hlo, hhi⟩ := ratBracket_of_masks hp h hacc hnm
    (q2Mask atoms mac p uv.evenPart w) (q2Mask atoms mac p uv.oddPart w)
    (fun i hi hbit => hmac _ uv.evenPart (q2Level w) (q2Fuel w) i hi hbit)
    (fun i hi hbit => hmac _ uv.oddPart (q2Level w) (q2Fuel w) i hi hbit)
  constructor
  · rw [q2Lower]
    push_cast
    exact hlo
  · rw [q2Upper]
    push_cast
    exact hhi

/-- **Soundness of the packed test.** Every successful candidate's lower endpoint is within
`2⁻ʲ` of the mass — which is exactly a fast-Cauchy approximant at precision `j`. -/
private theorem q2_sound {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    (hacc : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length → mask.testBit i = true →
        P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A)
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hmac : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    {j w : ℕ} (hw : Q2Success atoms acc mac p uv j w) :
    |(μ.toMeasure (openOf P uv.evenPart)).toReal - ((q2Lower atoms acc mac p uv w : ℚ) : ℝ)|
      ≤ (2 : ℝ)⁻¹ ^ j := by
  obtain ⟨hnm, hgap⟩ := hw
  obtain ⟨hlo, hhi⟩ := q2_bracket hp h hacc hmac hnm
  have hgapR : ((q2Upper atoms acc mac p uv w : ℚ) : ℝ)
      - ((q2Lower atoms acc mac p uv w : ℚ) : ℝ) < (2 : ℝ)⁻¹ ^ j := by
    have := (Rat.cast_lt (K := ℝ)).mpr hgap
    push_cast at this
    exact this
  rw [abs_le]
  constructor <;> linarith

/-- **Termination.** At every precision some packed candidate passes the test. Combined with
`q2_sound` — correctness for *every* successful candidate — this is exactly what the prefix
search needs, and nothing about which candidate it returns. -/
private theorem exists_q2Success {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (hexact : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length →
        (mask.testBit i = true ↔ P.dense ((atoms m).getD i (0, 0)).1 ∈ A)) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) = (atomic P m).toMeasure A)
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hsound : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    (hpers : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t t' i : ℕ), t ≤ t' → i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      (mac l (streamTake u n) n t').testBit i = true)
    (hcomp : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n : ℕ), ∃ t, ∀ i, i < l.length →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n →
      (mac l (streamTake u n) n t).testBit i = true)
    (j : ℕ) : ∃ w, Q2Success atoms acc mac p uv j w := by
  obtain ⟨n, m, hnm, hgap⟩ := exists_indices_gap hp h j
  obtain ⟨t₁, ht₁⟩ := hcomp (atoms (p (m + 1))) uv.evenPart (n + 1)
  obtain ⟨t₂, ht₂⟩ := hcomp (atoms (p (m + 1))) uv.oddPart (n + 1)
  -- persistence lifts each track's completeness fuel to their maximum
  have hcompl : ∀ (u : Baire) (t' : ℕ), t' ≤ max t₁ t₂ →
      (∀ i, i < (atoms (p (m + 1))).length →
        P.dense ((atoms (p (m + 1))).getD i (0, 0)).1 ∈ innerApprox P u (n + 1) →
        (mac (atoms (p (m + 1))) (streamTake u (n + 1)) (n + 1) t').testBit i = true) →
      ∀ i, i < (atoms (p (m + 1))).length →
        ((mac (atoms (p (m + 1))) (streamTake u (n + 1)) (n + 1) (max t₁ t₂)).testBit i = true ↔
          P.dense ((atoms (p (m + 1))).getD i (0, 0)).1 ∈ innerApprox P u (n + 1)) := by
    intro u t' hle hc i hi
    refine ⟨fun hb => hsound _ u (n + 1) (max t₁ t₂) i hi hb, fun hmem => ?_⟩
    exact hpers _ u (n + 1) t' (max t₁ t₂) i hle hi (hc i hi hmem)
  -- exactness on each track, moved from `ℝ≥0∞` to `ℝ` by nonnegativity
  have hval : ∀ u : Baire,
      (∀ i, i < (atoms (p (m + 1))).length →
        ((mac (atoms (p (m + 1))) (streamTake u (n + 1)) (n + 1) (max t₁ t₂)).testBit i = true ↔
          P.dense ((atoms (p (m + 1))).getD i (0, 0)).1 ∈ innerApprox P u (n + 1))) →
      ((ratOfCode (acc (p (m + 1))
            (mac (atoms (p (m + 1))) (streamTake u (n + 1)) (n + 1) (max t₁ t₂))) : ℚ) : ℝ)
        = ((atomic P (p (m + 1))).toMeasure (innerApprox P u (n + 1))).toReal := by
    intro u hu
    have heq := hexact (p (m + 1)) _ _ (measurableSet_innerApprox u (n + 1)) hu
    have := congrArg ENNReal.toReal heq
    simpa [ENNReal.toReal_ofReal (hnonneg _ _)] using this
  have hU := hval uv.evenPart (hcompl uv.evenPart t₁ (le_max_left _ _) ht₁)
  have hV := hval uv.oddPart (hcompl uv.oddPart t₂ (le_max_right _ _) ht₂)
  refine ⟨Nat.pair (n + 1) (Nat.pair m (max t₁ t₂)), ?_, ?_⟩
  · simp only [q2Level_pack, q2Stage_pack]
    omega
  · -- the rational gap, read off the two real equations
    have hR : ((q2Upper atoms acc mac p uv (Nat.pair (n + 1) (Nat.pair m (max t₁ t₂))) : ℚ) : ℝ)
        - ((q2Lower atoms acc mac p uv (Nat.pair (n + 1) (Nat.pair m (max t₁ t₂))) : ℚ) : ℝ)
        < (2 : ℝ)⁻¹ ^ j := by
      simp only [q2Upper, q2Lower, q2Mask, q2Level_pack, q2Stage_pack, q2Fuel_pack]
      push_cast
      rw [hU, hV]
      linarith
    refine (Rat.cast_lt (K := ℝ)).mp ?_
    push_cast
    exact hR

/-- The adaptive prefix length, in the builder's `(a, k)`-packed convention. The oracle head is
not needed, so the bound is non-adaptive — a special case the builder permits. -/
private def q2PrefixBound (v : ℕ) (_head : ℕ) : ℕ :=
  2 * q2Stage v.unpair.2 + 4 * q2Level v.unpair.2 + 4

/-- The weak-name lookup `p (q2Stage w + 1)` lies strictly inside the prefix. -/
private theorem lt_q2PrefixBound_stage (a w head : ℕ) :
    2 * (q2Stage w + 1) < q2PrefixBound (Nat.pair a w) head := by
  simp only [q2PrefixBound, Nat.unpair_pair]
  omega

/-- Every even-track lookup below the candidate's level lies strictly inside the prefix. -/
private theorem lt_q2PrefixBound_even (a w head : ℕ) {i : ℕ} (hi : i < q2Level w) :
    4 * i + 1 < q2PrefixBound (Nat.pair a w) head := by
  simp only [q2PrefixBound, Nat.unpair_pair]
  omega

/-- Every odd-track lookup below the candidate's level lies strictly inside the prefix. -/
private theorem lt_q2PrefixBound_odd (a w head : ℕ) {i : ℕ} (hi : i < q2Level w) :
    4 * i + 3 < q2PrefixBound (Nat.pair a w) head := by
  simp only [q2PrefixBound, Nat.unpair_pair]
  omega

private theorem primrec₂_q2PrefixBound : Primrec₂ q2PrefixBound := by
  have hw : Primrec fun x : ℕ × ℕ => x.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp Primrec.fst)
  have hlevel : Primrec fun x : ℕ × ℕ => q2Level x.1.unpair.2 :=
    Primrec.fst.comp (Primrec.unpair.comp hw)
  have hstage : Primrec fun x : ℕ × ℕ => q2Stage x.1.unpair.2 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.unpair.comp hw)))
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hstage)
      (Primrec.nat_mul.comp (Primrec.const 4) hlevel))
    (Primrec.const 4))

/-- The **atomic index** the candidate's stage names, read off an `F` prefix at its packed
coordinate: the value `p (q2Stage w + 1)`, which is what `acc` and `atoms` are indexed by.

Deliberately not called a stage. `q2Stage w` is the stage `m` itself; this is the weak name's
value there. Both are naturals and both occur around `acc`, so a swap would typecheck. -/
private def q2AtomicIndexOf (pre : List ℕ) (w : ℕ) : ℕ := pre.getD (2 * (q2Stage w + 1)) 0

/-- The even track's level-`q2Level w` prefix, read off an `F` prefix. -/
private def q2EvenOf (pre : List ℕ) (w : ℕ) : List ℕ :=
  (List.range (q2Level w)).map fun i => pre.getD (4 * i + 1) 0

/-- The odd track's level-`q2Level w` prefix, read off an `F` prefix. -/
private def q2OddOf (pre : List ℕ) (w : ℕ) : List ℕ :=
  (List.range (q2Level w)).map fun i => pre.getD (4 * i + 3) 0

private theorem q2AtomicIndexOf_streamTake {p uv : Baire} {w N : ℕ} (hN : 2 * (q2Stage w + 1) < N) :
    q2AtomicIndexOf (streamTake (Baire.interleave p uv) N) w = p (q2Stage w + 1) := by
  rw [q2AtomicIndexOf, streamTake_getD _ hN, Baire.interleave_even]

private theorem q2EvenOf_streamTake {p uv : Baire} {w N : ℕ}
    (hN : ∀ i, i < q2Level w → 4 * i + 1 < N) :
    q2EvenOf (streamTake (Baire.interleave p uv) N) w = streamTake uv.evenPart (q2Level w) := by
  refine List.ext_getElem (by simp [q2EvenOf, streamTake]) fun i h1 h2 => ?_
  have hi : i < q2Level w := by simpa [q2EvenOf] using h1
  simp only [q2EvenOf, List.getElem_map, List.getElem_range]
  rw [streamTake_getD _ (hN i hi), show 4 * i + 1 = 2 * (2 * i) + 1 by ring,
    Baire.interleave_odd]
  simp [streamTake]

private theorem q2OddOf_streamTake {p uv : Baire} {w N : ℕ}
    (hN : ∀ i, i < q2Level w → 4 * i + 3 < N) :
    q2OddOf (streamTake (Baire.interleave p uv) N) w = streamTake uv.oddPart (q2Level w) := by
  refine List.ext_getElem (by simp [q2OddOf, streamTake]) fun i h1 h2 => ?_
  have hi : i < q2Level w := by simpa [q2OddOf] using h1
  simp only [q2OddOf, List.getElem_map, List.getElem_range]
  rw [streamTake_getD _ (hN i hi), show 4 * i + 3 = 2 * (2 * i + 1) + 1 by ring,
    Baire.interleave_odd]
  simp [streamTake]

/-- The even track's certified-weight code, read off an `F` prefix. -/
private def q2CertUCode (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : RatCode :=
  acc (q2AtomicIndexOf pre w)
    (mac (atoms (q2AtomicIndexOf pre w)) (q2EvenOf pre w) (q2Level w) (q2Fuel w))

private theorem q2CertUCode_streamTake {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {p uv : Baire} {w N : ℕ}
    (h1 : 2 * (q2Stage w + 1) < N) (h2 : ∀ i, i < q2Level w → 4 * i + 1 < N) :
    q2CertUCode atoms acc mac (streamTake (Baire.interleave p uv) N) w
      = acc (p (q2Stage w + 1)) (q2Mask atoms mac p uv.evenPart w) := by
  rw [q2CertUCode, q2AtomicIndexOf_streamTake h1, q2EvenOf_streamTake h2, q2Mask]

/-- The odd track's certified-weight code, read off an `F` prefix. -/
private def q2CertVCode (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : RatCode :=
  acc (q2AtomicIndexOf pre w)
    (mac (atoms (q2AtomicIndexOf pre w)) (q2OddOf pre w) (q2Level w) (q2Fuel w))

private theorem q2CertVCode_streamTake {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {p uv : Baire} {w N : ℕ}
    (h1 : 2 * (q2Stage w + 1) < N) (h3 : ∀ i, i < q2Level w → 4 * i + 3 < N) :
    q2CertVCode atoms acc mac (streamTake (Baire.interleave p uv) N) w
      = acc (p (q2Stage w + 1)) (q2Mask atoms mac p uv.oddPart w) := by
  rw [q2CertVCode, q2AtomicIndexOf_streamTake h1, q2OddOf_streamTake h3, q2Mask]

/-- The gap code: `(1 + 2·2⁻ᵐ) - (cU + cV)`, which is `q2Upper - q2Lower` rearranged so that
the two Lévy–Prokhorov error terms are added rather than subtracted. -/
private def q2GapCode (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (w : ℕ) : RatCode :=
  subCode
    (addCode oneCode (addCode (halfPowCode (q2Stage w)) (halfPowCode (q2Stage w))))
    (addCode (q2CertUCode atoms acc mac pre w) (q2CertVCode atoms acc mac pre w))

private theorem ratOfCode_q2GapCode {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {p uv : Baire} {w N : ℕ}
    (h1 : 2 * (q2Stage w + 1) < N) (h2 : ∀ i, i < q2Level w → 4 * i + 1 < N)
    (h3 : ∀ i, i < q2Level w → 4 * i + 3 < N) :
    ratOfCode (q2GapCode atoms acc mac (streamTake (Baire.interleave p uv) N) w)
      = q2Upper atoms acc mac p uv w - q2Lower atoms acc mac p uv w := by
  rw [q2GapCode, ratOfCode_subCode, ratOfCode_addCode, ratOfCode_addCode, ratOfCode_addCode,
    ratOfCode_oneCode, ratOfCode_halfPowCode, q2CertUCode_streamTake h1 h2,
    q2CertVCode_streamTake h1 h3, q2Upper, q2Lower]
  ring

/-- The level-below-stage test: plain natural arithmetic on the packed candidate. -/
private def q2LevelOkB (w : ℕ) : Bool := decide (q2Level w ≤ q2Stage w)

/-- The gap test, entirely on rational CODES — the comparison is `primrecPred_ratLt`'s, so no
real quantity occurs anywhere in what the search evaluates. -/
private def q2GapOkB (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) : Bool :=
  decide (ratOfCode (q2GapCode atoms acc mac pre w) < ratOfCode (halfPowCode j))

/-- The combined test. -/
private def q2SuccessB (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (pre : List ℕ) (j w : ℕ) : Bool :=
  q2LevelOkB w && q2GapOkB atoms acc mac pre j w

/-- **Exact-prefix agreement.** On the prefix the builder actually supplies, the finite Boolean
test is equivalent to the semantic predicate — which is what lets `q2_sound` be applied to
whatever candidate the search returns. -/
private theorem q2SuccessB_eq_true_iff {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {p uv : Baire} (j w head : ℕ) :
    q2SuccessB atoms acc mac
        (streamTake (Baire.interleave p uv) (q2PrefixBound (Nat.pair j w) head)) j w = true
      ↔ Q2Success atoms acc mac p uv j w := by
  rw [q2SuccessB, Bool.and_eq_true, q2LevelOkB, q2GapOkB, decide_eq_true_iff,
    decide_eq_true_iff,
    ratOfCode_q2GapCode (lt_q2PrefixBound_stage j w head)
      (fun i hi => lt_q2PrefixBound_even j w head hi)
      (fun i hi => lt_q2PrefixBound_odd j w head hi),
    ratOfCode_halfPowCode, Q2Success]

private theorem primrec_q2Level : Primrec q2Level := Primrec.fst.comp Primrec.unpair

private theorem primrec_q2Stage : Primrec q2Stage :=
  Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem primrec_q2Fuel : Primrec q2Fuel :=
  Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

private theorem primrec_q2AtomicIndexOf : Primrec fun x : List ℕ × ℕ => q2AtomicIndexOf x.1 x.2 :=
  (Primrec.list_getD 0).comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (primrec_q2Stage.comp Primrec.snd)))

private theorem primrec_q2EvenOf : Primrec fun x : List ℕ × ℕ => q2EvenOf x.1 x.2 :=
  Primrec.list_map (Primrec.list_range.comp (primrec_q2Level.comp Primrec.snd))
    (((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd) (Primrec.const 1))).to₂)

private theorem primrec_q2OddOf : Primrec fun x : List ℕ × ℕ => q2OddOf x.1 x.2 :=
  Primrec.list_map (Primrec.list_range.comp (primrec_q2Level.comp Primrec.snd))
    (((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) Primrec.snd) (Primrec.const 3))).to₂)

/-- The even endpoint is primitive recursive. The mask computation is isolated from `acc`: the
tuple producer matches `mac`'s argument order exactly, the mask comes from the tupled
hypothesis, and only then is it paired with the atomic index for `acc`. -/
private theorem primrec_q2CertUCode {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => q2CertUCode atoms acc mac x.1 x.2 := by
  have htuple : Primrec fun x : List ℕ × ℕ =>
      ((atoms (q2AtomicIndexOf x.1 x.2), q2EvenOf x.1 x.2), (q2Level x.2, q2Fuel x.2)) :=
    ((hatoms.comp primrec_q2AtomicIndexOf).pair primrec_q2EvenOf).pair
      ((primrec_q2Level.comp Primrec.snd).pair (primrec_q2Fuel.comp Primrec.snd))
  have hmask : Primrec fun x : List ℕ × ℕ =>
      mac (atoms (q2AtomicIndexOf x.1 x.2)) (q2EvenOf x.1 x.2) (q2Level x.2) (q2Fuel x.2) :=
    hmac.comp htuple
  exact hacc.comp primrec_q2AtomicIndexOf hmask

/-- The odd endpoint, mirroring `primrec_q2CertUCode` through `q2OddOf`. -/
private theorem primrec_q2CertVCode {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => q2CertVCode atoms acc mac x.1 x.2 := by
  have htuple : Primrec fun x : List ℕ × ℕ =>
      ((atoms (q2AtomicIndexOf x.1 x.2), q2OddOf x.1 x.2), (q2Level x.2, q2Fuel x.2)) :=
    ((hatoms.comp primrec_q2AtomicIndexOf).pair primrec_q2OddOf).pair
      ((primrec_q2Level.comp Primrec.snd).pair (primrec_q2Fuel.comp Primrec.snd))
  have hmask : Primrec fun x : List ℕ × ℕ =>
      mac (atoms (q2AtomicIndexOf x.1 x.2)) (q2OddOf x.1 x.2) (q2Level x.2) (q2Fuel x.2) :=
    hmac.comp htuple
  exact hacc.comp primrec_q2AtomicIndexOf hmask

/-- The gap code is primitive recursive: pure composition over the two endpoints, the stage's
error term, and the binary coded-arithmetic combinators. -/
private theorem primrec_q2GapCode {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun x : List ℕ × ℕ => q2GapCode atoms acc mac x.1 x.2 := by
  have hem : Primrec fun x : List ℕ × ℕ => halfPowCode (q2Stage x.2) :=
    primrec_halfPowCode.comp (primrec_q2Stage.comp Primrec.snd)
  exact primrec₂_subCode.comp
    (primrec₂_addCode.comp (Primrec.const oneCode) (primrec₂_addCode.comp hem hem))
    (primrec₂_addCode.comp (primrec_q2CertUCode hatoms hacc hmac)
      (primrec_q2CertVCode hatoms hacc hmac))

private theorem primrec_q2LevelOkB : Primrec q2LevelOkB :=
  (Primrec.ite (Primrec.nat_le.comp primrec_q2Level primrec_q2Stage)
    (Primrec.const true) (Primrec.const false)).of_eq fun w => by
      by_cases h : q2Level w ≤ q2Stage w <;> simp [q2LevelOkB, h]

private theorem primrec_q2GapOkB {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun y : List ℕ × ℕ × ℕ => q2GapOkB atoms acc mac y.1 y.2.1 y.2.2 :=
  (Primrec.ite
    (primrecPred_ratLt
      ((primrec_q2GapCode hatoms hacc hmac).comp
        (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))
      (primrec_halfPowCode.comp (Primrec.fst.comp Primrec.snd)))
    (Primrec.const true) (Primrec.const false)).of_eq fun y => by
      by_cases h : ratOfCode (q2GapCode atoms acc mac y.1 y.2.2)
          < ratOfCode (halfPowCode y.2.1) <;> simp [q2GapOkB, h]

private theorem primrec_q2SuccessB {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec fun y : List ℕ × ℕ × ℕ => q2SuccessB atoms acc mac y.1 y.2.1 y.2.2 :=
  (Primrec.cond (primrec_q2LevelOkB.comp (Primrec.snd.comp Primrec.snd))
    (primrec_q2GapOkB hatoms hacc hmac) (Primrec.const false)).of_eq fun y => by
      cases h : q2LevelOkB y.2.2 <;> simp [q2SuccessB, h]

attribute [local irreducible] q2CertUCode q2CertVCode q2GapCode q2LevelOkB q2GapOkB q2SuccessB

/-- The packed test, in the builder's convention. -/
private def q2SearchG (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (v : ℕ) : ℕ :=
  cond (q2SuccessB atoms acc mac (ofNat (List ℕ) v.unpair.2)
    v.unpair.1.unpair.1 v.unpair.1.unpair.2) 0 1

/-- **Unpacking.** The packed call reduces to `q2SuccessB` on the components. -/
private theorem q2SearchG_pack {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (j w : ℕ) (pre : List ℕ) :
    q2SearchG atoms acc mac (Nat.pair (Nat.pair j w) (encode pre))
      = cond (q2SuccessB atoms acc mac pre j w) 0 1 := by
  rw [q2SearchG]
  simp [Denumerable.ofNat_encode]

/-- **Zero means success.** The convention bridge, stated separately from the projections. -/
private theorem q2SearchG_eq_zero_iff {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} (j w : ℕ) (pre : List ℕ) :
    q2SearchG atoms acc mac (Nat.pair (Nat.pair j w) (encode pre)) = 0
      ↔ q2SuccessB atoms acc mac pre j w = true := by
  rw [q2SearchG_pack]
  cases h : q2SuccessB atoms acc mac pre j w <;> simp

private theorem primrec_q2SearchG {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec (q2SearchG atoms acc mac) := by
  have hpre : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)
  have hj : Primrec fun v : ℕ => v.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hw : Primrec fun v : ℕ => v.unpair.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  exact Primrec.cond
    ((primrec_q2SuccessB hatoms hacc hmac).comp (hpre.pair (hj.pair hw)))
    (Primrec.const 0) (Primrec.const 1)

private theorem q2_search_dom {μ : ProbabilityMeasure X} {p uv : Baire}
    (hp : WeakMeasureNames P p μ) (h : ContinuityOpenNames P μ uv)
    {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    (hnonneg : ∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ))
    (hexact : ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
      (∀ i, i < (atoms m).length →
        (mask.testBit i = true ↔ P.dense ((atoms m).getD i (0, 0)).1 ∈ A)) →
      ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) = (atomic P m).toMeasure A)
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hsound : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n)
    (hpers : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t t' i : ℕ), t ≤ t' → i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      (mac l (streamTake u n) n t').testBit i = true)
    (hcomp : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n : ℕ), ∃ t, ∀ i, i < l.length →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n →
      (mac l (streamTake u n) n t).testBit i = true)
    {searchCode : OracleCode}
    (hdom : ∀ (F : Baire) (a : ℕ), (searchCode.eval F a).Dom ↔
      ∃ k, SearchSuccess q2PrefixBound (q2SearchG atoms acc mac) F a k)
    (j : ℕ) : (searchCode.eval (Baire.interleave p uv) j).Dom := by
  rw [hdom]
  obtain ⟨w, hw⟩ := exists_q2Success hp h hnonneg hexact hsound hpers hcomp j
  refine ⟨w, ?_⟩
  change q2SearchG atoms acc mac (Nat.pair (Nat.pair j w)
    (encode (streamTake (Baire.interleave p uv)
      (q2PrefixBound (Nat.pair j w) (Baire.interleave p uv 0))))) = 0
  rw [q2SearchG_eq_zero_iff, q2SuccessB_eq_true_iff]
  exact hw

/-- **5b: the paired stream.** `OracleCode.pair OracleCode.query searchCode` carries the
original oracle and the witness stream side by side: `R i = Nat.pair (F i) (witness i)`. The
choice-free constructor, so the wire format is transparent rather than an opaque interleaving.
Totality of the right component is exactly `q2_search_dom`. -/
private theorem q2_paired_mem {searchCode : OracleCode} {F : Baire}
    (hdom : ∀ j, (searchCode.eval F j).Dom) :
    (fun j => Nat.pair (F j) ((searchCode.eval F j).get (hdom j)))
      ∈ (OracleCode.pair OracleCode.query searchCode).evalStream F := by
  refine OracleCode.mem_evalStream.mpr fun j => ?_
  have hs : searchCode.eval F j = Part.some ((searchCode.eval F j).get (hdom j)) :=
    Part.eq_some_iff.mpr (Part.get_mem _)
  rw [OracleCode.eval_pair_some (OracleCode.eval_query F j) hs]
  exact Part.mem_some _

/-- Recover the original-oracle prefix from a paired prefix. -/
private def q2OrigOf (preR : List ℕ) : List ℕ := preR.map fun v => v.unpair.1

/-- Read the witness recorded at coordinate `j` of a paired prefix. -/
private def q2WitnessOf (preR : List ℕ) (j : ℕ) : ℕ := (preR.getD j 0).unpair.2

private theorem q2OrigOf_streamTake_paired (F : Baire) (wit : ℕ → ℕ) (N : ℕ) :
    q2OrigOf (streamTake (fun i => Nat.pair (F i) (wit i)) N) = streamTake F N := by
  refine List.ext_getElem (by simp [q2OrigOf, streamTake]) fun i h1 h2 => ?_
  simp [q2OrigOf, streamTake]

private theorem q2WitnessOf_streamTake_paired (F : Baire) (wit : ℕ → ℕ) {N j : ℕ} (hj : j < N) :
    q2WitnessOf (streamTake (fun i => Nat.pair (F i) (wit i)) N) j = wit j := by
  rw [q2WitnessOf, streamTake_getD _ hj, Nat.unpair_pair]

/-- The chain's first bound: expose the witness at coordinate `j`. -/
private def q2ChainB0 (j : ℕ) : ℕ := j + 1

/-- The chain's adaptive bound. **Both terms are load-bearing**: `j + 1` preserves access to
witness coordinate `j`, and `q2PrefixBound` covers every original-oracle read the candidate
performs. Either alone typechecks and fails later. -/
private def q2ChainB1 (j v : ℕ) : ℕ :=
  max (j + 1) (q2PrefixBound (Nat.pair j (q2WitnessOf (ofNat (List ℕ) v) j)) 0)

/-- The chain's emitted value: the code of the candidate's LOWER endpoint. -/
private def q2ChainG (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode)
    (mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ) (v : ℕ) : ℕ :=
  subCode
    (q2CertUCode atoms acc mac (q2OrigOf (ofNat (List ℕ) v.unpair.2))
      (q2WitnessOf (ofNat (List ℕ) v.unpair.2) v.unpair.1))
    (halfPowCode (q2Stage (q2WitnessOf (ofNat (List ℕ) v.unpair.2) v.unpair.1)))

/-- **The chain emits the candidate's lower endpoint.** Both bridges land on the original `F`
prefix, so `q2CertUCode_streamTake` applies directly — the wire format never enters
the endpoint semantics. -/
private theorem ratOfCode_q2ChainG_paired {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ} {p uv : Baire} {wit : ℕ → ℕ} {j N : ℕ}
    (hj : j < N) (hN : q2PrefixBound (Nat.pair j (wit j)) 0 ≤ N) :
    ratOfCode (q2ChainG atoms acc mac (Nat.pair j
        (encode (streamTake (fun i => Nat.pair (Baire.interleave p uv i) (wit i)) N))))
      = q2Lower atoms acc mac p uv (wit j) := by
  have h1 : 2 * (q2Stage (wit j) + 1) < N :=
    lt_of_lt_of_le (lt_q2PrefixBound_stage j (wit j) 0) hN
  have h2 : ∀ i, i < q2Level (wit j) → 4 * i + 1 < N :=
    fun i hi => lt_of_lt_of_le (lt_q2PrefixBound_even j (wit j) 0 hi) hN
  rw [q2ChainG]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [q2WitnessOf_streamTake_paired _ _ hj, q2OrigOf_streamTake_paired,
    q2CertUCode_streamTake h1 h2, ratOfCode_subCode, ratOfCode_halfPowCode, q2Lower]

private theorem primrec_q2OrigOf : Primrec q2OrigOf :=
  Primrec.list_map Primrec.id ((Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to₂)

private theorem primrec₂_q2WitnessOf : Primrec₂ q2WitnessOf :=
  Primrec.snd.comp (Primrec.unpair.comp
    ((Primrec.list_getD 0).comp Primrec.fst Primrec.snd))

private theorem primrec_q2ChainB0 : Primrec q2ChainB0 := Primrec.succ

private theorem primrec₂_q2ChainB1 : Primrec₂ q2ChainB1 := by
  have hwit : Primrec fun x : ℕ × ℕ => q2WitnessOf (ofNat (List ℕ) x.2) x.1 :=
    primrec₂_q2WitnessOf.comp ((Primrec.ofNat (List ℕ)).comp Primrec.snd) Primrec.fst
  exact Primrec.nat_max.comp (Primrec.succ.comp Primrec.fst)
    (primrec₂_q2PrefixBound.comp (Primrec₂.natPair.comp Primrec.fst hwit)
      (Primrec.const 0))

private theorem primrec_q2ChainG {atoms : ℕ → List (ℕ × ℕ)} {acc : ℕ → ℕ → RatCode}
    {mac : List (ℕ × ℕ) → List ℕ → ℕ → ℕ → ℕ}
    (hatoms : Primrec atoms) (hacc : Primrec₂ acc)
    (hmac : Primrec fun v : (List (ℕ × ℕ) × List ℕ) × ℕ × ℕ => mac v.1.1 v.1.2 v.2.1 v.2.2) :
    Primrec (q2ChainG atoms acc mac) := by
  have hpreR : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)
  have hj : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hwit : Primrec fun v : ℕ => q2WitnessOf (ofNat (List ℕ) v.unpair.2) v.unpair.1 :=
    primrec₂_q2WitnessOf.comp hpreR hj
  exact primrec₂_subCode.comp
    ((primrec_q2CertUCode hatoms hacc hmac).comp ((primrec_q2OrigOf.comp hpreR).pair hwit))
    (primrec_halfPowCode.comp (primrec_q2Stage.comp hwit))

/-- **The mass of an effective continuity open.** From a weak name of `µ` and an effective
µ-continuity open pair, one
oracle code produces a fast Cauchy name of `µ U` — uniformly, the code being chosen before any
of `p`, `uv`, `µ`. -/
theorem exists_contSetMassCode :
    ∃ c : OracleCode, ∀ (p uv : Baire) (μ : ProbabilityMeasure X),
      WeakMeasureNames P p μ → ContinuityOpenNames P μ uv →
      ∃ r ∈ c.evalStream (Baire.interleave p uv),
        realRep.Names r (μ.toMeasure (openOf P uv.evenPart)).toReal := by
  classical
  obtain ⟨atoms, acc, hatoms, haccprim, hnonneg, haccsound, hexact⟩ :=
    exists_completeCertifiedWeightCode P
  obtain ⟨mac, hmacprim, hmacspec⟩ := exists_maskAtCode (P := P)
  have hsound : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t i : ℕ), i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n :=
    fun l u n t i hi hb => (hmacspec l u n).1 t i hi hb
  have hpers : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n t t' i : ℕ), t ≤ t' → i < l.length →
      (mac l (streamTake u n) n t).testBit i = true →
      (mac l (streamTake u n) n t').testBit i = true :=
    fun l u n t t' i htt' hi hb => (hmacspec l u n).2.1 t t' i htt' hi hb
  have hcomp : ∀ (l : List (ℕ × ℕ)) (u : Baire) (n : ℕ), ∃ t, ∀ i, i < l.length →
      P.dense (l.getD i (0, 0)).1 ∈ innerApprox P u n →
      (mac l (streamTake u n) n t).testBit i = true :=
    fun l u n => (hmacspec l u n).2.2
  obtain ⟨searchCode, hsearchmem, hsearchdom⟩ :=
    OracleCode.exists_prefixSearchCode primrec₂_q2PrefixBound
      (primrec_q2SearchG hatoms haccprim hmacprim)
  obtain ⟨chainCode, hchain⟩ :=
    OracleCode.exists_prefixChainCode primrec_q2ChainB0 primrec₂_q2ChainB1 primrec₂_q2ChainB1
      (primrec_q2ChainG hatoms haccprim hmacprim)
  refine ⟨chainCode.subst (OracleCode.pair OracleCode.query searchCode), ?_⟩
  intro p uv μ hp h
  have hdomj : ∀ j, (searchCode.eval (Baire.interleave p uv) j).Dom :=
    q2_search_dom hp h hnonneg hexact hsound hpers hcomp hsearchdom
  set wit : ℕ → ℕ := fun j => (searchCode.eval (Baire.interleave p uv) j).get (hdomj j)
    with hwitdef
  have hRmem : (fun i => Nat.pair (Baire.interleave p uv i) (wit i))
      ∈ (OracleCode.pair OracleCode.query searchCode).evalStream (Baire.interleave p uv) :=
    q2_paired_mem hdomj
  rw [OracleCode.evalStream_subst hRmem]
  set M : ℕ → ℕ := fun n => max (n + 1) (q2PrefixBound (Nat.pair n (wit n)) 0) with hMdef
  have hnM : ∀ n, n < M n := fun n => lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_left _ _)
  have hboundM : ∀ n, q2PrefixBound (Nat.pair n (wit n)) 0 ≤ M n := fun n => le_max_right _ _
  have hN1 : ∀ n, q2ChainB1 n (encode (streamTake
      (fun i => Nat.pair (Baire.interleave p uv i) (wit i)) (q2ChainB0 n))) = M n := by
    intro n
    rw [q2ChainB1, q2ChainB0]
    simp only [Denumerable.ofNat_encode]
    rw [q2WitnessOf_streamTake_paired _ wit (Nat.lt_succ_self n)]
  have hN2 : ∀ n, q2ChainB1 n (encode (streamTake
      (fun i => Nat.pair (Baire.interleave p uv i) (wit i)) (M n))) = M n := by
    intro n
    rw [q2ChainB1]
    simp only [Denumerable.ofNat_encode]
    rw [q2WitnessOf_streamTake_paired _ wit (hnM n)]
  refine ⟨fun n => q2ChainG atoms acc mac (Nat.pair n (encode (streamTake
    (fun i => Nat.pair (Baire.interleave p uv i) (wit i)) (M n)))), ?_, ?_⟩
  · refine OracleCode.mem_evalStream.mpr fun n => ?_
    rw [hchain, hN1 n, hN2 n]
    exact Part.mem_some _
  · refine realPresentation.cauchyRep_names_iff.mpr fun n => ?_
    -- the returned witness passes the test, hence satisfies `Q2Success`
    have hQ : Q2Success atoms acc mac p uv n (wit n) := by
      have hmem : wit n ∈ searchCode.eval (Baire.interleave p uv) n := Part.get_mem _
      have hss : q2SearchG atoms acc mac (Nat.pair (Nat.pair n (wit n))
          (encode (streamTake (Baire.interleave p uv)
            (q2PrefixBound (Nat.pair n (wit n)) (Baire.interleave p uv 0))))) = 0 :=
        ((hsearchmem (Baire.interleave p uv) n (wit n)).mp hmem).1
      rw [q2SearchG_eq_zero_iff, q2SuccessB_eq_true_iff] at hss
      exact hss
    have hval := ratOfCode_q2ChainG_paired (atoms := atoms) (acc := acc) (mac := mac)
      (p := p) (uv := uv) (wit := wit) (hnM n) (hboundM n)
    change dist ((ratOfCode (q2ChainG atoms acc mac (Nat.pair n (encode (streamTake
      (fun i => Nat.pair (Baire.interleave p uv i) (wit i)) (M n))))) : ℚ) : ℝ) _ ≤ _
    rw [hval, Real.dist_eq, abs_sub_comm]
    exact q2_sound hp h haccsound hsound hQ

end ContinuityOpenMassSearch

end ComputableAnalysis
