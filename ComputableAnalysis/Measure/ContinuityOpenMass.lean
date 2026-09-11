/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.REPredStages
import ComputableAnalysis.Measure.ContinuityOpen

/-!
# Certified masks over inner approximations

The mass of an effective continuity open is read off a weak name through the atomic
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
def thrCodeOfPrefix (pre : List ℕ) (n k : ℕ) : ℕ :=
  subCode ((pre.getD k 0).unpair.2) (halfPowCode n)

theorem primrec_thrCodeOfPrefix :
    Primrec fun w : (List ℕ × ℕ) × ℕ => thrCodeOfPrefix w.1.1 w.1.2 w.2 :=
  primrec₂_subCode.comp
    (Primrec.snd.comp (Primrec.unpair.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)))
    (primrec_halfPowCode.comp (Primrec.snd.comp Primrec.fst))

/-- Agreement at the exact prefix, below its length. -/
theorem ratOfCode_thrCodeOfPrefix (u : Baire) {n k : ℕ} (h : k < n) :
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
def macCert (g : ℕ × ℕ × ℕ → ℕ → Bool) (pre : List ℕ) (n j t : ℕ) : Bool :=
  (List.range n).any fun k =>
    g (j, (pre.getD k 0).unpair.1, thrCodeOfPrefix pre n k) t

theorem primrec_macCert {g : ℕ × ℕ × ℕ → ℕ → Bool} (hgprim : Primrec₂ g) :
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
def macOf (g : ℕ × ℕ × ℕ → ℕ → Bool) (l : List (ℕ × ℕ)) (pre : List ℕ) (n t : ℕ) : ℕ :=
  maskOfList ((List.range l.length).map fun i => macCert g pre n (l.getD i (0, 0)).1 t)

theorem primrec_macOf {g : ℕ × ℕ × ℕ → ℕ → Bool} (hgprim : Primrec₂ g) :
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

end ComputableAnalysis
