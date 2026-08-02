/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Principles.ChoiceTwo
import ComputableAnalysis.Weihrauch.Principles.WKLReduction
import ComputableAnalysis.Weihrauch.Principles.WKLClosedChoice

/-!
# `C₂.parallelize ≤sW C_Cantor`, and `LLPO.parallelize ≡sW WKL`

Countably many independent binary choices are a closed subset of Cantor space: instance
`n` constrains coordinate `n`, and a point avoiding every removed value is exactly a
simultaneous solution.

The compiled negative name reads coordinate `m` as a pair `(stage, wordCode)`. Let
`w := treeWordDecode m.unpair.2`. If `w` is empty the coordinate is the sentinel;
otherwise, writing `n := |w| - 1`, the coordinate forbids the cylinder of `w` exactly
when instance `n` removes `w`'s last bit at stage `m.unpair.1`. So one removal of bit `b`
from instance `n` forbids every length-`(n + 1)` cylinder ending in `b`, which is
precisely the set of points whose coordinate `n` is `b`.

**The empty word is gated explicitly.** Without the gate, `|w| - 1` truncates to `0` on
`w = []` and `cantorForbiddenWordCode []` forbids `cylinder [] = univ` — a single removal
at instance `0` would empty the space. The gate is a correctness condition, not a
convenience.

The semantic anchor `closedCantorSet_c2ParallelForbiddenName` is promise-free: it is an
identity of sets on every stream, so `C₂`'s at-most-one-answer promise enters only in
placing the compiled name in `C_Cantor`'s domain.

Assembling with the bridge of `WKLClosedChoice.lean` and the death-race reduction of
`WKLReduction.lean` gives `parallelize_llpo_equiv_wkl : LLPO.parallelize ≡sW WKL`.
-/

namespace ComputableAnalysis

open Encodable Denumerable

/-! ### The compiled negative name -/

/-- The last bit of a word; `false` on the empty word, which the compiled name gates
away. -/
def wordLastBit (w : List Bool) : Bool := w.getD (w.length - 1) false

/-- The negative name compiled from a parallel `C₂` name. Coordinate `m` decodes as a
pair `(stage, wordCode)`; the decoded word `w` is forbidden exactly when instance
`|w| - 1` removes `w`'s last bit at that stage. The empty word is gated: it would
otherwise forbid the whole space. -/
def c2ParallelForbiddenName (p : Baire) : Baire := fun m =>
  if (treeWordDecode m.unpair.2).length = 0 then 0
  else if p (Nat.pair ((treeWordDecode m.unpair.2).length - 1) m.unpair.1) =
      (wordLastBit (treeWordDecode m.unpair.2)).toNat + 1 then
    cantorForbiddenWordCode (treeWordDecode m.unpair.2)
  else 0

/-- A coordinate is non-sentinel exactly when its decoded word is nonempty and the
corresponding instance removes that word's last bit at that stage. -/
theorem c2ParallelForbiddenName_ne_zero_iff {p : Baire} {m : ℕ} :
    c2ParallelForbiddenName p m ≠ 0 ↔
      (treeWordDecode m.unpair.2).length ≠ 0 ∧
        p (Nat.pair ((treeWordDecode m.unpair.2).length - 1) m.unpair.1) =
          (wordLastBit (treeWordDecode m.unpair.2)).toNat + 1 := by
  rw [c2ParallelForbiddenName]
  by_cases h0 : (treeWordDecode m.unpair.2).length = 0
  · simp [h0]
  · by_cases h1 : p (Nat.pair ((treeWordDecode m.unpair.2).length - 1) m.unpair.1) =
        (wordLastBit (treeWordDecode m.unpair.2)).toNat + 1
    · simp [h0, h1, cantorForbiddenWordCode]
    · simp [h0, h1]

/-- A non-sentinel coordinate forbids exactly its decoded word. -/
theorem cantorForbiddenWord_c2ParallelForbiddenName {p : Baire} {m : ℕ}
    (h : c2ParallelForbiddenName p m ≠ 0) :
    cantorForbiddenWord (c2ParallelForbiddenName p) m =
      some (treeWordDecode m.unpair.2) := by
  obtain ⟨h0, h1⟩ := c2ParallelForbiddenName_ne_zero_iff.mp h
  refine cantorForbiddenWord_of_eq_code ?_
  rw [c2ParallelForbiddenName, if_neg h0, if_pos h1]

/-- **The semantic anchor**, promise-free: the presented closed set is exactly the set of
points solving every instance simultaneously. -/
theorem closedCantorSet_c2ParallelForbiddenName (p : Baire) :
    closedCantorSet (c2ParallelForbiddenName p) =
      {x : Cantor | ∀ n, C₂.accepts (Baire.track n p) (Bool.toNat (x n))} := by
  ext x
  simp only [closedCantorSet, Set.mem_setOf_eq, C₂.accepts_iff, Baire.track]
  constructor
  · intro hx n
    refine ⟨by cases x n <;> simp, fun s hs => ?_⟩
    -- the length-`(n + 1)` prefix of `x` is forbidden by the coordinate `(s, its code)`
    have hlen : (streamTake x (n + 1)).length = n + 1 := length_streamTake x (n + 1)
    have hlast : wordLastBit (streamTake x (n + 1)) = x n := by
      rw [wordLastBit, hlen, Nat.add_sub_cancel]
      exact streamTake_getD x (Nat.lt_succ_self n)
    set m : ℕ := Nat.pair s (treeWordCode (streamTake x (n + 1))) with hm
    have hu2 : treeWordDecode m.unpair.2 = streamTake x (n + 1) := by
      rw [hm, Nat.unpair_pair, treeWordDecode_treeWordCode]
    have hu1 : m.unpair.1 = s := by rw [hm, Nat.unpair_pair]
    have hne : c2ParallelForbiddenName p m ≠ 0 := by
      refine c2ParallelForbiddenName_ne_zero_iff.mpr ⟨by rw [hu2, hlen]; omega, ?_⟩
      rw [hu2, hu1, hlen, hlast, Nat.add_sub_cancel]
      exact hs
    have hforb := cantorForbiddenWord_c2ParallelForbiddenName hne
    rw [hu2] at hforb
    exact hx m _ hforb (mem_cylinder_streamTake x (n + 1))
  · intro hc m u hu hcyl
    have hne : c2ParallelForbiddenName p m ≠ 0 := by
      intro h0
      rw [cantorForbiddenWord_eq_none_iff.mpr h0] at hu
      simp at hu
    obtain ⟨h0, h1⟩ := c2ParallelForbiddenName_ne_zero_iff.mp hne
    have hforb := cantorForbiddenWord_c2ParallelForbiddenName hne
    rw [hu] at hforb
    have hue : u = treeWordDecode m.unpair.2 := Option.some_injective _ hforb
    -- `x` starts with `u`, so `u`'s last bit is coordinate `|u| - 1` of `x`
    have hpre : streamTake x u.length = u := mem_cylinder_iff.mp hcyl
    have hulen : u.length ≠ 0 := by rw [hue]; exact h0
    have hlast : wordLastBit u = x (u.length - 1) := by
      have h2 : u.getD (u.length - 1) false
          = (streamTake x u.length).getD (u.length - 1) false := by rw [hpre]
      rw [wordLastBit, h2]
      exact streamTake_getD x (by omega)
    rw [← hue, hlast] at h1
    exact absurd h1 ((hc (u.length - 1)).2 m.unpair.1)

/-- On a solvable parallel instance the presented set is nonempty: choose a solution at
each coordinate. -/
theorem c_Cantor_dom_c2ParallelForbiddenName {p : Baire}
    (hdom : ∀ n, ∃ i : ℕ, C₂.accepts (Baire.track n p) i) :
    C_Cantor.Dom (c2ParallelForbiddenName p) := by
  classical
  rw [C_Cantor.dom_iff, closedCantorSet_c2ParallelForbiddenName]
  choose i hi using hdom
  refine ⟨fun n => decide (i n = 1), fun n => ?_⟩
  obtain ⟨hle, hrem⟩ := C₂.accepts_iff.mp (hi n)
  have hval : Bool.toNat (decide (i n = 1)) = i n := by
    rcases Nat.eq_zero_or_pos (i n) with h | h
    · rw [h]; simp
    · rw [le_antisymm hle h]; simp
  rw [hval]
  exact hi n

/-! ### The preprocessor code

Coordinate `m` queries the parallel name at the single position
`Nat.pair (|treeWordDecode m.unpair.2| - 1) m.unpair.1`, computed from `m` alone, so one
prefix decides it. -/

/-- A single code compiles the negative name. -/
theorem exists_c2ParallelForbiddenCode : ∃ K : OracleCode, ∀ p : Baire,
    c2ParallelForbiddenName p ∈ K.evalStream p := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hword : Primrec fun v : ℕ => treeWordDecode v.unpair.1 :=
    primrec_treeWordDecode.comp hu1
  -- the single queried position, as a function of the output coordinate
  have hqpos : Primrec fun j : ℕ =>
      Nat.pair ((treeWordDecode j.unpair.2).length - 1) j.unpair.1 :=
    Primrec₂.natPair.comp
      (Primrec.nat_sub.comp
        (Primrec.list_length.comp (primrec_treeWordDecode.comp hu2)) (Primrec.const 1))
      hu1
  have hbound : Primrec₂ fun (j : ℕ) (_ : ℕ) =>
      Nat.pair ((treeWordDecode j.unpair.2).length - 1) j.unpair.1 + 1 :=
    (Primrec.succ.comp (hqpos.comp Primrec.fst)).to₂
  have hdecw : Primrec fun v : ℕ => treeWordDecode v.unpair.1.unpair.2 :=
    primrec_treeWordDecode.comp (hu2.comp hu1)
  have hlen : Primrec fun v : ℕ => (treeWordDecode v.unpair.1.unpair.2).length :=
    Primrec.list_length.comp hdecw
  have hlook : Primrec fun v : ℕ =>
      (ofNat (List ℕ) v.unpair.2).getD
        (Nat.pair ((treeWordDecode v.unpair.1.unpair.2).length - 1) v.unpair.1.unpair.1) 0 :=
    (Primrec.list_getD 0).comp ((Primrec.ofNat (List ℕ)).comp hu2) (hqpos.comp hu1)
  have hbit : Primrec fun v : ℕ =>
      (wordLastBit (treeWordDecode v.unpair.1.unpair.2)).toNat + 1 :=
    Primrec.succ.comp (Primrec.cond
      ((Primrec.list_getD false).comp hdecw (Primrec.nat_sub.comp hlen (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0))
  have hg : Primrec fun v : ℕ =>
      if (treeWordDecode v.unpair.1.unpair.2).length = 0 then 0
      else if (ofNat (List ℕ) v.unpair.2).getD
          (Nat.pair ((treeWordDecode v.unpair.1.unpair.2).length - 1) v.unpair.1.unpair.1) 0 =
          (wordLastBit (treeWordDecode v.unpair.1.unpair.2)).toNat + 1 then
        cantorForbiddenWordCode (treeWordDecode v.unpair.1.unpair.2)
      else 0 :=
    Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) (Primrec.const 0)
      (Primrec.ite (Primrec.eq.comp hlook hbit)
        (Primrec.succ.comp (primrec_treeWordCode.comp hdecw)) (Primrec.const 0))
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨K, fun p => OracleCode.mem_evalStream.mpr fun m => ?_⟩
  rw [hK p m, Part.mem_some_iff, c2ParallelForbiddenName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [streamTake_getD p (Nat.lt_succ_self _)]

/-- The preprocessor code, extracted once so consumers share a single combinator.
Specified, not constructed. -/
noncomputable def c2ParallelForbiddenCode : OracleCode :=
  Classical.choose exists_c2ParallelForbiddenCode

/-- **Specification of `c2ParallelForbiddenCode`**. -/
theorem mem_evalStream_c2ParallelForbiddenCode (p : Baire) :
    c2ParallelForbiddenName p ∈ c2ParallelForbiddenCode.evalStream p :=
  Classical.choose_spec exists_c2ParallelForbiddenCode p

/-! ### The postprocessor

A `C_Cantor` answer is a Cantor point; a `C₂.parallelize` answer is a sequence of
naturals, whose name carries coordinate `n` at the head of track `n`. Spreading the
answer's coordinate `m.unpair.1` over track `m.unpair.1` does exactly that, and is an
axiom-free two-node code. -/

/-- Spread the answer across tracks: `r m = a m.unpair.1`, so track `n` is constantly
`a n` and in particular `r (Nat.pair n 0) = a n`. -/
def trackSpreadCode : OracleCode := OracleCode.comp OracleCode.query OracleCode.left

theorem eval_trackSpreadCode (a : Baire) (m : ℕ) :
    trackSpreadCode.eval a m = Part.some (a m.unpair.1) :=
  (OracleCode.eval_comp_some (OracleCode.eval_left a m)).trans
    (OracleCode.eval_query a m.unpair.1)

theorem mem_evalStream_trackSpreadCode (a : Baire) :
    (fun m => a m.unpair.1) ∈ trackSpreadCode.evalStream a :=
  OracleCode.mem_evalStream.mpr fun m => by
    rw [eval_trackSpreadCode]
    exact Part.mem_some _

/-! ### The reduction -/

/-- **`C₂.parallelize ≤sW C_Cantor`, as an explicit pair.** -/
theorem isStrongReductionPair_parallelize_c2_le_c_cantor :
    IsStrongReductionPair C₂.parallelize C_Cantor c2ParallelForbiddenCode
      trackSpreadCode := by
  intro p xs hpxs hdom
  obtain rfl : xs = fun n => Baire.track n p := funext (baireSequence_names_iff.mp hpxs)
  rw [Problem.parallelize_dom_iff] at hdom
  refine ⟨c2ParallelForbiddenName p, mem_evalStream_c2ParallelForbiddenCode p,
    c2ParallelForbiddenName p, baireRep_names_iff.mpr rfl,
    c_Cantor_dom_c2ParallelForbiddenName (fun n => hdom n), ?_⟩
  intro a y' hay' hacc
  obtain ⟨hle, rfl⟩ := cantorRep_names_iff.mp hay'
  refine ⟨fun m => a m.unpair.1, mem_evalStream_trackSpreadCode a, fun n => a n, ?_, ?_⟩
  · exact natSequence_names_iff.mpr fun n => by rw [Nat.unpair_pair]
  · intro n
    have hx : (fun n => a n == 1) ∈ closedCantorSet (c2ParallelForbiddenName p) := hacc
    rw [closedCantorSet_c2ParallelForbiddenName] at hx
    have hb : Bool.toNat ((a n == 1 : Bool)) = a n := by
      have h01 : a n = 0 ∨ a n = 1 := by have := hle n; omega
      rcases h01 with h | h <;> rw [h] <;> simp
    have hn := hx n
    rwa [hb] at hn

/-- **Countably many binary choices reduce strongly to closed choice on Cantor
space.** -/
theorem parallelize_c2_le_c_cantor : C₂.parallelize ≤sW C_Cantor :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_parallelize_c2_le_c_cantor⟩

/-! ### The calibration -/

/-- **`LLPO.parallelize ≡sW WKL`.** The upper bound composes the parallelized
`C₂ ≡sW LLPO` calibration, the closed-choice reduction above, and the presentation
bridge; the lower bound is the death-race reduction of `WKLReduction.lean`. -/
theorem parallelize_llpo_equiv_wkl : LLPO.parallelize ≡sW WKL := by
  refine ⟨?_, wkl_le_parallelize_llpo⟩
  refine StrongWeihrauchReducible.trans (parallelize_congr_strong c2_equiv_llpo).2 ?_
  exact StrongWeihrauchReducible.trans parallelize_c2_le_c_cantor wkl_equiv_c_cantor.2

end ComputableAnalysis
