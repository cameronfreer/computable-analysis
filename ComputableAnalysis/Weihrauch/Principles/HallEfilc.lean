/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.PrefixTable
import ComputableAnalysis.Weihrauch.StrongReduction
import ComputableAnalysis.Weihrauch.Principles.Hall
import ComputableAnalysis.Weihrauch.Principles.EFILC

/-!
# `Hall ≤sW EFILC`: injective partial transversals as fibers

`hall_le_efilc : Hall ≤sW EFILC`, with the explicit reduction pair
`isStrongReductionPair_hall_le_efilc` over the named codes `hallSystemCode` and
`hallTransversalCode`.

The preprocessor compiles a presented family into the inverse system of its **injective
partial transversals**: the level-`k` fiber enumerates the codes of the injective
`k`-tuples with in-list entries — built by extending only with unused candidates, so no
duplicate-freeness test is ever computed — and the bond truncates the decoded tuple.
**The preprocessor consumes the enumerator track only**: the candidate relation is never
read by either code, entering solely through the membership-equivalence promise in the
correctness proof. The postprocessor reads the transversal **off the section answer
alone** — the level-`(n + 1)` tuple's entry `n` — so strongness is enforced by the
postprocessor's type.

Level nonemptiness is the one use of mathlib's Hall machinery: the **finite** marriage
theorem (`Finset.all_card_le_biUnion_card_iff_existsInjective'`), applied to the
enumerated lists through the marriage promise — a correctness promise only, never
computed. The semantic anchor `Hall.dom_iff` falls out at the end: the domain is exactly
the promised families, by compiling and decoding a section.

This reduction is proved from the presented promises alone — independently of any
ω-model or provability-level relationship between the corresponding statements. It
certifies a strong reduction in this one direction and nothing else: no lower bound and
no equivalence is suggested.
-/

namespace ComputableAnalysis

open Encodable Denumerable
open Baire (ofList)

/-! ### The compiled system -/

/-- Membership on raw lists as a Boolean, in structural-recursion form. -/
private def memB (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: t => decide (b = a) || memB a t

private theorem memB_eq_true {a : ℕ} {l : List ℕ} : memB a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [memB]
  | cons b t ih =>
    simp only [memB, Bool.or_eq_true, decide_eq_true_eq, ih, List.mem_cons]
    exact or_congr_left eq_comm

private theorem memB_eq_false {a : ℕ} {l : List ℕ} : memB a l = false ↔ a ∉ l := by
  rw [Bool.eq_false_iff]
  exact not_congr memB_eq_true

/-- All **injective** partial transversals on `{0, …, k - 1}`: each level extends only by
candidates not already used. -/
def hallTuples (q : Baire) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 =>
      (hallTuples q k).flatMap fun t =>
        ((hallCand q k).filter fun y => !(memB y t)).map fun y => t ++ [y]

/-- Membership characterization: exactly the length-`k` injective tuples with in-list
entries. -/
theorem mem_hallTuples (q : Baire) : ∀ (k : ℕ) (t : List ℕ),
    t ∈ hallTuples q k ↔
      t.length = k ∧ (∀ i, (hi : i < t.length) → t[i] ∈ hallCand q i) ∧ t.Nodup := by
  intro k
  induction k with
  | zero =>
    intro t
    simp only [hallTuples, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, fun i hi => absurd hi (by simp), List.nodup_nil⟩
    · rintro ⟨hlen, -, -⟩
      exact List.eq_nil_of_length_eq_zero hlen
  | succ k ih =>
    intro t
    simp only [hallTuples, List.mem_flatMap, List.mem_map, List.mem_filter,
      Bool.not_eq_eq_eq_not, Bool.not_true]
    constructor
    · rintro ⟨t', ht', y, ⟨hy, hyB⟩, rfl⟩
      obtain ⟨hlen, hmem, hnd⟩ := (ih t').mp ht'
      have hynot : y ∉ t' := memB_eq_false.mp hyB
      refine ⟨by simp [hlen], fun i hi => ?_, ?_⟩
      · rcases Nat.lt_or_ge i t'.length with h | h
        · rw [List.getElem_append_left h]
          exact hmem i h
        · have hieq : i = t'.length := by
            have h2 : i < t'.length + 1 := by simpa using hi
            omega
          subst hieq
          have hval : (t' ++ [y])[t'.length]'hi = y := by
            have h3 : (t' ++ [y])[t'.length]? = some y := List.getElem?_concat_length
            rw [List.getElem?_eq_getElem hi] at h3
            exact Option.some_injective _ h3
          rw [hval, hlen]
          exact hy
      · exact ((List.perm_append_singleton y t').nodup_iff).mpr
          (List.nodup_cons.mpr ⟨hynot, hnd⟩)
    · rintro ⟨hlen, hmem, hnd⟩
      have hk : k < t.length := by omega
      have hdrop : t.drop k = [t[k]] := by
        rw [List.drop_eq_getElem_cons hk]
        have h2 : t.drop (k + 1) = [] := List.drop_eq_nil_of_le (by omega)
        rw [h2]
      have hnotmem : t[k] ∉ t.take k := by
        intro hc
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hc
        have hj' : j < k := by
          simp only [List.length_take] at hj
          omega
        rw [List.getElem_take] at hjeq
        have : j = k := hnd.getElem_inj_iff.mp hjeq
        omega
      refine ⟨t.take k, (ih _).mpr ⟨?_, ?_, hnd.sublist (List.take_sublist k t)⟩,
        t[k], ⟨?_, memB_eq_false.mpr hnotmem⟩, ?_⟩
      · rw [List.length_take, hlen]
        omega
      · intro i hi
        have hi' : i < k := by
          simp only [List.length_take] at hi
          omega
        rw [List.getElem_take]
        exact hmem i (by omega)
      · exact hmem k hk
      · rw [← hdrop, List.take_append_drop]

/-- The bond of the compiled system: truncate the decoded tuple. Oracle-free. -/
def hallBondValue (k x : ℕ) : ℕ := encode ((ofNat (List ℕ) x : List ℕ).take k)

/-- The compiled system name: track `0` the coded injective-tuple fibers, track `1` the
truncation bonds. Reads the family's **enumerator track only**. -/
def hallSystemName (q : Baire) : Baire := fun m =>
  if m.unpair.1 = 0 then encode ((hallTuples q m.unpair.2).map fun t => encode t)
  else if m.unpair.1 = 1 then hallBondValue m.unpair.2.unpair.1 m.unpair.2.unpair.2
  else 0

@[simp]
theorem efilcFiber_hallSystemName (q : Baire) (k : ℕ) :
    efilcFiber (hallSystemName q) k = (hallTuples q k).map fun t => encode t := by
  simp [efilcFiber, hallSystemName, Nat.unpair_pair]

@[simp]
theorem efilcBond_hallSystemName (q : Baire) (k x : ℕ) :
    efilcBond (hallSystemName q) k x = hallBondValue k x := by
  simp [efilcBond, hallSystemName, Nat.unpair_pair]

/-! ### The compiled system keeps the promises -/

/-- The pure finite-Hall step, over the enumerated lists: the marriage condition yields an
injective length-`k` tuple of in-list candidates — the one use of mathlib's **finite**
Hall theorem, from the marriage promise only. -/
private theorem exists_hall_tuple {q : Baire} (hmar : HallMarriage q) (k : ℕ) :
    ∃ t : List ℕ, t.length = k ∧
      (∀ i, (hi : i < t.length) → t[i] ∈ hallCand q i) ∧ t.Nodup := by
  have hall : ∀ s : Finset (Fin k),
      s.card ≤ (s.biUnion fun i => (hallCand q i.1).toFinset).card := by
    intro s
    have himg : ((s.image Fin.val).biUnion fun n => (hallCand q n).toFinset) =
        s.biUnion fun i => (hallCand q i.1).toFinset :=
      Finset.image_biUnion
    calc s.card = (s.image Fin.val).card :=
          (Finset.card_image_of_injective s Fin.val_injective).symm
      _ ≤ ((s.image Fin.val).biUnion fun n => (hallCand q n).toFinset).card := hmar _
      _ = (s.biUnion fun i => (hallCand q i.1).toFinset).card := by rw [himg]
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_existsInjective'
      fun i : Fin k => (hallCand q i.1).toFinset).mp hall
  refine ⟨List.ofFn f, by simp, fun i hi => ?_, List.nodup_ofFn.mpr hfinj⟩
  have hi' : i < k := by simpa using hi
  rw [List.getElem_ofFn]
  exact List.mem_toFinset.mp (hfmem _)

/-- The compiled system is in `EFILC`'s domain on every promised family: nonemptiness
from the marriage promise through finite Hall, bonds into the fiber below by
truncation. -/
theorem efilc_dom_hallSystemName {q : Baire} (hmar : HallMarriage q) :
    EFILC.Dom (hallSystemName q) := by
  rw [EFILC.dom_iff]
  constructor
  · intro k
    obtain ⟨t, hlen, hmem, hnd⟩ := exists_hall_tuple hmar k
    rw [efilcFiber_hallSystemName]
    exact List.ne_nil_of_mem
      (List.mem_map_of_mem ((mem_hallTuples q k t).mpr ⟨hlen, hmem, hnd⟩))
  · intro k x hx
    rw [efilcFiber_hallSystemName] at hx ⊢
    rw [efilcBond_hallSystemName]
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hlen, hmem, hnd⟩ := (mem_hallTuples q (k + 1) t).mp ht
    refine List.mem_map.mpr ⟨t.take k, (mem_hallTuples q k _).mpr
      ⟨?_, ?_, hnd.sublist (List.take_sublist k t)⟩, ?_⟩
    · rw [List.length_take, hlen]
      omega
    · intro i hi
      have hi' : i < k := by
        simp only [List.length_take] at hi
        omega
      rw [List.getElem_take]
      exact hmem i (by omega)
    · rw [hallBondValue, Denumerable.ofNat_encode]

/-! ### The transversal read off a section -/

/-- The transversal name: entry `n` of the decoded level-`(n + 1)` tuple. Runs on the
**answer alone**. -/
def transversalName (a : Baire) : Baire := fun n =>
  (ofNat (List ℕ) (a (n + 1)) : List ℕ).getD n 0

/-- **Sections decode to injective transversals**: the truncation coherence makes the
decoded section tuples a nested family, so the read-off values are entries of every
long-enough injective tuple. The candidate relation enters exactly here, through the
membership-equivalence promise. -/
theorem isHallTransversal_of_section {q a : Baire} (hmem : HallMemIff q)
    (hsec : IsEfilcSection (hallSystemName q) a) :
    IsHallTransversal q (transversalName a) := by
  obtain ⟨hfib, hcoh⟩ := hsec
  -- the decoded section tuples
  have htup : ∀ n, (ofNat (List ℕ) (a n) : List ℕ) ∈ hallTuples q n := by
    intro n
    have h := hfib n
    rw [efilcFiber_hallSystemName] at h
    obtain ⟨t, ht, hcode⟩ := List.mem_map.mp h
    rw [← hcode, Denumerable.ofNat_encode]
    exact ht
  have hlen : ∀ n, (ofNat (List ℕ) (a n) : List ℕ).length = n := fun n =>
    ((mem_hallTuples q n _).mp (htup n)).1
  have hnd : ∀ n, (ofNat (List ℕ) (a n) : List ℕ).Nodup := fun n =>
    ((mem_hallTuples q n _).mp (htup n)).2.2
  have htake : ∀ n, (ofNat (List ℕ) (a (n + 1)) : List ℕ).take n =
      (ofNat (List ℕ) (a n) : List ℕ) := by
    intro n
    have h := hcoh n
    rw [efilcBond_hallSystemName, hallBondValue] at h
    rw [← h, Denumerable.ofNat_encode]
  have hprefix : ∀ {n m : ℕ}, n ≤ m →
      (ofNat (List ℕ) (a m) : List ℕ).take n = (ofNat (List ℕ) (a n) : List ℕ) := by
    intro n m hnm
    induction m with
    | zero =>
      obtain rfl : n = 0 := by omega
      exact List.take_of_length_le (by rw [hlen])
    | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with hlt | hge
      · rw [← ih (by omega), ← htake m, List.take_take, Nat.min_eq_left (by omega)]
      · obtain rfl : n = m + 1 := by omega
        exact List.take_of_length_le (by rw [hlen])
  have hget : ∀ {n m i : ℕ}, n ≤ m → i < n →
      (ofNat (List ℕ) (a m) : List ℕ).getD i 0 =
        (ofNat (List ℕ) (a n) : List ℕ).getD i 0 := by
    intro n m i hnm hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    have h1 : (ofNat (List ℕ) (a m) : List ℕ)[i]? =
        ((ofNat (List ℕ) (a m) : List ℕ).take n)[i]? :=
      (List.getElem?_take_of_lt hi).symm
    rw [h1, hprefix hnm]
  constructor
  · intro n
    -- the value is an entry of the level-`(n + 1)` tuple, hence an enumerated candidate
    have hn : n < (ofNat (List ℕ) (a (n + 1)) : List ℕ).length := by
      rw [hlen]
      omega
    have hval : transversalName a n = (ofNat (List ℕ) (a (n + 1)) : List ℕ)[n] := by
      change (ofNat (List ℕ) (a (n + 1)) : List ℕ).getD n 0 = _
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
    refine (hmem n _).mp ?_
    rw [hval]
    exact ((mem_hallTuples q (n + 1) _).mp (htup (n + 1))).2.1 n hn
  · intro n n' heq
    by_contra hne
    -- both values are entries of one covering injective tuple
    set m := max n n' + 1 with hm
    have hn : n < (ofNat (List ℕ) (a m) : List ℕ).length := by rw [hlen]; omega
    have hn' : n' < (ofNat (List ℕ) (a m) : List ℕ).length := by rw [hlen]; omega
    have h1 : transversalName a n = (ofNat (List ℕ) (a m) : List ℕ).getD n 0 := by
      change (ofNat (List ℕ) (a (n + 1)) : List ℕ).getD n 0 = _
      rw [hget (by omega : n + 1 ≤ m) (by omega)]
    have h2 : transversalName a n' = (ofNat (List ℕ) (a m) : List ℕ).getD n' 0 := by
      change (ofNat (List ℕ) (a (n' + 1)) : List ℕ).getD n' 0 = _
      rw [hget (by omega : n' + 1 ≤ m) (by omega)]
    have h3 : (ofNat (List ℕ) (a m) : List ℕ).getD n 0 =
        (ofNat (List ℕ) (a m) : List ℕ).getD n' 0 := by
      rw [← h1, ← h2, heq]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hn, List.getElem?_eq_getElem hn',
      Option.getD_some, Option.getD_some] at h3
    exact hne ((hnd m).getElem_inj_iff.mp h3)

/-! ### The codes -/

/-- A prefix length covering the enumerator positions below the coordinate's level. -/
def hallPosBound (m : ℕ) : ℕ :=
  prefixBound ((List.range (m.unpair.2 + 1)).map fun i => Nat.pair 0 i)

theorem hallPos_lt_hallPosBound {m i : ℕ} (h : i ≤ m.unpair.2) :
    Nat.pair 0 i < hallPosBound m :=
  lt_prefixBound_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by omega)))

private theorem hallCand_congr {q₁ q₂ : Baire} {i : ℕ}
    (h : q₁ (Nat.pair 0 i) = q₂ (Nat.pair 0 i)) : hallCand q₁ i = hallCand q₂ i := by
  rw [hallCand, hallCand, h]

private theorem hallTuples_congr {q₁ q₂ : Baire} {k : ℕ}
    (h : ∀ i < k, hallCand q₁ i = hallCand q₂ i) :
    hallTuples q₁ k = hallTuples q₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [hallTuples, hallTuples, ih fun i hi => h i (by omega), h k (by omega)]

private theorem hallTuples_eq_nat_rec (q : Baire) (k : ℕ) :
    hallTuples q k = Nat.rec (motive := fun _ => List (List ℕ)) [[]]
      (fun j IH => IH.flatMap fun t =>
        ((hallCand q j).filter fun y => !(memB y t)).map fun y => t ++ [y]) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hallTuples, ih]

private theorem memB_eq_foldr (a : ℕ) (l : List ℕ) :
    memB a l = l.foldr (fun b acc => decide (b = a) || acc) false := by
  induction l with
  | nil => rfl
  | cons b t ih => rw [List.foldr_cons, ← ih]; rfl

private theorem primrec_memB : Primrec₂ memB := by
  have h : Primrec fun p : ℕ × List ℕ =>
      p.2.foldr (fun b acc => decide (b = p.1) || acc) false :=
    Primrec.list_foldr (f := fun p : ℕ × List ℕ => p.2)
      (g := fun _ : ℕ × List ℕ => false)
      (h := fun (p : ℕ × List ℕ) (z : ℕ × Bool) => decide (z.1 = p.1) || z.2)
      Primrec.snd (Primrec.const false)
      ((Primrec.or.comp
        (PrimrecRel.comp Primrec.eq (Primrec.fst.comp Primrec.snd)
          (Primrec.fst.comp Primrec.fst)).decide
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact h.of_eq fun p => (memB_eq_foldr p.1 p.2).symm

private theorem primrec_tableHallCand :
    Primrec₂ fun (P : List ℕ) (i : ℕ) => hallCand (ofList P) i :=
  (Primrec.ofNat (List ℕ)).comp ((Primrec.list_getD 0).comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd))

private theorem primrec_tableHallTuples :
    Primrec₂ fun (P : List ℕ) (k : ℕ) => hallTuples (ofList P) k := by
  have hinner : Primrec₂ fun (z : List ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
      ((hallCand (ofList z.1) z.2.1).filter fun y => !(memB y t)).map fun y => t ++ [y] :=
    Primrec.list_map
      (f := fun w : (List ℕ × ℕ × List (List ℕ)) × List ℕ =>
        (hallCand (ofList w.1.1) w.1.2.1).filter fun y => !(memB y w.2))
      (g := fun (w : (List ℕ × ℕ × List (List ℕ)) × List ℕ) (y : ℕ) => w.2 ++ [y])
      (primrec_list_filter
        (primrec_tableHallCand.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        ((Primrec.not.comp (primrec_memB.comp Primrec.snd
          (Primrec.snd.comp Primrec.fst))).to₂))
      ((Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  have hg : Primrec₂ fun (P : List ℕ) (z : ℕ × List (List ℕ)) =>
      z.2.flatMap fun t =>
        ((hallCand (ofList P) z.1).filter fun y => !(memB y t)).map fun y => t ++ [y] :=
    Primrec.list_flatMap (f := fun z : List ℕ × ℕ × List (List ℕ) => z.2.2)
      (g := fun (z : List ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
        ((hallCand (ofList z.1) z.2.1).filter fun y => !(memB y t)).map fun y => t ++ [y])
      (Primrec.snd.comp Primrec.snd) hinner
  exact (Primrec.nat_rec (Primrec.const [[]]) hg).of_eq fun P k =>
    (hallTuples_eq_nat_rec (ofList P) k).symm

/-- A single code produces the compiled system name, consuming the enumerator track
only, from a primitively bounded prefix. -/
theorem exists_hallSystemCode : ∃ K : OracleCode, ∀ q : Baire,
    hallSystemName q ∈ K.evalStream q := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hbound : Primrec₂ fun (m : ℕ) (_ : ℕ) => hallPosBound m :=
    ((primrec_prefixBound.comp (Primrec.list_map
      (f := fun m : ℕ => List.range (m.unpair.2 + 1))
      (g := fun (_ : ℕ) (i : ℕ) => Nat.pair 0 i)
      (Primrec.list_range.comp (Primrec.succ.comp hu2))
      ((Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd).to₂))).comp Primrec.fst).to₂
  have hfib : Primrec fun v : ℕ =>
      encode ((hallTuples (ofList (ofNat (List ℕ) v.unpair.2)) v.unpair.1.unpair.2).map
        fun t => encode t) :=
    Primrec.encode.comp (Primrec.list_map
      (f := fun v : ℕ => hallTuples (ofList (ofNat (List ℕ) v.unpair.2)) v.unpair.1.unpair.2)
      (g := fun (_ : ℕ) (t : List ℕ) => encode t)
      (primrec_tableHallTuples.comp ((Primrec.ofNat (List ℕ)).comp hu2) (hu2.comp hu1))
      (Primrec.encode.comp Primrec.snd).to₂)
  have hbond : Primrec fun v : ℕ =>
      hallBondValue v.unpair.1.unpair.2.unpair.1 v.unpair.1.unpair.2.unpair.2 :=
    Primrec.encode.comp (Primrec.list_take.comp
      (Primrec.fst.comp (Primrec.unpair.comp (hu2.comp hu1)))
      ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp (Primrec.unpair.comp (hu2.comp hu1)))))
  have hg : Primrec fun v : ℕ =>
      if v.unpair.1.unpair.1 = 0 then
        encode ((hallTuples (ofList (ofNat (List ℕ) v.unpair.2)) v.unpair.1.unpair.2).map
          fun t => encode t)
      else if v.unpair.1.unpair.1 = 1 then
        hallBondValue v.unpair.1.unpair.2.unpair.1 v.unpair.1.unpair.2.unpair.2
      else 0 :=
    Primrec.ite (Primrec.eq.comp (hu1.comp hu1) (Primrec.const 0)) hfib
      (Primrec.ite (Primrec.eq.comp (hu1.comp hu1) (Primrec.const 1)) hbond
        (Primrec.const 0))
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨K, fun q => OracleCode.mem_evalStream.mpr fun m => ?_⟩
  rw [hK q m, Part.mem_some_iff, hallSystemName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  have htab : hallTuples (ofList (streamTake q (hallPosBound m))) m.unpair.2 =
      hallTuples q m.unpair.2 := by
    exact hallTuples_congr fun i hi => hallCand_congr
      (Baire.ofList_streamTake q (hallPos_lt_hallPosBound (by omega)))
  by_cases h0 : m.unpair.1 = 0
  · rw [if_pos h0, if_pos h0, htab]
  · by_cases h1 : m.unpair.1 = 1
    · rw [if_neg h0, if_pos h1, if_neg h0]
    · rw [if_neg h0, if_neg h1, if_neg h0]

/-- The system code, extracted once so consumers share a single combinator. Specified,
not constructed. -/
noncomputable def hallSystemCode : OracleCode := Classical.choose exists_hallSystemCode

/-- **Specification of `hallSystemCode`**: on any name it produces the compiled system. -/
theorem mem_evalStream_hallSystemCode (q : Baire) :
    hallSystemName q ∈ hallSystemCode.evalStream q :=
  Classical.choose_spec exists_hallSystemCode q

/-- A single code produces the transversal name from the answer alone. -/
theorem exists_hallTransversalCode : ∃ H : OracleCode, ∀ a : Baire,
    transversalName a ∈ H.evalStream a := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hbound : Primrec₂ fun (n : ℕ) (_ : ℕ) => n + 2 :=
    (Primrec.succ.comp (Primrec.succ.comp Primrec.fst)).to₂
  have hg : Primrec fun v : ℕ =>
      (ofNat (List ℕ) ((ofNat (List ℕ) v.unpair.2 : List ℕ).getD (v.unpair.1 + 1) 0) :
        List ℕ).getD v.unpair.1 0 :=
    (Primrec.list_getD 0).comp
      ((Primrec.ofNat (List ℕ)).comp ((Primrec.list_getD 0).comp
        ((Primrec.ofNat (List ℕ)).comp hu2) (Primrec.succ.comp hu1)))
      hu1
  obtain ⟨H, hH⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨H, fun a => OracleCode.mem_evalStream.mpr fun n => ?_⟩
  rw [hH a n, Part.mem_some_iff, transversalName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [streamTake_getD a (by omega : n + 1 < n + 2)]

/-- The transversal code, extracted once so consumers share a single combinator.
Specified, not constructed. -/
noncomputable def hallTransversalCode : OracleCode :=
  Classical.choose exists_hallTransversalCode

/-- **Specification of `hallTransversalCode`**: on any answer stream it produces the
transversal name. -/
theorem mem_evalStream_hallTransversalCode (a : Baire) :
    transversalName a ∈ hallTransversalCode.evalStream a :=
  Classical.choose_spec exists_hallTransversalCode a

/-! ### The reduction, and the semantic anchor -/

/-- **`Hall ≤sW EFILC`, as an explicit pair**: `hallSystemCode` compiles the injective
partial transversals from the enumerator track alone, and `hallTransversalCode` decodes
any accepted section into an injective transversal, from the answer alone. -/
theorem isStrongReductionPair_hall_le_efilc :
    IsStrongReductionPair Hall EFILC hallSystemCode hallTransversalCode := by
  intro p x hpx hdom
  obtain rfl : x = p := baireRep_names_iff.mp hpx
  obtain ⟨f₀, hmem, hmar, -⟩ := hdom
  refine ⟨hallSystemName x, mem_evalStream_hallSystemCode x, hallSystemName x,
    baireRep_names_iff.mpr rfl, efilc_dom_hallSystemName hmar, ?_⟩
  intro a y' hay' hacc
  obtain rfl : y' = a := baireRep_names_iff.mp hay'
  obtain ⟨-, -, hsec⟩ := EFILC.accepts_iff.mp hacc
  refine ⟨transversalName y', mem_evalStream_hallTransversalCode y', transversalName y',
    baireRep_names_iff.mpr rfl, ?_⟩
  exact Hall.accepts_iff.mpr ⟨hmem, hmar, isHallTransversal_of_section hmem hsec⟩

/-- **Countable Hall reduces strongly to explicit finite inverse-limit compactness**, for
the one-sided relation-plus-enumerator presentation. A strong reduction in this one
direction and nothing else: no lower bound and no equivalence is suggested. -/
theorem hall_le_efilc : Hall ≤sW EFILC :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_hall_le_efilc⟩

/-- **The semantic anchor**: `Hall`'s domain is exactly the promised families — the
nontrivial direction *is* countable Hall, by compiling to `EFILC` and decoding a
section. -/
theorem Hall.dom_iff {p : Baire} : Hall.Dom p ↔ HallMemIff p ∧ HallMarriage p := by
  constructor
  · rintro ⟨f, hmem, hmar, -⟩
    exact ⟨hmem, hmar⟩
  · rintro ⟨hmem, hmar⟩
    obtain ⟨s, -, -, hsec⟩ := efilc_dom_hallSystemName hmar
    exact ⟨transversalName s, hmem, hmar, isHallTransversal_of_section hmem hsec⟩

end ComputableAnalysis
