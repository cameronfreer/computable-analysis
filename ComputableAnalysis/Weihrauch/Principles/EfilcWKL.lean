/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.PrefixTable
import ComputableAnalysis.Weihrauch.StrongReduction
import ComputableAnalysis.Weihrauch.Principles.EFILC
import ComputableAnalysis.Weihrauch.Principles.WKL

/-!
# `EFILC ≤W WKL`: chunk-coded systems, with a certified ordinary reduction

`efilc_le_wkl : EFILC ≤W WKL`, with the explicit reduction pair
`isReductionPair_efilc_le_wkl` over the named codes `chunkTreeCode` and
`treeSectionCode`.

The preprocessor compiles a presented system into a binary tree by **chunk coding**: the
level-`k` chunk has width equal to the level-`k` fiber length, and a node is any bit-word
prefix of the chunk encoding of an in-range coherent index tuple (`chunkBits`,
little-endian `Nat.testBit` blocks; deliberately inefficient width, which keeps every
index encodable and the verifier primitive recursive). The postprocessor decodes a path
back into a section: the chunk-`k` bits read back the selected index (`bitsToNat`), and
the fiber entry at that index is the section value.

**This is a certified ordinary reduction**: its decoder consults the chunk widths — data
of the *input* system — so `treeSectionCode` runs on `Baire.interleave` of the input and
the answer, exactly the access `≤W` grants and `≤sW` withholds. (Compare `WKLEfilc.lean`,
whose decoder runs on the answer alone.) Whether some *other* strong reduction exists in
this direction is not addressed here: the theorem certifies an ordinary reduction, never
non-strong-reducibility.

Both codes ride `OracleCode.exists_prefixChainCode`: the tree-membership verifier reads
the fibers below the word length (a primitively bounded prefix), then the bond values *of
the fiber elements just read* (an adaptively recomputed prefix); the decoder reads the
widths from the input's even track, then the chunk bits from the answer's odd track.

This reduction is proved from the presented promises alone — independently of any
ω-model or provability-level relationship between the corresponding statements.
-/

namespace ComputableAnalysis

open Encodable Denumerable
open OracleCode (binaryWords mem_binaryWords)
open Baire (ofList)

/-! ### Chunk bit coding -/

/-- The width-`w` little-endian bit block of an index. -/
def chunkBits (w i : ℕ) : List Bool := (List.range w).map fun j => i.testBit j

@[simp]
theorem length_chunkBits (w i : ℕ) : (chunkBits w i).length = w := by
  simp [chunkBits]

/-- Read a bit block back to its index. -/
def bitsToNat : List Bool → ℕ
  | [] => 0
  | b :: t => (if b then 1 else 0) + 2 * bitsToNat t

theorem chunkBits_succ (w i : ℕ) :
    chunkBits (w + 1) i = i.testBit 0 :: chunkBits w (i / 2) := by
  rw [chunkBits, List.range_succ_eq_map, List.map_cons, List.map_map]
  refine congrArg _ ?_
  rw [chunkBits]
  refine List.map_congr_left fun j _ => ?_
  simp [Function.comp, Nat.testBit_succ]

/-- **The chunk coding decodes**: reading back the bit block of `i` recovers `i` modulo
`2 ^ w` — in particular exactly `i` whenever `i < 2 ^ w`. -/
theorem bitsToNat_chunkBits (w i : ℕ) : bitsToNat (chunkBits w i) = i % 2 ^ w := by
  induction w generalizing i with
  | zero => simp [chunkBits, bitsToNat, Nat.mod_one]
  | succ w ih =>
    rw [chunkBits_succ, bitsToNat, ih, pow_succ, mul_comm (2 ^ w) 2, Nat.mod_mul,
      Nat.testBit_zero]
    by_cases h : i % 2 = 1
    · simp [h]
    · have h0 : i % 2 = 0 := by omega
      simp [h0]

/-! ### The presented system, read positionally -/

/-- The level-`k` chunk width: the fiber length. -/
def efilcWidth (q : Baire) (k : ℕ) : ℕ := (efilcFiber q k).length

/-- The fiber entry an index selects; fallback `0` out of range. -/
def efilcElem (q : Baire) (k idx : ℕ) : ℕ := (efilcFiber q k).getD idx 0

/-- The bit position where the level-`k` chunk starts. -/
def chunkStartQ (q : Baire) : ℕ → ℕ
  | 0 => 0
  | k + 1 => chunkStartQ q k + efilcWidth q k

theorem chunkStartQ_le {q : Baire} {m k : ℕ} (h : m ≤ k) :
    chunkStartQ q m ≤ chunkStartQ q k := by
  induction k with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega)).trans (Nat.le_add_right _ _)

/-- All in-range index tuples for levels `0, …, j - 1`. -/
def efilcTuples (q : Baire) : ℕ → List (List ℕ)
  | 0 => [[]]
  | j + 1 =>
      (efilcTuples q j).flatMap fun t =>
        (List.range (efilcWidth q j)).map fun i => t ++ [i]

theorem mem_efilcTuples (q : Baire) : ∀ (j : ℕ) (t : List ℕ),
    t ∈ efilcTuples q j ↔
      t.length = j ∧ ∀ i, (hi : i < t.length) → t[i] < efilcWidth q i := by
  intro j
  induction j with
  | zero =>
    intro t
    simp only [efilcTuples, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, fun i hi => absurd hi (by simp)⟩
    · rintro ⟨hlen, -⟩
      exact List.eq_nil_of_length_eq_zero hlen
  | succ j ih =>
    intro t
    simp only [efilcTuples, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨t', ht', i, hi, rfl⟩
      obtain ⟨hlen, hmem⟩ := (ih t').mp ht'
      refine ⟨by simp [hlen], fun m hm => ?_⟩
      rcases Nat.lt_or_ge m t'.length with h | h
      · rw [List.getElem_append_left h]
        exact hmem m h
      · have hmeq : m = t'.length := by
          have h2 : m < t'.length + 1 := by simpa using hm
          omega
        subst hmeq
        have hval : (t' ++ [i])[t'.length]'hm = i := by
          have h3 : (t' ++ [i])[t'.length]? = some i := List.getElem?_concat_length
          rw [List.getElem?_eq_getElem hm] at h3
          exact Option.some_injective _ h3
        rw [hval, hlen]
        exact hi
    · rintro ⟨hlen, hmem⟩
      have hj : j < t.length := by omega
      have hdrop : t.drop j = [t[j]] := by
        rw [List.drop_eq_getElem_cons hj]
        have h2 : t.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
        rw [h2]
      refine ⟨t.take j, (ih _).mpr ⟨?_, ?_⟩, t[j], ?_, ?_⟩
      · rw [List.length_take, hlen]
        omega
      · intro i hi
        have hi' : i < j := by simpa [List.length_take, hlen] using hi
        rw [List.getElem_take]
        exact hmem i (by omega)
      · exact hmem j hj
      · rw [← hdrop, List.take_append_drop]

/-- The coherence check for an index tuple: consecutive selected elements are related by
the bonds. -/
def tupleCoherentB (q : Baire) (t : List ℕ) : Bool :=
  (List.range (t.length - 1)).all fun i =>
    decide (efilcBond q i (efilcElem q (i + 1) (t.getD (i + 1) 0)) =
      efilcElem q i (t.getD i 0))

theorem tupleCoherentB_iff {q : Baire} {t : List ℕ} :
    tupleCoherentB q t = true ↔ ∀ i, i + 1 < t.length →
      efilcBond q i (efilcElem q (i + 1) (t.getD (i + 1) 0)) =
        efilcElem q i (t.getD i 0) := by
  simp only [tupleCoherentB, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro h i hi
    exact h i (by omega)
  · intro h i hi
    exact h i (by omega)

/-- The chunk encoding of the first `m` levels of an index tuple. -/
def encodeUpTo (q : Baire) (t : List ℕ) (m : ℕ) : List Bool :=
  (List.range m).flatMap fun i => chunkBits (efilcWidth q i) (t.getD i 0)

theorem encodeUpTo_succ (q : Baire) (t : List ℕ) (m : ℕ) :
    encodeUpTo q t (m + 1) =
      encodeUpTo q t m ++ chunkBits (efilcWidth q m) (t.getD m 0) := by
  rw [encodeUpTo, encodeUpTo, List.range_succ, List.flatMap_append]
  simp

@[simp]
theorem length_encodeUpTo (q : Baire) (t : List ℕ) (m : ℕ) :
    (encodeUpTo q t m).length = chunkStartQ q m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [encodeUpTo_succ, List.length_append, ih, length_chunkBits]
    rfl

theorem encodeUpTo_prefix (q : Baire) (t : List ℕ) {m j : ℕ} (h : m ≤ j) :
    encodeUpTo q t m <+: encodeUpTo q t j := by
  induction j with
  | zero =>
    obtain rfl : m = 0 := by omega
    exact List.prefix_refl _
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact List.prefix_refl _
    · rw [encodeUpTo_succ]
      exact (ih (by omega)).trans (List.prefix_append _ _)

theorem encodeUpTo_congr {q : Baire} {t t' : List ℕ} {m : ℕ}
    (h : ∀ i < m, t.getD i 0 = t'.getD i 0) :
    encodeUpTo q t m = encodeUpTo q t' m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [encodeUpTo_succ, encodeUpTo_succ, ih fun i hi => h i (by omega), h m (by omega)]

/-- Truncating an in-range tuple stays in range. -/
theorem take_efilcTuples {q : Baire} {j m : ℕ} {t : List ℕ} (hm : m ≤ j)
    (ht : t ∈ efilcTuples q j) : t.take m ∈ efilcTuples q m := by
  obtain ⟨hlen, hmem⟩ := (mem_efilcTuples q j t).mp ht
  refine (mem_efilcTuples q m _).mpr ⟨?_, fun i hi => ?_⟩
  · rw [List.length_take, hlen]
    omega
  · have hi' : i < m := by
      simp only [List.length_take] at hi
      omega
    rw [List.getElem_take]
    exact hmem i (by omega)

/-- Truncating a coherent tuple stays coherent. -/
theorem tupleCoherentB_take {q : Baire} {m : ℕ} {t : List ℕ}
    (h : tupleCoherentB q t = true) : tupleCoherentB q (t.take m) = true := by
  rw [tupleCoherentB_iff] at h ⊢
  intro i hi
  have hlen : (t.take m).length ≤ t.length := by
    rw [List.length_take]
    omega
  have hgd : ∀ n, n < (t.take m).length → (t.take m).getD n 0 = t.getD n 0 := by
    intro n hn
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take_of_lt (by simp only [List.length_take] at hn; omega)]
  rw [hgd (i + 1) hi, hgd i (by omega)]
  exact h i (by omega)

/-- Bit `j` of the level-`k` chunk of an encoded tuple. -/
theorem getD_encodeUpTo (q : Baire) (t : List ℕ) {m k j : ℕ} (hk : k < m)
    (hj : j < efilcWidth q k) :
    (encodeUpTo q t m).getD (chunkStartQ q k + j) false =
      (chunkBits (efilcWidth q k) (t.getD k 0)).getD j false := by
  induction m with
  | zero => omega
  | succ m ih =>
    rw [encodeUpTo_succ]
    rcases Nat.lt_or_ge k m with hkm | hkm
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left, ← List.getD_eq_getElem?_getD]
      · exact ih hkm
      · rw [length_encodeUpTo]
        have h1 : chunkStartQ q (k + 1) ≤ chunkStartQ q m := chunkStartQ_le (by omega)
        have h2 : chunkStartQ q (k + 1) = chunkStartQ q k + efilcWidth q k := rfl
        omega
    · obtain rfl : k = m := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right, length_encodeUpTo]
      · have h2 : chunkStartQ q k + j - chunkStartQ q k = j := by omega
        rw [h2, ← List.getD_eq_getElem?_getD]
      · rw [length_encodeUpTo]
        omega

/-! ### The compiled tree -/

/-- The node test: some in-range coherent tuple of at most `w.length` chunks encodes `w`
as a prefix. Prefixhood is phrased through `List.take`, the primitive-recursive form. -/
def chunkNodeB (q : Baire) (w : List Bool) : Bool :=
  (List.range (w.length + 1)).any fun j =>
    (efilcTuples q j).any fun t =>
      tupleCoherentB q t && decide (w = (encodeUpTo q t j).take w.length)

theorem chunkNodeB_iff {q : Baire} {w : List Bool} :
    chunkNodeB q w = true ↔ ∃ j ≤ w.length, ∃ t ∈ efilcTuples q j,
      tupleCoherentB q t = true ∧ w <+: encodeUpTo q t j := by
  simp only [chunkNodeB, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, t, ht, hcoh, hpre⟩
    exact ⟨j, by omega, t, ht, hcoh, List.prefix_iff_eq_take.mpr hpre⟩
  · rintro ⟨j, hj, t, ht, hcoh, hpre⟩
    exact ⟨j, by omega, t, ht, hcoh, List.prefix_iff_eq_take.mp hpre⟩

/-- The compiled tree name: the node test at the decoded word. -/
def chunkTreeName (q : Baire) : Baire := fun m =>
  if chunkNodeB q (treeWordDecode m) then 1 else 0

theorem treeMem_chunkTreeName {q : Baire} {w : List Bool} :
    TreeMem (chunkTreeName q) w ↔ chunkNodeB q w = true := by
  rw [TreeMem, chunkTreeName, treeWordDecode_treeWordCode]
  cases h : chunkNodeB q w <;> simp

/-! ### The compiled tree keeps the promises -/

theorem efilcWidth_pos {q : Baire} (hne : FibersNonempty q) (k : ℕ) :
    0 < efilcWidth q k :=
  List.length_pos_iff.mpr (hne k)

theorem le_chunkStartQ {q : Baire} (hne : FibersNonempty q) (k : ℕ) :
    k ≤ chunkStartQ q k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    have := efilcWidth_pos hne k
    have h2 : chunkStartQ q (k + 1) = chunkStartQ q k + efilcWidth q k := rfl
    omega

theorem chunkStartQ_lt {q : Baire} (hne : FibersNonempty q) {m k : ℕ} (h : m < k) :
    chunkStartQ q m < chunkStartQ q k := by
  have h1 : chunkStartQ q (m + 1) ≤ chunkStartQ q k := chunkStartQ_le (by omega)
  have h2 : chunkStartQ q (m + 1) = chunkStartQ q m + efilcWidth q m := rfl
  have := efilcWidth_pos hne m
  omega

/-- Prefix closure: truncate the witness tuple to the shorter word's chunk count. -/
theorem isPrefixClosed_chunkTreeName {q : Baire} (hne : FibersNonempty q) :
    IsPrefixClosed (chunkTreeName q) := by
  intro w v hw hpre
  rw [treeMem_chunkTreeName] at hw ⊢
  rw [chunkNodeB_iff] at hw ⊢
  obtain ⟨j, hj, t, ht, hcoh, hwpre⟩ := hw
  rcases Nat.lt_or_ge v.length j with hjv | hjv
  swap
  · exact ⟨j, hjv, t, ht, hcoh, hpre.trans hwpre⟩
  · refine ⟨v.length, le_rfl, t.take v.length,
      take_efilcTuples (by
        have := ((mem_efilcTuples q j t).mp ht).1
        omega) ht, tupleCoherentB_take hcoh, ?_⟩
    have htlen : t.length = j := ((mem_efilcTuples q j t).mp ht).1
    have henc : encodeUpTo q (t.take v.length) v.length = encodeUpTo q t v.length := by
      refine encodeUpTo_congr fun i hi => ?_
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_take_of_lt hi]
    rw [henc]
    refine List.prefix_of_prefix_length_le (hpre.trans hwpre)
      (encodeUpTo_prefix q t (by omega)) ?_
    rw [length_encodeUpTo]
    exact (le_chunkStartQ hne v.length).trans' (le_refl _) |>.trans
      (le_of_eq rfl) |>.trans (le_refl _) |>.trans' (by omega)

/-- Infinity: push any top element down through the bonds, index it in each fiber, and
take the first `n` encoded bits. -/
theorem isInfiniteTree_chunkTreeName {q : Baire} (hne : FibersNonempty q)
    (hB : BondsIntoFiber q) : IsInfiniteTree (chunkTreeName q) := by
  intro n
  -- the coherent element chain below a top element of fiber `n`
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne n)
  set e : ℕ → ℕ := fun i => efilcDown q n i x with he
  have hemem : ∀ i ≤ n, e i ∈ efilcFiber q i := fun i hi => efilcDown_mem hB hi hx
  -- the index tuple of the chain
  set t : List ℕ := (List.range n).map fun i => (efilcFiber q i).idxOf (e i) with htdef
  have hgetD : ∀ i < n, t.getD i 0 = (efilcFiber q i).idxOf (e i) := by
    intro i hi
    rw [htdef, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have helem : ∀ i < n, efilcElem q i (t.getD i 0) = e i := by
    intro i hi
    rw [efilcElem, hgetD i hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (hemem i (by omega))),
      Option.getD_some, List.getElem_idxOf]
  have ht : t ∈ efilcTuples q n := by
    refine (mem_efilcTuples q n t).mpr ⟨by simp [htdef], fun i hi => ?_⟩
    have hi' : i < n := by simpa [htdef] using hi
    have : t[i] = (efilcFiber q i).idxOf (e i) := by
      simp [htdef]
    rw [this]
    exact List.idxOf_lt_length_of_mem (hemem i (by omega))
  have hcoh : tupleCoherentB q t = true := by
    rw [tupleCoherentB_iff]
    intro i hi
    have hlen : t.length = n := by simp [htdef]
    have hi' : i + 1 < n := by omega
    rw [helem (i + 1) hi', helem i (by omega), he]
    have h1 : efilcBond q i (efilcDown q n (i + 1) x) =
        efilcDown q (i + 1) i (efilcDown q n (i + 1) x) :=
      (efilcDown_succ_self q i _).symm
    rw [h1, efilcDown_trans q (by omega) (by omega)]
  -- the length-`n` node: the first `n` encoded bits
  have hlen : t.length = n := by simp [htdef]
  have hnodelen : ((encodeUpTo q t n).take n).length = n := by
    rw [List.length_take, length_encodeUpTo]
    exact Nat.min_eq_left (le_chunkStartQ hne n)
  refine ⟨(encodeUpTo q t n).take n, hnodelen, ?_⟩
  rw [treeMem_chunkTreeName, chunkNodeB_iff]
  exact ⟨n, le_of_eq hnodelen.symm, t, ht, hcoh, List.take_prefix n _⟩

/-- The compiled tree is in `WKL`'s domain on every promised system. -/
theorem wkl_dom_chunkTreeName {q : Baire} (hne : FibersNonempty q)
    (hB : BondsIntoFiber q) : WKL.Dom (chunkTreeName q) :=
  WKL.dom_iff.mpr ⟨isPrefixClosed_chunkTreeName hne, isInfiniteTree_chunkTreeName hne hB⟩

/-! ### Decoding a path -/

/-- The index the path's level-`k` chunk selects. -/
def pathIdx (q : Baire) (bits : ℕ → Bool) (k : ℕ) : ℕ :=
  bitsToNat ((List.range (efilcWidth q k)).map fun j => bits (chunkStartQ q k + j))

/-- The section value the path selects at level `k`. -/
def pathSectionValue (q : Baire) (bits : ℕ → Bool) (k : ℕ) : ℕ :=
  efilcElem q k (pathIdx q bits k)

/-- **The decoding lemma**: a path through the compiled tree pins the decoder's chunk
indices, up to any level bound, to those of one in-range coherent tuple. -/
theorem exists_tuple_decoding {q : Baire} (hne : FibersNonempty q) {π : Cantor}
    (hpath : ∀ n, TreeMem (chunkTreeName q) (streamTake π n)) (n : ℕ) :
    ∃ j t, t ∈ efilcTuples q j ∧ tupleCoherentB q t = true ∧ n < j ∧
      ∀ k ≤ n, pathIdx q π k = t.getD k 0 := by
  have hw := (treeMem_chunkTreeName.mp (hpath (chunkStartQ q (n + 1))))
  rw [chunkNodeB_iff] at hw
  obtain ⟨j, hj, t, ht, hcoh, hpre⟩ := hw
  have hwlen : (streamTake π (chunkStartQ q (n + 1))).length = chunkStartQ q (n + 1) := by
    simp
  have htlen : t.length = j := ((mem_efilcTuples q j t).mp ht).1
  have hn : n < j := by
    by_contra hle
    have h1 : chunkStartQ q (n + 1) ≤ (encodeUpTo q t j).length := by
      have := hpre.length_le
      omega
    rw [length_encodeUpTo] at h1
    have h2 : chunkStartQ q j ≤ chunkStartQ q n := chunkStartQ_le (by omega)
    have h3 : chunkStartQ q n < chunkStartQ q (n + 1) := chunkStartQ_lt hne (by omega)
    omega
  refine ⟨j, t, ht, hcoh, hn, fun k hk => ?_⟩
  have hrange := ((mem_efilcTuples q j t).mp ht).2
  have hklt : t.getD k 0 < efilcWidth q k := by
    have hkj : k < t.length := by omega
    have := hrange k hkj
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkj, Option.getD_some]
  -- the path's chunk-`k` bits are the tuple's chunk-`k` block
  have hchunk : ((List.range (efilcWidth q k)).map fun j' => π (chunkStartQ q k + j')) =
      chunkBits (efilcWidth q k) (t.getD k 0) := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    have hi : i < efilcWidth q k := by simpa using h1
    have hpos : chunkStartQ q k + i < chunkStartQ q (n + 1) := by
      have hle1 : chunkStartQ q (k + 1) ≤ chunkStartQ q (n + 1) := chunkStartQ_le (by omega)
      have h2' : chunkStartQ q (k + 1) = chunkStartQ q k + efilcWidth q k := rfl
      omega
    have hbit : π (chunkStartQ q k + i) =
        (streamTake π (chunkStartQ q (n + 1))).getD (chunkStartQ q k + i) false :=
      (streamTake_getD π hpos).symm
    have hbit2 : (streamTake π (chunkStartQ q (n + 1))).getD (chunkStartQ q k + i) false =
        (encodeUpTo q t j).getD (chunkStartQ q k + i) false := by
      obtain ⟨r, hr⟩ := hpre
      rw [← hr, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by rw [hwlen]; omega)]
    have hbit3 := getD_encodeUpTo q t (m := j) (by omega : k < j) hi
    have hgetElem : ((List.range (efilcWidth q k)).map
        fun j' => π (chunkStartQ q k + j'))[i] = π (chunkStartQ q k + i) := by
      simp
    rw [hgetElem, hbit, hbit2, hbit3, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]
  rw [pathIdx, hchunk, bitsToNat_chunkBits]
  exact Nat.mod_eq_of_lt (lt_trans hklt (Nat.lt_two_pow_self))

/-- **Paths decode to sections**: on a promised system, any path through the compiled
tree decodes to a section. -/
theorem isEfilcSection_of_path {q : Baire} (hne : FibersNonempty q) {π : Cantor}
    (hpath : ∀ n, TreeMem (chunkTreeName q) (streamTake π n)) :
    IsEfilcSection q (fun k => pathSectionValue q π k) := by
  constructor
  · intro k
    obtain ⟨j, t, ht, hcoh, hn, hidx⟩ := exists_tuple_decoding hne hpath k
    have htlen : t.length = j := ((mem_efilcTuples q j t).mp ht).1
    have hklt : t.getD k 0 < efilcWidth q k := by
      have hkj : k < t.length := by omega
      have := ((mem_efilcTuples q j t).mp ht).2 k hkj
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkj, Option.getD_some]
    change efilcElem q k (pathIdx q π k) ∈ efilcFiber q k
    rw [hidx k le_rfl, efilcElem, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hklt, Option.getD_some]
    exact List.getElem_mem hklt
  · intro k
    obtain ⟨j, t, ht, hcoh, hn, hidx⟩ := exists_tuple_decoding hne hpath (k + 1)
    have htlen : t.length = j := ((mem_efilcTuples q j t).mp ht).1
    have hcoh' := tupleCoherentB_iff.mp hcoh k (by omega)
    change efilcBond q k (efilcElem q (k + 1) (pathIdx q π (k + 1))) =
      efilcElem q k (pathIdx q π k)
    rw [hidx (k + 1) le_rfl, hidx k (by omega)]
    exact hcoh'

/-! ### Reading the system off a prefix table

The codes below access the presented system only through the stream `Baire.ofList P` a
prefix list `P` presents, so a congruence lemma converts their outputs to the semantic
values once the prefix covers the accessed positions: the fiber positions below the word
length, and the bond positions of the fiber elements just read. -/

theorem efilcFiber_congr {q₁ q₂ : Baire} {k : ℕ}
    (h : q₁ (Nat.pair 0 k) = q₂ (Nat.pair 0 k)) : efilcFiber q₁ k = efilcFiber q₂ k := by
  rw [efilcFiber, efilcFiber, h]

theorem efilcTuples_congr {q₁ q₂ : Baire} {j : ℕ}
    (h : ∀ k < j, efilcFiber q₁ k = efilcFiber q₂ k) :
    efilcTuples q₁ j = efilcTuples q₂ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [efilcTuples, efilcTuples, ih fun k hk => h k (by omega)]
    have hw : efilcWidth q₁ j = efilcWidth q₂ j := by
      rw [efilcWidth, efilcWidth, h j (by omega)]
    rw [hw]

theorem chunkStartQ_congr {q₁ q₂ : Baire} {m : ℕ}
    (h : ∀ k < m, efilcFiber q₁ k = efilcFiber q₂ k) :
    chunkStartQ q₁ m = chunkStartQ q₂ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : chunkStartQ q₁ (m + 1) = chunkStartQ q₁ m + efilcWidth q₁ m := rfl
    have h2 : chunkStartQ q₂ (m + 1) = chunkStartQ q₂ m + efilcWidth q₂ m := rfl
    have hw : efilcWidth q₁ m = efilcWidth q₂ m := by
      rw [efilcWidth, efilcWidth, h m (by omega)]
    rw [h1, h2, ih fun k hk => h k (by omega), hw]

theorem encodeUpTo_width_congr {q₁ q₂ : Baire} {t : List ℕ} {m : ℕ}
    (h : ∀ k < m, efilcFiber q₁ k = efilcFiber q₂ k) :
    encodeUpTo q₁ t m = encodeUpTo q₂ t m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hw : efilcWidth q₁ m = efilcWidth q₂ m := by
      rw [efilcWidth, efilcWidth, h m (by omega)]
    rw [encodeUpTo_succ, encodeUpTo_succ, ih fun k hk => h k (by omega), hw]

/-- **The node-test congruence**: two presentations agreeing on the fibers below the word
length, and on the bonds of those fibers' elements, decide the same nodes. -/
theorem chunkNodeB_congr {q₁ q₂ : Baire} {w : List Bool}
    (hfib : ∀ k ≤ w.length, efilcFiber q₁ k = efilcFiber q₂ k)
    (hbond : ∀ i, i + 1 ≤ w.length → ∀ x ∈ efilcFiber q₂ (i + 1),
      efilcBond q₁ i x = efilcBond q₂ i x) :
    chunkNodeB q₁ w = chunkNodeB q₂ w := by
  rw [Bool.eq_iff_iff, chunkNodeB_iff, chunkNodeB_iff]
  have htup : ∀ j ≤ w.length, efilcTuples q₁ j = efilcTuples q₂ j := fun j hj =>
    efilcTuples_congr fun k hk => hfib k (by omega)
  have helem : ∀ k ≤ w.length, ∀ i, efilcElem q₁ k i = efilcElem q₂ k i := by
    intro k hk i
    rw [efilcElem, efilcElem, hfib k hk]
  have hcoh : ∀ j ≤ w.length, ∀ t ∈ efilcTuples q₂ j,
      (tupleCoherentB q₁ t = true ↔ tupleCoherentB q₂ t = true) := by
    intro j hj t ht
    obtain ⟨hlen, hmem⟩ := (mem_efilcTuples q₂ j t).mp ht
    rw [tupleCoherentB_iff, tupleCoherentB_iff]
    refine forall_congr' fun i => ?_
    refine imp_congr_right fun hi => ?_
    have hi1 : i + 1 < t.length := hi
    have hidx : t.getD (i + 1) 0 = t[i + 1]'hi1 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1, Option.getD_some]
    have hx : efilcElem q₂ (i + 1) (t.getD (i + 1) 0) ∈ efilcFiber q₂ (i + 1) := by
      have hr : t[i + 1]'hi1 < (efilcFiber q₂ (i + 1)).length := hmem (i + 1) hi1
      rw [efilcElem, hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
        Option.getD_some]
      exact List.getElem_mem hr
    rw [helem (i + 1) (by omega), helem i (by omega),
      hbond i (by omega) _ hx]
  constructor
  · rintro ⟨j, hj, t, ht, hc, hpre⟩
    rw [htup j hj] at ht
    refine ⟨j, hj, t, ht, (hcoh j hj t ht).mp hc, ?_⟩
    rwa [encodeUpTo_width_congr fun k hk => (hfib k (by omega)).symm]
  · rintro ⟨j, hj, t, ht, hc, hpre⟩
    refine ⟨j, hj, t, (htup j hj).symm ▸ ht, (hcoh j hj t ht).mpr hc, ?_⟩
    rwa [encodeUpTo_width_congr fun k hk => hfib k (by omega)]

/-! ### Primitive recursiveness of the table-driven node test -/

private theorem primrec_tableFiber :
    Primrec₂ fun (P : List ℕ) (k : ℕ) => efilcFiber (ofList P) k :=
  (Primrec.ofNat (List ℕ)).comp ((Primrec.list_getD 0).comp Primrec.fst
    (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd))

private theorem primrec_tableWidth :
    Primrec₂ fun (P : List ℕ) (k : ℕ) => efilcWidth (ofList P) k :=
  Primrec.list_length.comp primrec_tableFiber

private theorem primrec_tableElem :
    Primrec fun z : (List ℕ × ℕ) × ℕ => efilcElem (ofList z.1.1) z.1.2 z.2 :=
  (Primrec.list_getD 0).comp
    (primrec_tableFiber.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    Primrec.snd

private theorem primrec_tableBond :
    Primrec fun z : (List ℕ × ℕ) × ℕ => efilcBond (ofList z.1.1) z.1.2 z.2 :=
  (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
    (Primrec₂.natPair.comp (Primrec.const 1)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd))

private theorem efilcTuples_eq_nat_rec (q : Baire) (j : ℕ) :
    efilcTuples q j = Nat.rec (motive := fun _ => List (List ℕ)) [[]]
      (fun m IH => IH.flatMap fun t =>
        (List.range (efilcWidth q m)).map fun i => t ++ [i]) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [efilcTuples, ih]

private theorem primrec_tableTuples :
    Primrec₂ fun (P : List ℕ) (j : ℕ) => efilcTuples (ofList P) j := by
  have hinner : Primrec₂ fun (z : List ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
      (List.range (efilcWidth (ofList z.1) z.2.1)).map fun i => t ++ [i] :=
    Primrec.list_map
      (f := fun w : (List ℕ × ℕ × List (List ℕ)) × List ℕ =>
        List.range (efilcWidth (ofList w.1.1) w.1.2.1))
      (g := fun (w : (List ℕ × ℕ × List (List ℕ)) × List ℕ) (i : ℕ) => w.2 ++ [i])
      (Primrec.list_range.comp
        (primrec_tableWidth.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
      ((Primrec.list_concat.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂)
  have hg : Primrec₂ fun (P : List ℕ) (z : ℕ × List (List ℕ)) =>
      z.2.flatMap fun t =>
        (List.range (efilcWidth (ofList P) z.1)).map fun i => t ++ [i] :=
    Primrec.list_flatMap (f := fun z : List ℕ × ℕ × List (List ℕ) => z.2.2)
      (g := fun (z : List ℕ × ℕ × List (List ℕ)) (t : List ℕ) =>
        (List.range (efilcWidth (ofList z.1) z.2.1)).map fun i => t ++ [i])
      (Primrec.snd.comp Primrec.snd) hinner
  exact (Primrec.nat_rec (Primrec.const [[]]) hg).of_eq fun P j =>
    (efilcTuples_eq_nat_rec (ofList P) j).symm

private theorem primrec_tableCoherent :
    Primrec₂ fun (P : List ℕ) (t : List ℕ) => tupleCoherentB (ofList P) t :=
  primrec_list_all
    (f := fun z : List ℕ × List ℕ => List.range (z.2.length - 1))
    (p := fun (z : List ℕ × List ℕ) (i : ℕ) =>
      decide (efilcBond (ofList z.1) i (efilcElem (ofList z.1) (i + 1) (z.2.getD (i + 1) 0)) =
        efilcElem (ofList z.1) i (z.2.getD i 0)))
    (Primrec.list_range.comp
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1)))
    ((PrimrecRel.comp Primrec.eq
      (primrec_tableBond.comp
        ((Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
          (primrec_tableElem.comp
            ((Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.succ.comp Primrec.snd)).pair
              ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
                (Primrec.succ.comp Primrec.snd))))))
      (primrec_tableElem.comp
        ((Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
          ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
            Primrec.snd)))).decide.to₂)

private theorem chunkBits_eq_div_mod (w i : ℕ) :
    chunkBits w i = (List.range w).map fun j => decide (i / 2 ^ j % 2 = 1) := by
  rw [chunkBits]
  refine List.map_congr_left fun j _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (i / 2 ^ j) with h | h <;>
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two, h]

private theorem primrec_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem primrec_chunkBits : Primrec₂ chunkBits := by
  have h : Primrec fun p : ℕ × ℕ =>
      (List.range p.1).map fun j => decide (p.2 / 2 ^ j % 2 = 1) :=
    Primrec.list_map (f := fun p : ℕ × ℕ => List.range p.1)
      (g := fun (p : ℕ × ℕ) (j : ℕ) => decide (p.2 / 2 ^ j % 2 = 1))
      (Primrec.list_range.comp Primrec.fst)
      ((PrimrecRel.comp Primrec.eq
        (Primrec.nat_mod.comp
          (Primrec.nat_div.comp (Primrec.snd.comp Primrec.fst)
            (primrec_natPow.comp (Primrec.const 2) Primrec.snd))
          (Primrec.const 2))
        (Primrec.const 1)).decide.to₂)
  exact h.of_eq fun p => (chunkBits_eq_div_mod p.1 p.2).symm

private theorem primrec_tableEncode :
    Primrec fun z : (List ℕ × List ℕ) × ℕ => encodeUpTo (ofList z.1.1) z.1.2 z.2 :=
  Primrec.list_flatMap
    (f := fun z : (List ℕ × List ℕ) × ℕ => List.range z.2)
    (g := fun (z : (List ℕ × List ℕ) × ℕ) (i : ℕ) =>
      chunkBits (efilcWidth (ofList z.1.1) i) (z.1.2.getD i 0))
    (Primrec.list_range.comp Primrec.snd)
    ((primrec_chunkBits.comp
      (primrec_tableWidth.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)).to₂)

private theorem primrec_tableNode :
    Primrec₂ fun (P : List ℕ) (w : List Bool) => chunkNodeB (ofList P) w :=
  primrec_list_any
    (f := fun z : List ℕ × List Bool => List.range (z.2.length + 1))
    (p := fun (z : List ℕ × List Bool) (j : ℕ) =>
      (efilcTuples (ofList z.1) j).any fun t =>
        tupleCoherentB (ofList z.1) t &&
          decide (z.2 = (encodeUpTo (ofList z.1) t j).take z.2.length))
    (Primrec.list_range.comp (Primrec.succ.comp (Primrec.list_length.comp Primrec.snd)))
    ((primrec_list_any
      (f := fun y : (List ℕ × List Bool) × ℕ => efilcTuples (ofList y.1.1) y.2)
      (p := fun (y : (List ℕ × List Bool) × ℕ) (t : List ℕ) =>
        tupleCoherentB (ofList y.1.1) t &&
          decide (y.1.2 = (encodeUpTo (ofList y.1.1) t y.2).take y.1.2.length))
      (primrec_tableTuples.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.and.comp
        (primrec_tableCoherent.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
          Primrec.snd)
        (PrimrecRel.comp Primrec.eq
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
          (Primrec.list_take.comp
            (Primrec.list_length.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
            (primrec_tableEncode.comp
              ((Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
                Primrec.snd).pair
                (Primrec.snd.comp Primrec.fst))))).decide).to₂)).to₂)

/-! ### The tree code -/

/-- A prefix length covering the fiber positions below the decoded word's length. -/
def fiberPosBound (m : ℕ) : ℕ :=
  prefixBound ((List.range ((treeWordDecode m).length + 1)).map fun k => Nat.pair 0 k)

theorem fiberPos_lt_fiberPosBound {m k : ℕ} (h : k ≤ (treeWordDecode m).length) :
    Nat.pair 0 k < fiberPosBound m :=
  lt_prefixBound_of_mem (List.mem_map_of_mem (List.mem_range.mpr (by omega)))

/-- A prefix length additionally covering the bond positions of the fiber elements the
first-stage prefix presents. -/
def bondPosBound (m : ℕ) (P : List ℕ) : ℕ :=
  max (fiberPosBound m)
    (prefixBound ((List.range (treeWordDecode m).length).flatMap fun i =>
      (efilcFiber (ofList P) (i + 1)).map fun x => Nat.pair 1 (Nat.pair i x)))

theorem bondPos_lt_bondPosBound {m : ℕ} {P : List ℕ} {i x : ℕ}
    (hi : i < (treeWordDecode m).length) (hx : x ∈ efilcFiber (ofList P) (i + 1)) :
    Nat.pair 1 (Nat.pair i x) < bondPosBound m P :=
  lt_of_lt_of_le
    (lt_prefixBound_of_mem (List.mem_flatMap.mpr
      ⟨i, List.mem_range.mpr hi, List.mem_map_of_mem hx⟩))
    (le_max_right _ _)

/-- A single code produces the compiled tree name: fibers from a primitively bounded
prefix, bonds from an adaptively recomputed one, then the pure node test. -/
theorem exists_chunkTreeCode : ∃ K : OracleCode, ∀ q : Baire,
    chunkTreeName q ∈ K.evalStream q := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hb₀ : Primrec fiberPosBound :=
    primrec_prefixBound.comp (Primrec.list_map
      (f := fun m : ℕ => List.range ((treeWordDecode m).length + 1))
      (g := fun (_ : ℕ) (k : ℕ) => Nat.pair 0 k)
      (Primrec.list_range.comp (Primrec.succ.comp
        (Primrec.list_length.comp primrec_treeWordDecode)))
      ((Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd).to₂))
  have hflat : Primrec fun p : ℕ × ℕ =>
      (List.range (treeWordDecode p.1).length).flatMap fun i =>
        (efilcFiber (ofList (ofNat (List ℕ) p.2)) (i + 1)).map fun x =>
          Nat.pair 1 (Nat.pair i x) :=
    Primrec.list_flatMap
      (f := fun p : ℕ × ℕ => List.range (treeWordDecode p.1).length)
      (g := fun (p : ℕ × ℕ) (i : ℕ) =>
        (efilcFiber (ofList (ofNat (List ℕ) p.2)) (i + 1)).map fun x =>
          Nat.pair 1 (Nat.pair i x))
      (Primrec.list_range.comp
        (Primrec.list_length.comp (primrec_treeWordDecode.comp Primrec.fst)))
      ((Primrec.list_map
        (f := fun y : (ℕ × ℕ) × ℕ =>
          efilcFiber (ofList (ofNat (List ℕ) y.1.2)) (y.2 + 1))
        (g := fun (y : (ℕ × ℕ) × ℕ) (x : ℕ) => Nat.pair 1 (Nat.pair y.2 x))
        (primrec_tableFiber.comp
          ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.fst))
          (Primrec.succ.comp Primrec.snd))
        ((Primrec₂.natPair.comp (Primrec.const 1)
          (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂)).to₂)
  have hb₁ : Primrec₂ fun (m : ℕ) (e : ℕ) => bondPosBound m (ofNat (List ℕ) e) :=
    (Primrec.nat_max.comp (hb₀.comp Primrec.fst) (primrec_prefixBound.comp hflat)).to₂
  have hb₂ : Primrec₂ fun (_ : ℕ) (e : ℕ) => (ofNat (List ℕ) e).length :=
    ((Primrec.list_length.comp ((Primrec.ofNat (List ℕ)).comp Primrec.snd)).to₂)
  have hg : Primrec fun v : ℕ =>
      if chunkNodeB (ofList (ofNat (List ℕ) v.unpair.2)) (treeWordDecode v.unpair.1)
        then 1 else 0 :=
    Primrec.ite
      (Primrec.eq.comp
        (primrec_tableNode.comp ((Primrec.ofNat (List ℕ)).comp hu2)
          (primrec_treeWordDecode.comp hu1))
        (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixChainCode (b₀ := fiberPosBound)
    (b₁ := fun m e => bondPosBound m (ofNat (List ℕ) e))
    (b₂ := fun _ e => (ofNat (List ℕ) e).length) hb₀ hb₁ hb₂ hg
  refine ⟨K, fun q => OracleCode.mem_evalStream.mpr fun m => ?_⟩
  rw [hK q m, Part.mem_some_iff]
  simp only [Denumerable.ofNat_encode, Nat.unpair_pair, length_streamTake]
  set N : ℕ := bondPosBound m (streamTake q (fiberPosBound m)) with hN
  have hcongr : chunkNodeB (ofList (streamTake q N)) (treeWordDecode m)
      = chunkNodeB q (treeWordDecode m) := by
    have hNfib : fiberPosBound m ≤ N := le_max_left _ _
    refine chunkNodeB_congr (fun k hk => ?_) (fun i hi x hx => ?_)
    · exact efilcFiber_congr
        (Baire.ofList_streamTake q (lt_of_lt_of_le (fiberPos_lt_fiberPosBound hk) hNfib))
    · have hfib1 : efilcFiber (ofList (streamTake q (fiberPosBound m))) (i + 1) =
          efilcFiber q (i + 1) := by
        exact efilcFiber_congr (Baire.ofList_streamTake q (fiberPos_lt_fiberPosBound hi))
      have hpos : Nat.pair 1 (Nat.pair i x) < N :=
        bondPos_lt_bondPosBound (by omega) (hfib1 ▸ hx)
      exact Baire.ofList_streamTake q hpos
  rw [chunkTreeName, hcongr]

/-- The tree code, extracted once so consumers share a single combinator. Specified, not
constructed. -/
noncomputable def chunkTreeCode : OracleCode := Classical.choose exists_chunkTreeCode

/-- **Specification of `chunkTreeCode`**: on any name it produces the compiled tree. -/
theorem mem_evalStream_chunkTreeCode (q : Baire) :
    chunkTreeName q ∈ chunkTreeCode.evalStream q :=
  Classical.choose_spec exists_chunkTreeCode q

/-! ### The section code -/

/-- The section read off the interleaved input-and-answer stream: system data on the even
track, path bits on the odd track. This is the ordinary postprocessor's shape — it
consults the *input* for the chunk widths, which is exactly what makes this direction
`≤W` rather than `≤sW`. -/
def sectionFromF (F : Baire) : Baire := fun k =>
  pathSectionValue (Baire.evenPart F) (fun n => Baire.oddPart F n == 1) k

/-- The even-track table view of a prefix list. -/
def evenTable (P : List ℕ) : Baire := fun n => P.getD (2 * n) 0

private theorem chunkStartQ_eq_nat_rec (q : Baire) (k : ℕ) :
    chunkStartQ q k = Nat.rec (motive := fun _ => ℕ) 0
      (fun m ih => ih + efilcWidth q m) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : chunkStartQ q (k + 1) = chunkStartQ q k + efilcWidth q k := rfl
    rw [h1, ih]

private theorem primrec_evenFiber :
    Primrec₂ fun (P : List ℕ) (k : ℕ) => efilcFiber (evenTable P) k :=
  (Primrec.ofNat (List ℕ)).comp ((Primrec.list_getD 0).comp Primrec.fst
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd)))

private theorem primrec_evenWidth :
    Primrec₂ fun (P : List ℕ) (k : ℕ) => efilcWidth (evenTable P) k :=
  Primrec.list_length.comp primrec_evenFiber

private theorem primrec_evenChunkStart :
    Primrec₂ fun (P : List ℕ) (k : ℕ) => chunkStartQ (evenTable P) k := by
  have hstep : Primrec₂ fun (P : List ℕ) (z : ℕ × ℕ) => z.2 + efilcWidth (evenTable P) z.1 :=
    ((Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (primrec_evenWidth.comp Primrec.fst (Primrec.fst.comp Primrec.snd))))
  exact (Primrec.nat_rec (Primrec.const 0) hstep).of_eq fun P k =>
    (chunkStartQ_eq_nat_rec (evenTable P) k).symm

private theorem bitsToNat_eq_foldr (l : List Bool) :
    bitsToNat l = l.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0 := by
  induction l with
  | nil => rfl
  | cons b t ih => rw [List.foldr_cons, ← ih]; rfl

private theorem primrec_bitsToNat : Primrec bitsToNat := by
  have h : Primrec fun l : List Bool =>
      l.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0 :=
    Primrec.list_foldr (f := fun l : List Bool => l) (g := fun _ : List Bool => (0 : ℕ))
      (h := fun (_ : List Bool) (p : Bool × ℕ) => (if p.1 then 1 else 0) + 2 * p.2)
      Primrec.id (Primrec.const 0)
      ((Primrec.nat_add.comp
        (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const true))
          (Primrec.const 1) (Primrec.const 0))
        (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))).to₂)
  exact h.of_eq fun l => (bitsToNat_eq_foldr l).symm

/-- A prefix length covering the even-track fiber positions below level `k`. -/
def evenFiberBound (k : ℕ) : ℕ :=
  2 * prefixBound ((List.range (k + 1)).map fun i => Nat.pair 0 i) + 1

theorem evenPos_lt_evenFiberBound {k i : ℕ} (h : i ≤ k) :
    2 * Nat.pair 0 i < evenFiberBound k := by
  have hmem : Nat.pair 0 i ∈ (List.range (k + 1)).map fun j => Nat.pair 0 j :=
    List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le h))
  have := lt_prefixBound_of_mem hmem
  rw [evenFiberBound]
  omega

/-- A prefix length additionally covering the odd-track bit positions of the first
`k + 1` chunks, with the widths read from the first-stage prefix. -/
def oddBitBound (k : ℕ) (P : List ℕ) : ℕ :=
  max (evenFiberBound k) (2 * chunkStartQ (evenTable P) (k + 1) + 2)

/-- A single code produces the decoded section from the interleaved stream. -/
theorem exists_treeSectionCode : ∃ H : OracleCode, ∀ F : Baire,
    sectionFromF F ∈ H.evalStream F := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hb₀ : Primrec evenFiberBound :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (primrec_prefixBound.comp (Primrec.list_map
        (f := fun k : ℕ => List.range (k + 1))
        (g := fun (_ : ℕ) (i : ℕ) => Nat.pair 0 i)
        (Primrec.list_range.comp Primrec.succ)
        ((Primrec₂.natPair.comp (Primrec.const 0) Primrec.snd).to₂))))
  have hb₁ : Primrec₂ fun (k : ℕ) (e : ℕ) => oddBitBound k (ofNat (List ℕ) e) :=
    ((Primrec.nat_max.comp (hb₀.comp Primrec.fst)
      (Primrec.succ.comp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (primrec_evenChunkStart.comp ((Primrec.ofNat (List ℕ)).comp Primrec.snd)
          (Primrec.succ.comp Primrec.fst))))))).to₂
  have hb₂ : Primrec₂ fun (_ : ℕ) (e : ℕ) => (ofNat (List ℕ) e).length :=
    ((Primrec.list_length.comp ((Primrec.ofNat (List ℕ)).comp Primrec.snd)).to₂)
  have hg : Primrec fun v : ℕ =>
      efilcElem (evenTable (ofNat (List ℕ) v.unpair.2)) v.unpair.1
        (bitsToNat ((List.range (efilcWidth (evenTable (ofNat (List ℕ) v.unpair.2))
            v.unpair.1)).map
          fun j => (ofNat (List ℕ) v.unpair.2).getD
            (2 * (chunkStartQ (evenTable (ofNat (List ℕ) v.unpair.2)) v.unpair.1 + j) + 1)
            0 == 1)) := by
    have hP : Primrec fun v : ℕ => (ofNat (List ℕ) v.unpair.2 : List ℕ) :=
      (Primrec.ofNat (List ℕ)).comp hu2
    have hbits : Primrec fun v : ℕ =>
        (List.range (efilcWidth (evenTable (ofNat (List ℕ) v.unpair.2)) v.unpair.1)).map
          fun j => (ofNat (List ℕ) v.unpair.2).getD
            (2 * (chunkStartQ (evenTable (ofNat (List ℕ) v.unpair.2)) v.unpair.1 + j) + 1)
            0 == 1 :=
      Primrec.list_map
        (f := fun v : ℕ =>
          List.range (efilcWidth (evenTable (ofNat (List ℕ) v.unpair.2)) v.unpair.1))
        (g := fun (v : ℕ) (j : ℕ) => (ofNat (List ℕ) v.unpair.2).getD
          (2 * (chunkStartQ (evenTable (ofNat (List ℕ) v.unpair.2)) v.unpair.1 + j) + 1)
          0 == 1)
        (Primrec.list_range.comp (primrec_evenWidth.comp hP hu1))
        ((Primrec.beq.comp
          ((Primrec.list_getD 0).comp (hP.comp Primrec.fst)
            (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
              (Primrec.nat_add.comp
                (primrec_evenChunkStart.comp (hP.comp Primrec.fst)
                  (hu1.comp Primrec.fst))
                Primrec.snd))))
          (Primrec.const 1)).to₂)
    exact (Primrec.list_getD 0).comp (primrec_evenFiber.comp hP hu1)
      (primrec_bitsToNat.comp hbits)
  obtain ⟨H, hH⟩ := OracleCode.exists_prefixChainCode (b₀ := evenFiberBound)
    (b₁ := fun k e => oddBitBound k (ofNat (List ℕ) e))
    (b₂ := fun _ e => (ofNat (List ℕ) e).length) hb₀ hb₁ hb₂ hg
  refine ⟨H, fun F => OracleCode.mem_evalStream.mpr fun k => ?_⟩
  rw [hH F k, Part.mem_some_iff]
  simp only [Denumerable.ofNat_encode, Nat.unpair_pair, length_streamTake]
  set N : ℕ := oddBitBound k (streamTake F (evenFiberBound k)) with hN
  have hNfib : evenFiberBound k ≤ N := le_max_left _ _
  -- the fibers below level `k` agree between the table view and the even part
  have hfib : ∀ i ≤ k,
      efilcFiber (evenTable (streamTake F N)) i = efilcFiber (Baire.evenPart F) i := by
    intro i hi
    refine efilcFiber_congr ?_
    change (streamTake F N).getD (2 * Nat.pair 0 i) 0 = F (2 * Nat.pair 0 i)
    exact streamTake_getD F (lt_of_lt_of_le (evenPos_lt_evenFiberBound hi) hNfib)
  have hfib0 : ∀ i ≤ k,
      efilcFiber (evenTable (streamTake F (evenFiberBound k))) i =
        efilcFiber (Baire.evenPart F) i := by
    intro i hi
    refine efilcFiber_congr ?_
    change (streamTake F (evenFiberBound k)).getD (2 * Nat.pair 0 i) 0 =
      F (2 * Nat.pair 0 i)
    exact streamTake_getD F (evenPos_lt_evenFiberBound hi)
  have hwidth : efilcWidth (evenTable (streamTake F N)) k =
      efilcWidth (Baire.evenPart F) k := by
    rw [efilcWidth, efilcWidth, hfib k le_rfl]
  have hstart : chunkStartQ (evenTable (streamTake F N)) k =
      chunkStartQ (Baire.evenPart F) k :=
    chunkStartQ_congr fun i hi => hfib i hi.le
  have hstart1 : chunkStartQ (evenTable (streamTake F (evenFiberBound k))) (k + 1) =
      chunkStartQ (Baire.evenPart F) (k + 1) :=
    chunkStartQ_congr fun i hi => hfib0 i (Nat.lt_succ_iff.mp hi)
  -- the odd-track bit positions of the first `k + 1` chunks are covered
  have hbitpos : ∀ j < efilcWidth (Baire.evenPart F) k,
      2 * (chunkStartQ (Baire.evenPart F) k + j) + 1 < N := by
    intro j hj
    have h1 : chunkStartQ (Baire.evenPart F) k + j <
        chunkStartQ (Baire.evenPart F) (k + 1) := by
      have h2 : chunkStartQ (Baire.evenPart F) (k + 1) =
          chunkStartQ (Baire.evenPart F) k + efilcWidth (Baire.evenPart F) k := rfl
      omega
    have h3 : 2 * chunkStartQ (evenTable (streamTake F (evenFiberBound k))) (k + 1) + 2
        ≤ N := le_max_right _ _
    rw [hstart1] at h3
    omega
  -- assemble the value equality
  change efilcElem (Baire.evenPart F) k
      (pathIdx (Baire.evenPart F) (fun n => Baire.oddPart F n == 1) k) = _
  rw [efilcElem, efilcElem, hfib k le_rfl, pathIdx, hwidth, hstart]
  have hlist : ((List.range (efilcWidth (Baire.evenPart F) k)).map
      fun j => (Baire.oddPart F (chunkStartQ (Baire.evenPart F) k + j) == 1)) =
      (List.range (efilcWidth (Baire.evenPart F) k)).map
        fun j => (streamTake F N).getD
          (2 * (chunkStartQ (Baire.evenPart F) k + j) + 1) 0 == 1 := by
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < efilcWidth (Baire.evenPart F) k := List.mem_range.mp hj
    have heq : Baire.oddPart F (chunkStartQ (Baire.evenPart F) k + j) =
        (streamTake F N).getD (2 * (chunkStartQ (Baire.evenPart F) k + j) + 1) 0 :=
      (streamTake_getD F (hbitpos j hj')).symm
    rw [heq]
  rw [hlist]

/-- The section code, extracted once so consumers share a single combinator. Specified,
not constructed. -/
noncomputable def treeSectionCode : OracleCode := Classical.choose exists_treeSectionCode

/-- **Specification of `treeSectionCode`**: on any interleaved stream it produces the
decoded section. -/
theorem mem_evalStream_treeSectionCode (F : Baire) :
    sectionFromF F ∈ treeSectionCode.evalStream F :=
  Classical.choose_spec exists_treeSectionCode F

/-! ### The reduction -/

theorem sectionFromF_interleave (q a : Baire) :
    sectionFromF (Baire.interleave q a) =
      fun k => pathSectionValue q (fun n => a n == 1) k := by
  funext k
  simp only [sectionFromF, Baire.evenPart_interleave, Baire.oddPart_interleave]

/-- **`EFILC ≤W WKL`, as an explicit pair**: `chunkTreeCode` compiles the chunk-coded
tree, and `treeSectionCode` decodes any accepted path into a section, consulting the
original input for the chunk widths. -/
theorem isReductionPair_efilc_le_wkl :
    IsReductionPair EFILC WKL chunkTreeCode treeSectionCode := by
  intro p x hpx hdom
  obtain rfl : x = p := baireRep_names_iff.mp hpx
  obtain ⟨hne, hB⟩ := EFILC.dom_iff.mp hdom
  refine ⟨chunkTreeName x, mem_evalStream_chunkTreeCode x, chunkTreeName x,
    baireRep_names_iff.mpr rfl, wkl_dom_chunkTreeName hne hB, ?_⟩
  intro a π hay hacc
  obtain ⟨-, rfl⟩ := cantorRep_names_iff.mp hay
  obtain ⟨-, -, hpath⟩ := WKL.accepts_iff.mp hacc
  refine ⟨sectionFromF (Baire.interleave x a), mem_evalStream_treeSectionCode _,
    sectionFromF (Baire.interleave x a), baireRep_names_iff.mpr rfl, ?_⟩
  rw [sectionFromF_interleave]
  exact EFILC.accepts_iff.mpr ⟨hne, hB, isEfilcSection_of_path hne hpath⟩

/-- **Explicit finite inverse-limit compactness reduces ordinarily to weak Kőnig's
lemma.** -/
theorem efilc_le_wkl : EFILC ≤W WKL :=
  reduction_iff_exists_reductionPair.mpr ⟨_, _, isReductionPair_efilc_le_wkl⟩

end ComputableAnalysis
