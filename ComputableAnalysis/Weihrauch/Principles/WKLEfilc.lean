/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Principles.EFILC
import ComputableAnalysis.Weihrauch.Principles.WKLReduction

/-!
# `WKL ≤sW EFILC`: levels as fibers, truncation as bond

`wkl_le_efilc : WKL ≤sW EFILC`, with the explicit reduction pair
`isStrongReductionPair_wkl_le_efilc` over the named codes `treeSystemCode` and
`sectionPathCode`.

The preprocessor compiles a presented tree into the inverse system of its **levels**: the
level-`k` fiber enumerates the codes of the level-`k` nodes, and the bond truncates the
decoded word — no chunk coding, because fiber elements are node codes rather than bits.
The postprocessor reads the path **off the section answer alone**: the level-`(n + 1)`
section value decodes to a length-`(n + 1)` node whose entry `n` is the path bit.
**Strongness is enforced by the postprocessor's type**: `sectionPathCode` runs on the
answer stream, never on the input.

Both codes ride `OracleCode.exists_prefixPostCode`: the level-`k` fiber is decided by a
prefix of primitively computable length (`levelBound`, covering every level-`k` node
code), the bond is oracle-free, and output coordinate `n` of the path needs only the
section value at `n + 1`.

This reduction is proved from the presented promises alone — independently of any
ω-model or provability-level relationship between the corresponding statements.
-/

namespace ComputableAnalysis

open Encodable Denumerable
open OracleCode (binaryWords mem_binaryWords)

/-! ### The compiled system -/

/-- The semantic level-`k` fiber: the codes of the level-`k` nodes of `p`. -/
def treeLevel (p : Baire) (k : ℕ) : List ℕ :=
  ((binaryWords k).filter fun w => decide (p (treeWordCode w) ≠ 0)).map treeWordCode

/-- The bond of the compiled system: truncate the decoded word. Oracle-free. -/
def treeBondValue (k x : ℕ) : ℕ := treeWordCode ((treeWordDecode x).take k)

/-- The compiled system name: track `0` the level fibers, track `1` the truncation
bonds. -/
def treeSystemName (p : Baire) : Baire := fun n =>
  if n.unpair.1 = 0 then encode (treeLevel p n.unpair.2)
  else if n.unpair.1 = 1 then treeBondValue n.unpair.2.unpair.1 n.unpair.2.unpair.2
  else 0

@[simp]
theorem efilcFiber_treeSystemName (p : Baire) (k : ℕ) :
    efilcFiber (treeSystemName p) k = treeLevel p k := by
  simp [efilcFiber, treeSystemName, Nat.unpair_pair]

@[simp]
theorem efilcBond_treeSystemName (p : Baire) (k x : ℕ) :
    efilcBond (treeSystemName p) k x = treeBondValue k x := by
  simp [efilcBond, treeSystemName, Nat.unpair_pair]

theorem mem_treeLevel {p : Baire} {k x : ℕ} :
    x ∈ treeLevel p k ↔
      ∃ w : List Bool, w.length = k ∧ TreeMem p w ∧ x = treeWordCode w := by
  simp only [treeLevel, List.mem_map, List.mem_filter, mem_binaryWords,
    decide_eq_true_eq]
  constructor
  · rintro ⟨w, ⟨hlen, hmem⟩, rfl⟩
    exact ⟨w, hlen, hmem, rfl⟩
  · rintro ⟨w, hlen, hmem, rfl⟩
    exact ⟨w, ⟨hlen, hmem⟩, rfl⟩

/-- The compiled system keeps `WKL`'s promises as `EFILC`'s: levels of an infinite tree
are nonempty, and truncation lands in the level below by prefix closure. -/
theorem efilc_dom_treeSystemName {p : Baire} (hpc : IsPrefixClosed p)
    (hinf : IsInfiniteTree p) : EFILC.Dom (treeSystemName p) := by
  rw [EFILC.dom_iff]
  constructor
  · intro k
    obtain ⟨w, hw, hmem⟩ := hinf k
    rw [efilcFiber_treeSystemName]
    exact List.ne_nil_of_mem (mem_treeLevel.mpr ⟨w, hw, hmem, rfl⟩)
  · intro k x hx
    rw [efilcFiber_treeSystemName] at hx ⊢
    rw [efilcBond_treeSystemName]
    obtain ⟨w, hlen, hmem, rfl⟩ := mem_treeLevel.mp hx
    refine mem_treeLevel.mpr ⟨w.take k, ?_, ?_, ?_⟩
    · rw [List.length_take, hlen]
      omega
    · exact hpc w _ hmem (List.take_prefix k w)
    · rw [treeBondValue, treeWordDecode_treeWordCode]

/-! ### The system code -/

/-- A prefix length covering every level-`k` node code. -/
def levelBound (k : ℕ) : ℕ :=
  ((binaryWords k).map treeWordCode).foldr (fun i m => max (i + 1) m) 0

private theorem lt_foldr_max {l : List ℕ} {i : ℕ} (h : i ∈ l) :
    i < l.foldr (fun j m => max (j + 1) m) 0 := by
  induction l with
  | nil => simp at h
  | cons j t ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp only [List.foldr_cons]
      omega
    · have := ih h
      simp only [List.foldr_cons]
      omega

theorem treeWordCode_lt_levelBound {k : ℕ} {w : List Bool} (h : w ∈ binaryWords k) :
    treeWordCode w < levelBound k :=
  lt_foldr_max (List.mem_map_of_mem h)

/-- The level fiber decided from a prefix list. -/
def treeLevelFiberB (L : List ℕ) (k : ℕ) : List ℕ :=
  ((binaryWords k).filter fun w => treeMemB L w).map treeWordCode

theorem treeLevelFiberB_eq (p : Baire) {k N : ℕ} (h : levelBound k ≤ N) :
    treeLevelFiberB (streamTake p N) k = treeLevel p k := by
  rw [treeLevelFiberB, treeLevel]
  refine congrArg _ (List.filter_congr fun w hw => ?_)
  rw [treeMemB, streamTake_getD p (lt_of_lt_of_le (treeWordCode_lt_levelBound hw) h)]

private theorem primrec_decide_ne {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => decide (f a ≠ g a) := by
  obtain ⟨_, h⟩ := PrimrecRel.comp (PrimrecRel.not Primrec.eq) hf hg
  exact Primrec.of_eq h fun a => decide_eq_decide.mpr Iff.rfl

private theorem primrec_treeMemB {α : Type*} [Primcodable α] {L : α → List ℕ}
    {w : α → List Bool} (hL : Primrec L) (hw : Primrec w) :
    Primrec fun a => treeMemB (L a) (w a) :=
  primrec_decide_ne
    ((Primrec.list_getD 0).comp hL (primrec_treeWordCode.comp hw)) (Primrec.const 0)

/-- A single code produces the compiled system name. -/
theorem exists_treeSystemCode : ∃ K : OracleCode, ∀ p : Baire,
    treeSystemName p ∈ K.evalStream p := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hbound : Primrec₂ fun (n : ℕ) (_ : ℕ) => levelBound n.unpair.2 :=
    ((Primrec.list_foldr
        (Primrec.list_map (OracleCode.primrec_binaryWords.comp hu2)
          (primrec_treeWordCode.comp Primrec.snd).to₂)
        (Primrec.const 0)
        ((Primrec.nat_max.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.snd)).to₂)).comp Primrec.fst).to₂
  have hfib : Primrec fun v : ℕ =>
      encode (treeLevelFiberB (ofNat (List ℕ) v.unpair.2) v.unpair.1.unpair.2) :=
    Primrec.encode.comp (Primrec.list_map
      (primrec_list_filter (OracleCode.primrec_binaryWords.comp (hu2.comp hu1))
        ((primrec_treeMemB ((Primrec.ofNat (List ℕ)).comp (hu2.comp Primrec.fst))
          Primrec.snd).to₂))
      (primrec_treeWordCode.comp Primrec.snd).to₂)
  have hbond : Primrec fun v : ℕ =>
      treeBondValue v.unpair.1.unpair.2.unpair.1 v.unpair.1.unpair.2.unpair.2 :=
    primrec_treeWordCode.comp (Primrec.list_take.comp
      (Primrec.fst.comp (Primrec.unpair.comp (hu2.comp hu1)))
      (primrec_treeWordDecode.comp (Primrec.snd.comp (Primrec.unpair.comp (hu2.comp hu1)))))
  have hg : Primrec fun v : ℕ =>
      if v.unpair.1.unpair.1 = 0 then
        encode (treeLevelFiberB (ofNat (List ℕ) v.unpair.2) v.unpair.1.unpair.2)
      else if v.unpair.1.unpair.1 = 1 then
        treeBondValue v.unpair.1.unpair.2.unpair.1 v.unpair.1.unpair.2.unpair.2
      else 0 :=
    Primrec.ite (Primrec.eq.comp (hu1.comp hu1) (Primrec.const 0)) hfib
      (Primrec.ite (Primrec.eq.comp (hu1.comp hu1) (Primrec.const 1)) hbond
        (Primrec.const 0))
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨K, fun p => OracleCode.mem_evalStream.mpr fun n => ?_⟩
  rw [hK p n, Part.mem_some_iff, treeSystemName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  by_cases h0 : n.unpair.1 = 0
  · rw [if_pos h0, if_pos h0, treeLevelFiberB_eq p le_rfl]
  · by_cases h1 : n.unpair.1 = 1
    · rw [if_neg h0, if_pos h1, if_neg h0]
    · rw [if_neg h0, if_neg h1, if_neg h0]

/-- The system code, extracted once so consumers share a single combinator. Specified,
not constructed. -/
noncomputable def treeSystemCode : OracleCode := Classical.choose exists_treeSystemCode

/-- **Specification of `treeSystemCode`**: on any name it produces the compiled system. -/
theorem mem_evalStream_treeSystemCode (p : Baire) :
    treeSystemName p ∈ treeSystemCode.evalStream p :=
  Classical.choose_spec exists_treeSystemCode p

/-! ### The path code -/

/-- The path name read off a section answer: entry `n` of the decoded level-`(n + 1)`
node. -/
def sectionPathName (a : Baire) : Baire := fun n =>
  if (treeWordDecode (a (n + 1))).getD n false then 1 else 0

/-- The path itself, as a point of Cantor space. -/
def sectionPath (a : Baire) : Cantor := fun n => (treeWordDecode (a (n + 1))).getD n false

theorem cantorRep_names_sectionPathName (a : Baire) :
    cantorRep.Names (sectionPathName a) (sectionPath a) := by
  rw [cantorRep_names_iff]
  constructor
  · intro n
    rw [sectionPathName]
    split <;> omega
  · funext n
    rw [sectionPath, sectionPathName]
    cases h : (treeWordDecode (a (n + 1))).getD n false <;> simp

/-- A single code produces the path name from the answer alone. -/
theorem exists_sectionPathCode : ∃ H : OracleCode, ∀ a : Baire,
    sectionPathName a ∈ H.evalStream a := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hbound : Primrec₂ fun (n : ℕ) (_ : ℕ) => n + 2 :=
    (Primrec.succ.comp (Primrec.succ.comp Primrec.fst)).to₂
  have hbit : Primrec fun v : ℕ =>
      (treeWordDecode ((ofNat (List ℕ) v.unpair.2).getD (v.unpair.1 + 1) 0)).getD
        v.unpair.1 false :=
    (Primrec.list_getD false).comp
      (primrec_treeWordDecode.comp ((Primrec.list_getD 0).comp
        ((Primrec.ofNat (List ℕ)).comp hu2) (Primrec.succ.comp hu1)))
      hu1
  have hg : Primrec fun v : ℕ =>
      if (treeWordDecode ((ofNat (List ℕ) v.unpair.2).getD (v.unpair.1 + 1) 0)).getD
          v.unpair.1 false then 1 else 0 :=
    Primrec.ite (Primrec.eq.comp hbit (Primrec.const true)) (Primrec.const 1)
      (Primrec.const 0)
  obtain ⟨H, hH⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨H, fun a => OracleCode.mem_evalStream.mpr fun n => ?_⟩
  rw [hH a n, Part.mem_some_iff, sectionPathName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [streamTake_getD a (by omega : n + 1 < n + 2)]

/-- The path code, extracted once so consumers share a single combinator. Specified, not
constructed. -/
noncomputable def sectionPathCode : OracleCode := Classical.choose exists_sectionPathCode

/-- **Specification of `sectionPathCode`**: on any answer stream it produces the path
name. -/
theorem mem_evalStream_sectionPathCode (a : Baire) :
    sectionPathName a ∈ sectionPathCode.evalStream a :=
  Classical.choose_spec exists_sectionPathCode a

/-! ### Sections decode to paths -/

/-- A list of length `n + 1` splits as its length-`n` prefix and its last entry. -/
private theorem eq_take_append_getD {l : List Bool} {n : ℕ} (h : l.length = n + 1) :
    l = l.take n ++ [l.getD n false] := by
  have hn : n < l.length := by omega
  calc l = l.take (n + 1) := (List.take_of_length_le (by omega)).symm
    _ = l.take n ++ [l[n]] := by rw [List.take_add_one, List.getElem?_eq_getElem hn]; rfl
    _ = l.take n ++ [l.getD n false] := by rw [List.getD_eq_getElem _ _ hn]

/-- The decoded section value at level `k` is a genuine level-`k` node. -/
private theorem section_node {p a : Baire} (hmem : ∀ k, a k ∈ treeLevel p k) (k : ℕ) :
    (treeWordDecode (a k)).length = k ∧ TreeMem p (treeWordDecode (a k)) := by
  obtain ⟨w, hlen, hw, hcode⟩ := mem_treeLevel.mp (hmem k)
  rw [hcode, treeWordDecode_treeWordCode]
  exact ⟨hlen, hw⟩

/-- **Sections decode to paths**: the truncation coherence makes the decoded section
values a nested family, so the path bits reconstruct every level. -/
theorem streamTake_sectionPath {p a : Baire}
    (hsec : IsEfilcSection (treeSystemName p) a) (n : ℕ) :
    streamTake (sectionPath a) n = treeWordDecode (a n) := by
  obtain ⟨hmem, hcoh⟩ := hsec
  have hmem' : ∀ k, a k ∈ treeLevel p k := fun k => by
    have := hmem k
    rwa [efilcFiber_treeSystemName] at this
  induction n with
  | zero =>
    have h0 := (section_node hmem' 0).1
    rw [List.length_eq_zero_iff.mp h0]
    rfl
  | succ n ih =>
    have hbond := hcoh n
    rw [efilcBond_treeSystemName, treeBondValue] at hbond
    have htake : (treeWordDecode (a (n + 1))).take n = treeWordDecode (a n) := by
      rw [← hbond, treeWordDecode_treeWordCode]
    rw [streamTake_succ, ih]
    conv_rhs => rw [eq_take_append_getD (section_node hmem' (n + 1)).1]
    rw [htake]
    rfl

/-! ### The reduction -/

/-- **`WKL ≤sW EFILC`, as an explicit pair**: `treeSystemCode` compiles the levels and
`sectionPathCode` decodes any accepted section into a path, from the answer alone. -/
theorem isStrongReductionPair_wkl_le_efilc :
    IsStrongReductionPair WKL EFILC treeSystemCode sectionPathCode := by
  intro p x hpx hdom
  obtain rfl : x = p := baireRep_names_iff.mp hpx
  obtain ⟨hpc, hinf⟩ := WKL.dom_iff.mp hdom
  refine ⟨treeSystemName x, mem_evalStream_treeSystemCode x, treeSystemName x,
    baireRep_names_iff.mpr rfl, efilc_dom_treeSystemName hpc hinf, ?_⟩
  intro a y' hay' hacc
  obtain rfl : y' = a := baireRep_names_iff.mp hay'
  obtain ⟨-, -, hsec⟩ := EFILC.accepts_iff.mp hacc
  refine ⟨sectionPathName y', mem_evalStream_sectionPathCode y', sectionPath y',
    cantorRep_names_sectionPathName y', ?_⟩
  refine WKL.accepts_iff.mpr ⟨hpc, hinf, fun n => ?_⟩
  rw [streamTake_sectionPath hsec n]
  exact (section_node (fun k => by
    have hk := hsec.1 k
    rwa [efilcFiber_treeSystemName] at hk) n).2

/-- **Weak Kőnig's lemma reduces strongly to explicit finite inverse-limit
compactness.** -/
theorem wkl_le_efilc : WKL ≤sW EFILC :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_wkl_le_efilc⟩

end ComputableAnalysis
