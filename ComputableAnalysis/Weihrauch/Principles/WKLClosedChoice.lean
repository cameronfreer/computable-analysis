/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecContainers
import ComputableAnalysis.Weihrauch.StrongReduction
import ComputableAnalysis.Weihrauch.Principles.ClosedChoiceCantor

/-!
# `WKL ≡sW C_Cantor`: trees and negative information present the same problem

`wkl_equiv_c_cantor : WKL ≡sW C_Cantor`, from the two explicit reduction pairs
`isStrongReductionPair_wkl_le_c_cantor` and `isStrongReductionPair_c_cantor_le_wkl`.
Both postprocessors are `OracleCode.query`: the two problems answer in the same
represented space, and each construction makes the answer already correct, so nothing is
decoded on either side.

**A tree as negative information** (`treeForbiddenName`). Coordinate `i` forbids the
cylinder of the canonical word `treeWordDecode i` exactly when that word is **absent**
from the tree, and is the no-op sentinel otherwise. The points of the presented closed
set are then literally the paths of the tree
(`closedCantorSet_treeForbiddenName`).

**A closed set as a length-staged tree** (`closedCantorTreeName`). Level `|w|` consults
exactly the first `|w|` entries of the enumeration, which a bounded prefix decides. The
paths of that tree are exactly the points of the closed set
(`paths_closedCantorTreeName`).

**The canonical lookup is load-bearing in both directions.** Only the encoding direction
of the word coding is available: `treeWordDecode` is a partial inverse that
canonicalizes, so an arbitrary index need not be any word's code, and re-encoding a
decoded index need not return it. The forward preprocessor therefore tests the tree at
`p (treeWordCode (treeWordDecode i))`, never at `p i` — reading `p i` would test the
tree at an index unrelated to the word whose cylinder coordinate `i` forbids — and the
converse generates its tree name through `treeWordDecode j`, so that a canonical query
recovers its word.

Neither correspondence uses a promise: both are identities of sets holding for every
stream. Prefix closure and infinity enter only to place a compiled name in the target's
domain.

The equivalence is at `≡sW` and is exactly what is proved: two certified strong
reductions. No claim is made about the degree beyond that.
-/

namespace ComputableAnalysis

open Encodable Denumerable

/-! ### The compiled negative name -/

/-- The negative name compiled from a tree: coordinate `i` forbids the cylinder of the
canonical word `treeWordDecode i` when that word is absent, and forbids nothing
otherwise. The tree is read at the **canonical** index `treeWordCode (treeWordDecode i)`,
never at `i`. -/
def treeForbiddenName (p : Baire) : Baire := fun i =>
  if p (treeWordCode (treeWordDecode i)) = 0 then
    cantorForbiddenWordCode (treeWordDecode i)
  else 0

/-- **The extensional correspondence**: coordinate `i` forbids exactly the canonical word
`treeWordDecode i`, and does so exactly when that word is not a node. -/
theorem cantorForbiddenWord_treeForbiddenName (p : Baire) (i : ℕ) :
    cantorForbiddenWord (treeForbiddenName p) i =
      if TreeMem p (treeWordDecode i) then none else some (treeWordDecode i) := by
  by_cases h : TreeMem p (treeWordDecode i)
  · rw [ite_eq_left h, cantorForbiddenWord_eq_none_iff, treeForbiddenName, ite_eq_right h]
  · rw [ite_eq_right h]
    refine cantorForbiddenWord_of_eq_code ?_
    rw [treeForbiddenName, ite_eq_left (not_not.mp h)]

/-- **The presented closed set is the set of paths.** An identity of sets on every
stream: no promise about the tree is used. -/
theorem closedCantorSet_treeForbiddenName (p : Baire) :
    closedCantorSet (treeForbiddenName p) = {x : Cantor | ∀ n, TreeMem p (streamTake x n)} := by
  ext x
  simp only [closedCantorSet, Set.mem_ofPred_eq]
  constructor
  · intro hx n
    by_contra hmem
    have hcode : cantorForbiddenWord (treeForbiddenName p) (treeWordCode (streamTake x n))
        = some (streamTake x n) := by
      rw [cantorForbiddenWord_treeForbiddenName, treeWordDecode_treeWordCode, ite_eq_right hmem]
    exact hx _ _ hcode (mem_cylinder_streamTake x n)
  · intro hx i w hw hcyl
    rw [cantorForbiddenWord_treeForbiddenName] at hw
    by_cases hmem : TreeMem p (treeWordDecode i)
    · rw [ite_eq_left hmem] at hw
      simp at hw
    · rw [ite_eq_right hmem] at hw
      have hwe : treeWordDecode i = w := Option.some_injective _ hw
      have hp : TreeMem p w := by
        have h2 := hx w.length
        rwa [mem_cylinder_iff.mp hcyl] at h2
      rw [hwe] at hmem
      exact hmem hp

/-- The compiled name presents a nonempty closed set exactly when the tree has a path;
on `WKL`'s domain, weak Kőnig's lemma supplies one. -/
theorem c_Cantor_dom_treeForbiddenName {p : Baire} (hpc : IsPrefixClosed p)
    (hinf : IsInfiniteTree p) : C_Cantor.Dom (treeForbiddenName p) := by
  rw [C_Cantor.dom_iff, closedCantorSet_treeForbiddenName]
  exact exists_path_of_isInfiniteTree hpc hinf

/-! ### The preprocessor code

Coordinate `i` queries the tree at the single position `treeWordCode (treeWordDecode i)`,
which is computed from `i` alone, so a prefix one longer than that position decides the
coordinate and `OracleCode.exists_prefixPostCode` applies with no adaptive machinery. -/

/-- A single code compiles the negative name. -/
theorem exists_treeForbiddenCode : ∃ K : OracleCode, ∀ p : Baire,
    treeForbiddenName p ∈ K.evalStream p := by
  have hpos : Primrec fun i : ℕ => treeWordCode (treeWordDecode i) :=
    primrec_treeWordCode.comp primrec_treeWordDecode
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hbound : Primrec₂ fun (i : ℕ) (_ : ℕ) => treeWordCode (treeWordDecode i) + 1 :=
    (Primrec.succ.comp (hpos.comp Primrec.fst)).to₂
  have hlook : Primrec fun v : ℕ =>
      (ofNat (List ℕ) v.unpair.2).getD (treeWordCode (treeWordDecode v.unpair.1)) 0 :=
    (Primrec.list_getD 0).comp ((Primrec.ofNat (List ℕ)).comp hu2) (hpos.comp hu1)
  have hg : Primrec fun v : ℕ =>
      if (ofNat (List ℕ) v.unpair.2).getD (treeWordCode (treeWordDecode v.unpair.1)) 0 = 0 then
        cantorForbiddenWordCode (treeWordDecode v.unpair.1)
      else 0 :=
    Primrec.ite (Primrec.eq.comp hlook (Primrec.const 0))
      (Primrec.succ.comp (hpos.comp hu1)) (Primrec.const 0)
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨K, fun p => OracleCode.mem_evalStream.mpr fun i => ?_⟩
  rw [hK p i, Part.mem_some_iff, treeForbiddenName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [streamTake_getD p (Nat.lt_succ_self _)]

/-- The preprocessor code, extracted once so consumers share a single combinator.
Specified, not constructed. -/
noncomputable def treeForbiddenCode : OracleCode := Classical.choose exists_treeForbiddenCode

/-- **Specification of `treeForbiddenCode`**: on any tree name it produces the compiled
negative name. -/
theorem mem_evalStream_treeForbiddenCode (p : Baire) :
    treeForbiddenName p ∈ treeForbiddenCode.evalStream p :=
  Classical.choose_spec exists_treeForbiddenCode p

/-! ### The reduction -/

/-- **`WKL ≤sW C_Cantor`, as an explicit pair**: `treeForbiddenCode` compiles the tree
into negative information, and the postprocessor is the identity on the answer — every
point of the presented closed set already *is* a path. -/
theorem isStrongReductionPair_wkl_le_c_cantor :
    IsStrongReductionPair WKL C_Cantor treeForbiddenCode OracleCode.query := by
  intro p x hpx hdom
  obtain rfl : x = p := baireRep_names_iff.mp hpx
  obtain ⟨hpc, hinf⟩ := WKL.dom_iff.mp hdom
  refine ⟨treeForbiddenName x, mem_evalStream_treeForbiddenCode x, treeForbiddenName x,
    baireRep_names_iff.mpr rfl, c_Cantor_dom_treeForbiddenName hpc hinf, ?_⟩
  intro a y' hay' hacc
  -- the answer passes through unchanged: `query` is the identity stream operator, and
  -- the two problems answer in the same represented space
  have hq : a ∈ OracleCode.query.evalStream a := by
    rw [OracleCode.evalStream_query]
    exact Part.mem_some _
  refine ⟨a, hq, y', hay', WKL.accepts_iff.mpr ⟨hpc, hinf, ?_⟩⟩
  have hmem : y' ∈ closedCantorSet (treeForbiddenName x) := hacc
  rw [closedCantorSet_treeForbiddenName x] at hmem
  exact hmem

/-- **Weak Kőnig's lemma reduces strongly to closed choice on Cantor space.** A strong
reduction in this one direction and nothing else: no lower bound and no equivalence is
suggested. -/
theorem wkl_le_c_cantor : WKL ≤sW C_Cantor :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_wkl_le_c_cantor⟩

/-! ## The converse: a closed set as a length-staged tree

The naive tree — take `w` as a node when no forbidden cylinder contains it — is not
decidable from a finite prefix: it quantifies over the whole enumeration, so it is only
co-r.e. Staging by length repairs this. At level `|w|` the tree consults exactly the
first `|w|` entries, which a bounded prefix decides. A *fixed* word is tested only at its
own length, so it may well pass and be killed later by an entry forbidding all of its
extensions; what the staging preserves is the infinite picture — an infinite branch
survives all levels exactly when no enumerated cylinder contains it. The staged tree is
thus computable where the naive one is not, and has the same paths.
-/

/-- **Stage-`|w|` membership**: no cylinder forbidden by one of the first `|w|` entries of
the presentation has `w` inside it. -/
def StagedTreeMem (q : Baire) (w : List Bool) : Prop :=
  ∀ i < w.length, ∀ u, cantorForbiddenWord q i = some u → ¬ u <+: w

/-- The stage test as a Boolean, reading the presentation only at the first `|w|`
positions. -/
def closedCantorTreeMemB (q : Baire) (w : List Bool) : Bool :=
  (List.range w.length).all fun i =>
    decide (q i = 0) || !decide (treeWordDecode (q i - 1) <+: w)

theorem closedCantorTreeMemB_iff {q : Baire} {w : List Bool} :
    closedCantorTreeMemB q w = true ↔ StagedTreeMem q w := by
  rw [closedCantorTreeMemB, List.all_eq_true]
  constructor
  · intro h i hi u hu hup
    obtain ⟨hne, rfl⟩ := cantorForbiddenWord_eq_some_iff.mp hu
    have hb := h i (List.mem_range.mpr hi)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hb
    exact hb.elim hne fun hnp => hnp hup
  · intro h i hi
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
    by_cases h0 : q i = 0
    · exact Or.inl h0
    · exact Or.inr (h i (List.mem_range.mp hi) _
        (cantorForbiddenWord_eq_some_iff.mpr ⟨h0, rfl⟩))

/-- The stage test reads only the first `|w|` entries, so presentations agreeing there
decide the same words. -/
theorem stagedTreeMem_congr {q₁ q₂ : Baire} {w : List Bool}
    (h : ∀ i < w.length, q₁ i = q₂ i) : StagedTreeMem q₁ w ↔ StagedTreeMem q₂ w := by
  constructor
  · exact fun hm i hi u hu => hm i hi u ((cantorForbiddenWord_congr (h i hi)).trans hu)
  · exact fun hm i hi u hu => hm i hi u ((cantorForbiddenWord_congr (h i hi)).symm.trans hu)

theorem closedCantorTreeMemB_congr {q₁ q₂ : Baire} {w : List Bool}
    (h : ∀ i < w.length, q₁ i = q₂ i) :
    closedCantorTreeMemB q₁ w = closedCantorTreeMemB q₂ w := by
  rw [Bool.eq_iff_iff, closedCantorTreeMemB_iff, closedCantorTreeMemB_iff]
  exact stagedTreeMem_congr h

/-- The staged tree, as a `WKL` name. Coordinate `j` decides the **canonical** word
`treeWordDecode j`; at a canonical query `treeWordCode w` the decoder returns `w`. -/
def closedCantorTreeName (q : Baire) : Baire := fun j =>
  if closedCantorTreeMemB q (treeWordDecode j) then 1 else 0

/-- **The canonical readback**: the presented tree's nodes are exactly the words passing
their own stage test. -/
theorem treeMem_closedCantorTreeName {q : Baire} {w : List Bool} :
    TreeMem (closedCantorTreeName q) w ↔ StagedTreeMem q w := by
  rw [TreeMem, closedCantorTreeName, treeWordDecode_treeWordCode]
  by_cases h : closedCantorTreeMemB q w = true
  · rw [ite_eq_left h]
    exact ⟨fun _ => closedCantorTreeMemB_iff.mp h, fun _ => one_ne_zero⟩
  · rw [ite_eq_right h]
    exact ⟨fun hc => absurd rfl hc, fun hs => absurd (closedCantorTreeMemB_iff.mpr hs) h⟩

/-! ### The staged tree keeps `WKL`'s promises -/

/-- **Prefix closure.** A prefix examines fewer enumeration entries, and a forbidden
prefix of the shorter word would be a forbidden prefix of the longer one too. -/
theorem isPrefixClosed_closedCantorTreeName (q : Baire) :
    IsPrefixClosed (closedCantorTreeName q) := by
  intro w v hw hpre
  rw [treeMem_closedCantorTreeName] at hw ⊢
  intro i hi u hu hup
  exact hw i (lt_of_lt_of_le hi hpre.length_le) u hu (hup.trans hpre)

/-- Every prefix of a point of the closed set passes its own stage test. -/
theorem stagedTreeMem_streamTake {q : Baire} {x : Cantor} (hx : x ∈ closedCantorSet q)
    (n : ℕ) : StagedTreeMem q (streamTake x n) := by
  intro i hi u hu hup
  rw [length_streamTake] at hi
  have hul : u.length ≤ n := by
    have := hup.length_le
    rwa [length_streamTake] at this
  have hu' : streamTake x u.length = u := by
    have h1 : u = (streamTake x n).take u.length := List.prefix_iff_eq_take.mp hup
    rw [take_streamTake x hul] at h1
    exact h1.symm
  exact hx i u hu (mem_cylinder_iff.mpr hu')

/-- **Infinitude from nonemptiness.** A point of the closed set supplies a node at every
level, namely its own prefix. -/
theorem isInfiniteTree_closedCantorTreeName {q : Baire}
    (hne : (closedCantorSet q).Nonempty) : IsInfiniteTree (closedCantorTreeName q) := by
  obtain ⟨x, hx⟩ := hne
  exact fun n => ⟨streamTake x n, length_streamTake x n,
    treeMem_closedCantorTreeName.mpr (stagedTreeMem_streamTake hx n)⟩

/-- **The exact path identity**, with no promise used: the paths of the staged tree are
exactly the points of the presented closed set. The nontrivial direction takes a level
past both the offending entry and the forbidden word's length. -/
theorem paths_closedCantorTreeName (q : Baire) :
    {x : Cantor | ∀ n, TreeMem (closedCantorTreeName q) (streamTake x n)} =
      closedCantorSet q := by
  ext x
  simp only [Set.mem_ofPred_eq, closedCantorSet]
  constructor
  · intro hpath i u hu hcyl
    have hi : i < max (i + 1) u.length := lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
    have hul : u.length ≤ max (i + 1) u.length := le_max_right _ _
    have hup : u <+: streamTake x (max (i + 1) u.length) := by
      have h1 : streamTake x u.length = u := mem_cylinder_iff.mp hcyl
      have h2 : streamTake x u.length <+: streamTake x (max (i + 1) u.length) :=
        streamTake_prefix x hul
      rwa [h1] at h2
    exact treeMem_closedCantorTreeName.mp (hpath _) i
      (by rw [length_streamTake]; exact hi) u hu hup
  · exact fun hx n => treeMem_closedCantorTreeName.mpr (stagedTreeMem_streamTake hx n)

/-- A nonempty presented closed set puts the staged tree in `WKL`'s domain. -/
theorem wkl_dom_closedCantorTreeName {q : Baire} (hdom : C_Cantor.Dom q) :
    WKL.Dom (closedCantorTreeName q) :=
  WKL.dom_iff.mpr ⟨isPrefixClosed_closedCantorTreeName q,
    isInfiniteTree_closedCantorTreeName (C_Cantor.dom_iff.mp hdom)⟩

/-! ### The preprocessor code

Output coordinate `j` decodes `w := treeWordDecode j` and reads exactly the first
`|w|` entries, so the prefix bound is `(treeWordDecode j).length` — not `j`, and not
`treeWordCode w`. -/

/-- A single code compiles the staged tree. -/
theorem exists_closedCantorTreeCode : ∃ K : OracleCode, ∀ q : Baire,
    closedCantorTreeName q ∈ K.evalStream q := by
  have hu1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hu2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hbound : Primrec₂ fun (j : ℕ) (_ : ℕ) => (treeWordDecode j).length :=
    (Primrec.list_length.comp (primrec_treeWordDecode.comp Primrec.fst)).to₂
  have hval : Primrec fun y : (List ℕ × List Bool) × ℕ => y.1.1.getD y.2 0 :=
    (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  have hzero : Primrec fun y : (List ℕ × List Bool) × ℕ => decide (y.1.1.getD y.2 0 = 0) :=
    (PrimrecRel.comp Primrec.eq hval (Primrec.const 0)).decide
  have hpre : Primrec fun y : (List ℕ × List Bool) × ℕ =>
      decide (treeWordDecode (y.1.1.getD y.2 0 - 1) <+: y.1.2) :=
    (PrimrecRel.comp primrec_isPrefix
      (primrec_treeWordDecode.comp (Primrec.nat_sub.comp hval (Primrec.const 1)))
      (Primrec.snd.comp Primrec.fst)).decide
  have htest : Primrec₂ fun (L : List ℕ) (w : List Bool) =>
      closedCantorTreeMemB (Baire.ofList L) w :=
    primrec_list_all (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
      ((Primrec.or.comp hzero (Primrec.not.comp hpre)).to₂)
  have hb : Primrec fun v : ℕ =>
      closedCantorTreeMemB (Baire.ofList (ofNat (List ℕ) v.unpair.2))
        (treeWordDecode v.unpair.1) :=
    htest.comp ((Primrec.ofNat (List ℕ)).comp hu2) (primrec_treeWordDecode.comp hu1)
  have hg : Primrec fun v : ℕ =>
      if closedCantorTreeMemB (Baire.ofList (ofNat (List ℕ) v.unpair.2))
        (treeWordDecode v.unpair.1) then 1 else 0 := by
    refine Primrec.of_eq (Primrec.cond hb (Primrec.const 1) (Primrec.const 0)) fun v => ?_
    cases closedCantorTreeMemB (Baire.ofList (ofNat (List ℕ) v.unpair.2))
      (treeWordDecode v.unpair.1) <;> rfl
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hbound hg
  refine ⟨K, fun q => OracleCode.mem_evalStream.mpr fun j => ?_⟩
  rw [hK q j, Part.mem_some_iff, closedCantorTreeName]
  simp only [Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [closedCantorTreeMemB_congr fun i hi => Baire.ofList_streamTake q hi]

/-- The preprocessor code, extracted once so consumers share a single combinator.
Specified, not constructed. -/
noncomputable def closedCantorTreeCode : OracleCode :=
  Classical.choose exists_closedCantorTreeCode

/-- **Specification of `closedCantorTreeCode`**: on any negative name it produces the
staged tree. -/
theorem mem_evalStream_closedCantorTreeCode (q : Baire) :
    closedCantorTreeName q ∈ closedCantorTreeCode.evalStream q :=
  Classical.choose_spec exists_closedCantorTreeCode q

/-! ### The converse reduction, and the bridge -/

/-- **`C_Cantor ≤sW WKL`, as an explicit pair**: `closedCantorTreeCode` stages the closed
set into a tree, and the postprocessor is again the identity on the answer — every path
of the staged tree already lies in the closed set. -/
theorem isStrongReductionPair_c_cantor_le_wkl :
    IsStrongReductionPair C_Cantor WKL closedCantorTreeCode OracleCode.query := by
  intro q x hqx hdom
  obtain rfl : x = q := baireRep_names_iff.mp hqx
  refine ⟨closedCantorTreeName x, mem_evalStream_closedCantorTreeCode x,
    closedCantorTreeName x, baireRep_names_iff.mpr rfl,
    wkl_dom_closedCantorTreeName hdom, ?_⟩
  intro a y' hay' hacc
  have hq : a ∈ OracleCode.query.evalStream a := by
    rw [OracleCode.evalStream_query]
    exact Part.mem_some _
  obtain ⟨-, -, hpath⟩ := WKL.accepts_iff.mp hacc
  refine ⟨a, hq, y', hay', ?_⟩
  have hmem : y' ∈ {z : Cantor | ∀ n, TreeMem (closedCantorTreeName x) (streamTake z n)} :=
    hpath
  rw [paths_closedCantorTreeName x] at hmem
  exact hmem

/-- **Closed choice on Cantor space reduces strongly to weak Kőnig's lemma**, through the
length-staged tree. -/
theorem c_cantor_le_wkl : C_Cantor ≤sW WKL :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_c_cantor_le_wkl⟩

/-- **`WKL ≡sW C_Cantor`**: the tree and negative-information presentations are strongly
Weihrauch equivalent. Both directions are certified by explicit pairs whose
postprocessor is `OracleCode.query`, so neither reduction inspects its input twice. -/
theorem wkl_equiv_c_cantor : WKL ≡sW C_Cantor := ⟨wkl_le_c_cantor, c_cantor_le_wkl⟩

end ComputableAnalysis
