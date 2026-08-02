/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.StrongReduction
import ComputableAnalysis.Weihrauch.Principles.ClosedChoiceCantor

/-!
# `WKL ≤sW C_Cantor`: a tree as negative information

`wkl_le_c_cantor : WKL ≤sW C_Cantor`, with the explicit reduction pair
`isStrongReductionPair_wkl_le_c_cantor` over the named codes `treeForbiddenCode` and
`OracleCode.query`.

The preprocessor turns a presented tree into a negative name: coordinate `i` forbids the
cylinder of the canonical word `treeWordDecode i` exactly when that word is **absent**
from the tree, and is the no-op sentinel otherwise. The paths of the tree are then
literally the points of the presented closed set (`closedCantorSet_treeForbiddenName`),
so the postprocessor is the identity on the answer stream — `OracleCode.query` — and
strongness is immediate.

**The canonical lookup is load-bearing.** Coordinate `i` tests the tree at
`p (treeWordCode (treeWordDecode i))`, never at `p i`. Only the encoding direction of
the word coding is available: `treeWordDecode` is a partial inverse that canonicalizes,
so an arbitrary `i` need not be any word's code, and re-encoding a decoded index need
not return it. Reading `p i` would test the tree at an index unrelated to the word whose
cylinder coordinate `i` forbids.

Nothing here depends on the tree's promises: the correspondence between forbidden
cylinders and absent words is an identity of sets, proved for every stream. Prefix
closure and infinity enter only to place the compiled name in `C_Cantor`'s domain, where
they supply a path.

This certifies a strong reduction in this one direction and nothing else: no lower bound
and no equivalence is claimed. The converse, and hence `WKL ≡sW C_Cantor`, needs a
different construction and is not addressed here.
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
  · rw [if_pos h, cantorForbiddenWord_eq_none_iff, treeForbiddenName, if_neg h]
  · rw [if_neg h]
    refine cantorForbiddenWord_of_eq_code ?_
    rw [treeForbiddenName, if_pos (not_not.mp h)]

/-- **The presented closed set is the set of paths.** An identity of sets on every
stream: no promise about the tree is used. -/
theorem closedCantorSet_treeForbiddenName (p : Baire) :
    closedCantorSet (treeForbiddenName p) = {x : Cantor | ∀ n, TreeMem p (streamTake x n)} := by
  ext x
  simp only [closedCantorSet, Set.mem_setOf_eq]
  constructor
  · intro hx n
    by_contra hmem
    have hcode : cantorForbiddenWord (treeForbiddenName p) (treeWordCode (streamTake x n))
        = some (streamTake x n) := by
      rw [cantorForbiddenWord_treeForbiddenName, treeWordDecode_treeWordCode, if_neg hmem]
    exact hx _ _ hcode (mem_cylinder_streamTake x n)
  · intro hx i w hw hcyl
    rw [cantorForbiddenWord_treeForbiddenName] at hw
    by_cases hmem : TreeMem p (treeWordDecode i)
    · rw [if_pos hmem] at hw
      simp at hw
    · rw [if_neg hmem] at hw
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
  rw [closedCantorSet_treeForbiddenName] at hmem
  exact hmem

/-- **Weak Kőnig's lemma reduces strongly to closed choice on Cantor space.** A strong
reduction in this one direction and nothing else: no lower bound and no equivalence is
suggested. -/
theorem wkl_le_c_cantor : WKL ≤sW C_Cantor :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_wkl_le_c_cantor⟩

end ComputableAnalysis
