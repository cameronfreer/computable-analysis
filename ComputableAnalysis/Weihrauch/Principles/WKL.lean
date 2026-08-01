/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.KonigLemma
import ComputableAnalysis.Weihrauch.Problem

/-!
# Weak Kőnig's lemma as a Weihrauch problem

`WKL` receives a name of an infinite binary tree and must produce an infinite path.

**The tree presentation is decidable and positive.** A name `p : Baire` presents the set
of words whose code it marks nonzero: `TreeMem p w ↔ p (treeWordCode w) ≠ 0`, over the
pinned word coding `treeWordCode = encode ∘ boolWordToNat` of unit 1 — not
`Encodable (List Bool)`, so that the coding is fixed and its primitive recursiveness is
the already-landed `primrec_boolWordToNat`. Every stream is a valid name of *some* set of
words; being a tree is not a condition on names but a promise inside the problem, exactly
as `LLPO`'s at-most-one-nonzero constraint is.

**The promises live in `accepts`** (`IsPrefixClosed`, `IsInfiniteTree`), and answers are
points of `cantorSpace`, with the path condition `∀ n, TreeMem p (streamTake π n)`.

Because membership reads the name at exactly the code being asked about, a prefix reaching
past that code already decides it: `treeMemB` is that decision on a finite table, and
`treeMemB_streamTake_iff` its agreement with `TreeMem`. Every reduction out of `WKL`
consumes this presentation API rather than reproving it.

The semantic anchor is `WKL.dom_iff`: the domain is exactly the infinite trees, whose
nontrivial direction *is* weak Kőnig's lemma. It is proved through mathlib's
`exists_seq_forall_proj_of_forall_finite`, taking the level-`n` nodes as a finite inverse
system under prefix restriction — each level is finite (a node of length `n` is determined
by its `n` entries), so the fibre condition is automatic and no compactness argument on
Cantor space is needed.

The negative-information presentation of closed sets is deliberately *not* this object;
`WKL ≡sW C_Cantor` is a separate bridge, keeping the tree and closed-set presentations
independently meaningful (as `C₂ ≡sW LLPO` does for finite binary choice).
-/

namespace ComputableAnalysis

open Encodable Denumerable

/-! ### The pinned word coding -/

/-- The code of a binary word: the pinned unit-1 coding `boolWordToNat`, encoded. -/
def treeWordCode (w : List Bool) : ℕ := encode (boolWordToNat w)

/-- The partial inverse of `treeWordCode`. -/
def treeWordDecode (n : ℕ) : List Bool := natWordToBool (ofNat (List ℕ) n)

@[simp]
theorem treeWordDecode_treeWordCode (w : List Bool) : treeWordDecode (treeWordCode w) = w := by
  rw [treeWordDecode, treeWordCode, Denumerable.ofNat_encode, natWordToBool_boolWordToNat]

theorem primrec_treeWordCode : Primrec treeWordCode :=
  Primrec.encode.comp primrec_boolWordToNat

theorem primrec_treeWordDecode : Primrec treeWordDecode :=
  primrec_natWordToBool.comp (Primrec.ofNat (List ℕ))

/-! ### Trees presented by a stream -/

/-- `w` is a node of the tree presented by `p`: its code is marked nonzero. -/
def TreeMem (p : Baire) (w : List Bool) : Prop := p (treeWordCode w) ≠ 0

/-- The presentation is decidable: membership is a single comparison against `0`. -/
instance (p : Baire) (w : List Bool) : Decidable (TreeMem p w) :=
  inferInstanceAs (Decidable (p (treeWordCode w) ≠ 0))

/-- The presented set of words is closed under prefixes. -/
def IsPrefixClosed (p : Baire) : Prop :=
  ∀ w v : List Bool, TreeMem p w → v <+: w → TreeMem p v

/-- The presented set of words has a node at every level. -/
def IsInfiniteTree (p : Baire) : Prop := ∀ n, ∃ w : List Bool, w.length = n ∧ TreeMem p w

/-! ### Deciding membership from a prefix

Because `TreeMem` reads the name at the very code being asked about, a prefix reaching
past that code already decides membership. This is the presentation's finite-observation
layer, shared by every reduction out of `WKL`. -/

/-- Membership decided from a finite table of the name, with `0` (absent) as default. -/
def treeMemB (L : List ℕ) (w : List Bool) : Bool := decide (L.getD (treeWordCode w) 0 ≠ 0)

/-- A prefix reaching past a word's code decides that word's membership. -/
theorem treeMemB_streamTake {p : Baire} {N : ℕ} {w : List Bool} (h : treeWordCode w < N) :
    treeMemB (streamTake p N) w = decide (TreeMem p w) := by
  rw [treeMemB, streamTake_getD p h]
  rfl

theorem treeMemB_streamTake_iff {p : Baire} {N : ℕ} {w : List Bool}
    (h : treeWordCode w < N) : treeMemB (streamTake p N) w = true ↔ TreeMem p w := by
  rw [treeMemB_streamTake h, decide_eq_true_eq]

theorem primrec_treeMemB {α : Type*} [Primcodable α] {L : α → List ℕ} {w : α → List Bool}
    (hL : Primrec L) (hw : Primrec w) : Primrec fun a => treeMemB (L a) (w a) :=
  (PrimrecRel.comp (PrimrecRel.not Primrec.eq)
    ((Primrec.list_getD 0).comp hL (primrec_treeWordCode.comp hw)) (Primrec.const 0)).decide

/-- **Weak Kőnig's lemma** as a problem: on a prefix-closed set of binary words with a node
at every level, produce an infinite path. -/
def WKL : Problem baireSpace cantorSpace :=
  ⟨fun p π => IsPrefixClosed p ∧ IsInfiniteTree p ∧ ∀ n, TreeMem p (streamTake π n)⟩

/-- **Definitional unfolding of `WKL.accepts`.** An explicit rewrite lemma, deliberately
not a global `simp` rule. -/
theorem WKL.accepts_iff {p : Baire} {π : Cantor} :
    WKL.accepts p π ↔
      IsPrefixClosed p ∧ IsInfiniteTree p ∧ ∀ n, TreeMem p (streamTake π n) :=
  Iff.rfl

/-! ### The domain is exactly the infinite trees

The nontrivial direction is weak Kőnig's lemma, obtained from mathlib's inverse-system
form (`exists_seq_forall_proj_of_forall_finite`) rather than from compactness of Cantor
space: the level-`n` nodes are the system, prefix restriction is the projection, and each
level is finite. -/

/-- Each level of a presented tree is finite: a node of length `n` is determined by its
`n` entries, so the level embeds in `Fin n → Bool`. -/
private theorem finite_level (p : Baire) (n : ℕ) :
    Finite {w : List Bool // w.length = n ∧ TreeMem p w} := by
  have hinj : Function.Injective
      (fun w : {w : List Bool // w.length = n ∧ TreeMem p w} =>
        fun i : Fin n => w.val.getD i false) := by
    intro a b h
    refine Subtype.ext (List.ext_getElem (by rw [a.2.1, b.2.1]) fun i h1 h2 => ?_)
    have hi : i < n := by rw [← a.2.1]; exact h1
    have := congrFun h ⟨i, hi⟩
    simpa [List.getD_eq_getElem, h1, h2] using this
  exact Finite.of_injective _ hinj

/-- **Weak Kőnig's lemma**: a prefix-closed set of binary words with a node at every level
has an infinite path. -/
theorem exists_path_of_isInfiniteTree {p : Baire} (hpc : IsPrefixClosed p)
    (hinf : IsInfiniteTree p) : ∃ π : Cantor, ∀ n, TreeMem p (streamTake π n) := by
  classical
  -- the level-`n` nodes, as an inverse system under prefix restriction
  let α : ℕ → Type := fun n => {w : List Bool // w.length = n ∧ TreeMem p w}
  have hlen : ∀ {i j : ℕ}, i ≤ j → ∀ w : α j, (w.val.take i).length = i := by
    intro i j hij w
    rw [List.length_take, w.2.1, Nat.min_eq_left hij]
  let proj : {i j : ℕ} → (hij : i ≤ j) → α j → α i := fun {i _} hij w =>
    ⟨w.val.take i, hlen hij w, hpc w.val _ w.2.2 (List.take_prefix i w.val)⟩
  haveI : ∀ n, Finite (α n) := finite_level p
  haveI : ∀ n, Nonempty (α n) := fun n => by
    obtain ⟨w, hw, hmem⟩ := hinf n
    exact ⟨⟨w, hw, hmem⟩⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite (α := α) proj
    (fun {i} a => Subtype.ext (List.take_of_length_le (by rw [a.2.1])))
    (fun {i j _} hij hjk a => Subtype.ext (by
      simp only [proj, List.take_take, Nat.min_eq_left hij]))
    (fun i a => Set.toFinite _)
  -- read the path off the coherent family
  refine ⟨fun n => (f (n + 1)).val.getD n false, fun n => ?_⟩
  have key : ∀ n, streamTake (fun k => (f (k + 1)).val.getD k false) n = (f n).val := by
    intro n
    induction n with
    | zero => exact (List.length_eq_zero_iff.mp (f 0).2.1).symm
    | succ n ih =>
        rw [streamTake_succ, ih]
        have hn : n < (f (n + 1)).val.length := by rw [(f (n + 1)).2.1]; omega
        have hcoh : (f (n + 1)).val.take n = (f n).val :=
          congrArg Subtype.val (hf (Nat.le_succ n))
        rw [← hcoh, List.getD_eq_getElem _ _ hn, List.take_concat_get',
          List.take_of_length_le (by rw [(f (n + 1)).2.1])]
  rw [key n]
  exact (f n).2.2

/-- **The semantic anchor**: `WKL`'s domain is exactly the infinite trees. -/
theorem WKL.dom_iff {p : Baire} : WKL.Dom p ↔ IsPrefixClosed p ∧ IsInfiniteTree p := by
  constructor
  · rintro ⟨π, hpc, hinf, -⟩
    exact ⟨hpc, hinf⟩
  · rintro ⟨hpc, hinf⟩
    obtain ⟨π, hπ⟩ := exists_path_of_isInfiniteTree hpc hinf
    exact ⟨π, hpc, hinf, hπ⟩

end ComputableAnalysis
