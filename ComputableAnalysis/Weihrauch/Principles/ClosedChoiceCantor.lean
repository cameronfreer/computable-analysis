/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Principles.WKL

/-!
# Closed choice on Cantor space, from negative information

A name **enumerates forbidden basic cylinders**: entry `i` is either the no-op sentinel `0`
or `n + 1`, forbidding the cylinder of `treeWordDecode n`. The sentinel is essential — with
no way to say "nothing forbidden here", the whole space would have no name.

The conventions are deliberately permissive: duplicates and redundant extensions are
allowed, and **every** Baire stream is a valid negative name. Nonemptiness is not a
condition on names; it lives in the derived problem's domain (`C_Cantor.dom_iff`).

`closedCantorSet p` is the set of points avoiding every enumerated cylinder — the
complement of the generated open set `cantorForbiddenOpen p`, hence closed. Two names
present the same set exactly when they generate the same open set
(`closedCantorSet_congr`), which is the right extensionality: it respects redundant
extensions, so a name enumerating `[false]` and one enumerating both `[false, false]` and
`[false, true]` are extensionally equal.

Only the encoding direction of the word coding is available, and only it is needed
(`cantorForbiddenWord_of_eq_code`): re-encoding an arbitrary nonzero entry need not
reproduce it, because `treeWordDecode` canonicalizes.

This is deliberately concrete: no general hyperspace representation. The closed set and
this problem are enough to make `C_Cantor` independently meaningful and to calibrate it
against `WKL`.
-/

namespace ComputableAnalysis

/-- Entry `i` of a negative name: `0` is the no-op sentinel; `n + 1` forbids the cylinder
of `treeWordDecode n`. -/
def cantorForbiddenWord (p : Baire) (i : ℕ) : Option (List Bool) :=
  match p i with
  | 0 => none
  | n + 1 => some (treeWordDecode n)

/-- The sentinel: an entry forbids nothing exactly when it is `0`. -/
@[simp]
theorem cantorForbiddenWord_eq_none_iff {p : Baire} {i : ℕ} :
    cantorForbiddenWord p i = none ↔ p i = 0 := by
  cases hp : p i <;> simp [cantorForbiddenWord, hp]

/-- The code that forbids a given word. -/
def forbiddenWordCode (w : List Bool) : ℕ := treeWordCode w + 1

/-- The encoding direction: an entry carrying `forbiddenWordCode w` forbids `w`. The
converse fails — the decoder canonicalizes — and is not needed. -/
theorem cantorForbiddenWord_of_eq_code {p : Baire} {i : ℕ} {w : List Bool}
    (h : p i = forbiddenWordCode w) : cantorForbiddenWord p i = some w := by
  rw [cantorForbiddenWord, h, forbiddenWordCode]
  change some (treeWordDecode (treeWordCode w)) = some w
  rw [treeWordDecode_treeWordCode]

/-- The open set a negative name generates: the union of the enumerated cylinders. -/
def cantorForbiddenOpen (p : Baire) : Set Cantor :=
  ⋃ i, ⋃ w ∈ {w | cantorForbiddenWord p i = some w}, cylinder w

theorem isOpen_cantorForbiddenOpen (p : Baire) : IsOpen (cantorForbiddenOpen p) :=
  isOpen_iUnion fun _ => isOpen_iUnion fun w => isOpen_iUnion fun _ =>
    (Cantor.isClopen_cylinder w).isOpen

/-- The closed set a negative name presents: the points avoiding every enumerated
cylinder. -/
def closedCantorSet (p : Baire) : Set Cantor :=
  {x | ∀ i w, cantorForbiddenWord p i = some w → x ∉ cylinder w}

/-- The presented set is exactly the complement of the generated open set. -/
theorem closedCantorSet_eq_compl (p : Baire) :
    closedCantorSet p = (cantorForbiddenOpen p)ᶜ := by
  ext x
  simp only [closedCantorSet, cantorForbiddenOpen, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.mem_iUnion, not_exists]

theorem isClosed_closedCantorSet (p : Baire) : IsClosed (closedCantorSet p) := by
  rw [closedCantorSet_eq_compl]
  exact (isOpen_cantorForbiddenOpen p).isClosed_compl

/-- **Extensionality**: names generating the same forbidden open set present the same
closed set. Stated on the generated open set rather than on the enumerated words, so that
redundant extensions are respected. -/
theorem closedCantorSet_congr {p q : Baire}
    (h : cantorForbiddenOpen p = cantorForbiddenOpen q) :
    closedCantorSet p = closedCantorSet q := by
  rw [closedCantorSet_eq_compl, closedCantorSet_eq_compl, h]

/-- The all-zero name presents the whole space — what the sentinel buys. -/
@[simp]
theorem closedCantorSet_zero : closedCantorSet (fun _ => 0) = Set.univ := by
  ext x
  simp only [closedCantorSet, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro i w hw
  exact absurd (cantorForbiddenWord_eq_none_iff.mpr rfl) (by rw [hw]; simp)

/-- **Closed choice on Cantor space**: from a negative name of a closed set, produce a
point of it. The domain is the nonemptiness promise. -/
def C_Cantor : Problem baireSpace cantorSpace := ⟨fun p x => x ∈ closedCantorSet p⟩

/-- **Definitional unfolding of `C_Cantor.accepts`.** An explicit rewrite lemma,
deliberately not a global `simp` rule. -/
theorem C_Cantor.accepts_iff {p : Baire} {x : Cantor} :
    C_Cantor.accepts p x ↔ ∀ i w, cantorForbiddenWord p i = some w → x ∉ cylinder w :=
  Iff.rfl

/-- **The semantic anchor**: the domain is exactly the names of nonempty closed sets. -/
theorem C_Cantor.dom_iff {p : Baire} : C_Cantor.Dom p ↔ (closedCantorSet p).Nonempty :=
  Iff.rfl

end ComputableAnalysis
