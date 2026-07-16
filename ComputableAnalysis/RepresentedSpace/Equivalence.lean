/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.ComputableMap
import ComputableAnalysis.TypeTwo.StreamExamples

/-!
# Representation equivalence

Two representations of one carrier are **computably equivalent** (`X ≡c X'`) when the
identity is a computable map in both directions: names translate effectively either way.
Equivalence is an equivalence relation, and both computability of maps and computability
of points are invariant under it — the sense in which the theory depends on a
representation only up to computable translation.

Worked example (the units 7–9 acceptance test): the redundant Cantor representation
`cantorRepRedundant` accepts *every* name, decoding by the neutral zero/positive rule.
It is equivalent to the strict `cantorRep`: a strict name is already a redundant name of
the same point (`query` realizes one direction), and `truncate` computably repairs any
name into a strict one (`type2Computable_truncate` realizes the other).
-/

namespace ComputableAnalysis

universe u v

variable {α : Type u} {β : Type v}

namespace Representation

/-- `X ≡c X'`: the identity is a computable map in both directions, so names translate
effectively either way. -/
def Equiv (X X' : Representation α) : Prop :=
  ComputableMap X X' id ∧ ComputableMap X' X id

@[inherit_doc] infix:50 " ≡c " => Representation.Equiv

namespace Equiv

variable {X X' X'' : Representation α} {Y Y' : Representation β}

protected theorem refl : X ≡c X := ⟨.id, .id⟩

protected theorem symm (h : X ≡c X') : X' ≡c X := ⟨h.2, h.1⟩

protected theorem trans (h : X ≡c X') (h' : X' ≡c X'') : X ≡c X'' :=
  ⟨h'.1.comp h.1, h.2.comp h'.2⟩

/-- **Invariance of computable maps.** Computability of `f` depends on the representations
only up to equivalence. -/
theorem computableMap_congr {f : α → β} (hX : X ≡c X') (hY : Y ≡c Y') :
    ComputableMap X Y f ↔ ComputableMap X' Y' f :=
  ⟨fun hf => hY.1.comp (hf.comp hX.2), fun hf => hY.2.comp (hf.comp hX.1)⟩

/-- **Invariance of computable points.** Computability of a point depends on the
representation only up to equivalence. -/
theorem computablePoint_congr {a : α} (hX : X ≡c X') :
    X.ComputablePoint a ↔ X'.ComputablePoint a :=
  ⟨fun ha => hX.1.computablePoint ha, fun ha => hX.2.computablePoint ha⟩

end Equiv

end Representation

/-- The redundant Cantor representation: every name is valid, decoded by the neutral
zero/positive rule (`0 ↦ false`, positive ↦ `true`). -/
def cantorRepRedundant : Representation Cantor where
  rep p := Part.some (natStreamToBool p)
  onto x := ⟨encodeCantor x, Part.mem_some_iff.mpr (by
    funext n; cases hxn : x n <;> simp [hxn])⟩

/-- Names of the redundant Cantor representation: every stream names its decoding. -/
@[simp]
theorem cantorRepRedundant_names_iff {p : Baire} {x : Cantor} :
    cantorRepRedundant.Names p x ↔ x = natStreamToBool p :=
  Part.mem_some_iff

/-- The strict and redundant Cantor representations are computably equivalent: a strict
name already is a redundant name of the same point (`query`), and `truncate` computably
repairs an arbitrary name into a strict one. The units 7–9 worked example of two
computably equivalent representations of one carrier. -/
theorem cantorRep_equiv_redundant : cantorRep ≡c cantorRepRedundant := by
  constructor
  · refine ⟨.query, fun p x hpx => ⟨p, by simp, ?_⟩⟩
    obtain ⟨hle, hx⟩ := cantorRep_names_iff.mp hpx
    refine cantorRepRedundant_names_iff.mpr (hx.trans (funext fun n => ?_))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hle n) with h | h <;> simp [h]
  · obtain ⟨c, hc⟩ := type2Computable_truncate
    refine ⟨c, .of_computes hc fun p x hpx => ?_⟩
    rw [cantorRepRedundant_names_iff.mp hpx]
    refine cantorRep_names_iff.mpr ⟨truncate_le_one p, funext fun n => ?_⟩
    rcases Nat.eq_zero_or_pos (p n) with h | h
    · simp [truncate, h]
    · simp [truncate, h, Nat.min_eq_right h]

end ComputableAnalysis
