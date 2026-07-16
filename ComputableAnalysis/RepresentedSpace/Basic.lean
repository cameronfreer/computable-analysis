/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Cantor
import Mathlib.Computability.Partrec

/-!
# Represented spaces: representations and computable points

A **representation** of `α` is a partial surjection `rep : Baire →. α` (convention 4).
`Names`/`Valid` read off its graph and domain, and `onto` guarantees every point has a
name. Because `Part α` is single-valued, a valid name denotes at most one point
(`names_unique`); multivaluedness enters only at the problem layer (unit 10).

A point is a **computable point** when it has a first-order computable name: `Computable p`
treats `p : ℕ → ℕ` as an ordinary function (only the ℕ input/output are `Primcodable`;
`Baire` itself is not — convention 3).

`RepSpace` bundles a carrier with one chosen representation, for the later units where the
endpoints of maps and reductions vary. The explicit objects `baireRep`, `cantorRep`,
`natRep`, `discreteRep` are built as data, never as instances, and invalid names stay
invalid: `cantorRep` rejects any name with a coordinate `≥ 2`.
-/

namespace ComputableAnalysis

universe u

/-- A representation of `α`: a partial surjection from Baire names onto `α`. -/
structure Representation (α : Type u) where
  /-- The partial decoding of a Baire name to a point of `α`. -/
  rep : Baire →. α
  /-- Every point has at least one name. -/
  onto : ∀ a, ∃ p, a ∈ rep p

namespace Representation

variable {α : Type u}

/-- `p` is a name of `a` under `X`. -/
def Names (X : Representation α) (p : Baire) (a : α) : Prop := a ∈ X.rep p

/-- `p` is a valid name under `X` (it denotes some point). -/
def Valid (X : Representation α) (p : Baire) : Prop := (X.rep p).Dom

/-- A name is valid iff it denotes some point. -/
theorem valid_iff_exists_names {X : Representation α} {p : Baire} :
    X.Valid p ↔ ∃ a, X.Names p a := Part.dom_iff_mem

/-- Names are single-valued: a valid name denotes at most one point. Multivaluedness begins
at `Problem.accepts` (unit 10), never at `Representation`. -/
theorem names_unique {X : Representation α} {p : Baire} {a b : α}
    (ha : X.Names p a) (hb : X.Names p b) : a = b := Part.mem_unique ha hb

/-- `a` is a **computable point** of `X`: it has a first-order computable name. `Computable p`
treats `p : ℕ → ℕ` as an ordinary function (only ℕ is `Primcodable`; `Baire` is not). -/
def ComputablePoint (X : Representation α) (a : α) : Prop :=
  ∃ p : Baire, Computable p ∧ X.Names p a

end Representation

/-- A represented space: a carrier bundled with one chosen representation. Used where the
endpoints of maps and reductions vary (units 10–11); units 8–9 stay on bare
`Representation`. -/
structure RepSpace where
  /-- The underlying carrier type. -/
  carrier : Type u
  /-- The chosen representation of the carrier. -/
  rep : Representation carrier

instance : CoeSort (RepSpace.{u}) (Type u) := ⟨RepSpace.carrier⟩

/-! ### Explicit representations (data, never instances; invalid names stay invalid) -/

/-- Baire space represents itself by the identity. -/
def baireRep : Representation Baire where
  rep p := Part.some p
  onto a := ⟨a, Part.mem_some a⟩

/-- Cantor space (convention 4): a valid name takes values in `{0,1}` (`0 ↦ false`,
`1 ↦ true`); a name with any coordinate `≥ 2` has no denotation. -/
def cantorRep : Representation Cantor where
  rep p := Part.assert (∀ n, p n ≤ 1) fun _ => Part.some fun n => p n == 1
  onto x := ⟨encodeCantor x,
    Part.mem_assert (fun n => by simp only [encodeCantor_apply]; split <;> omega)
      (by
        have hg : (fun n => encodeCantor x n == 1) = x := by
          funext n; cases hxn : x n <;> simp [encodeCantor_apply, hxn]
        rw [hg]; exact Part.mem_some x)⟩

/-- The naturals, represented by the first coordinate of the name. -/
def natRep : Representation ℕ where
  rep p := Part.some (p 0)
  onto n := ⟨fun _ => n, Part.mem_some n⟩

/-- Any countable type, represented by decoding the first coordinate. Partial: a code whose
first coordinate does not decode has no denotation — no default-point totalization. -/
def discreteRep {α : Type u} [Encodable α] : Representation α where
  rep p := Part.ofOption (Encodable.decode (p 0))
  onto a := ⟨fun _ => Encodable.encode a, by simp [Encodable.encodek]⟩

/-! ### Names characterizations

One `simp` lemma per explicit representation, unpacking the `Part` plumbing once so
consumers never touch `Part.assert`/`Part.ofOption` internals. -/

@[simp]
theorem baireRep_names_iff {p q : Baire} : baireRep.Names p q ↔ q = p :=
  Part.mem_some_iff

@[simp]
theorem cantorRep_names_iff {p : Baire} {x : Cantor} :
    cantorRep.Names p x ↔ (∀ n, p n ≤ 1) ∧ x = fun n => p n == 1 := by
  simp [Representation.Names, cantorRep, Part.mem_assert_iff, Part.mem_some_iff]

@[simp]
theorem natRep_names_iff {p : Baire} {n : ℕ} : natRep.Names p n ↔ n = p 0 :=
  Part.mem_some_iff

@[simp]
theorem discreteRep_names_iff {α : Type u} [Encodable α] {p : Baire} {a : α} :
    discreteRep.Names p a ↔ Encodable.decode (p 0) = some a := by
  simp [Representation.Names, discreteRep, Part.mem_ofOption, Option.mem_def]

/-- An invalid Cantor name (some coordinate `≥ 2`) denotes nothing. -/
example : ¬ cantorRep.Valid (fun _ => 2) := by
  intro h
  obtain ⟨hle, -⟩ := h
  exact absurd (hle 0) (by decide)

/-! ### Named represented spaces -/

/-- Baire space as a `RepSpace`. -/
def baireSpace : RepSpace := ⟨Baire, baireRep⟩

/-- Cantor space as a `RepSpace`. -/
def cantorSpace : RepSpace := ⟨Cantor, cantorRep⟩

/-- The naturals as a `RepSpace`. -/
def natSpace : RepSpace := ⟨ℕ, natRep⟩

end ComputableAnalysis
