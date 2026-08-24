/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Order.KonigLemma
import ComputableAnalysis.Weihrauch.Problem

/-!
# Explicit finite inverse-limit compactness as a Weihrauch problem

`EFILC` receives a name of a sequential inverse system of explicitly enumerated finite
fibers with adjacent bonding maps, and must produce a section.

**The presentation is total and positional.** A name `q : Baire` presents, on track `0`,
the level-`k` fiber as the code of a finite list (`efilcFiber q k`, through the
`Denumerable (List ℕ)` coding), and on track `1` the bond value `efilcBond q k x` sending
a level-`(k + 1)` element `x` down to level `k`. Every stream is a valid name of *some*
system; being a genuine system — nonempty fibers, bonds landing in the fiber below — is
not a condition on names but a promise inside the problem, exactly as `WKL`'s
prefix-closure and infinity promises are.

**The promises live in `accepts`** (`FibersNonempty`, `BondsIntoFiber`), and answers are
points of `baireSpace`: streams selecting, at every level, a fiber element, coherently
under the bonds (`IsEfilcSection`).

The semantic anchor is `EFILC.dom_iff`: the domain is exactly the promised systems, whose
nontrivial direction *is* finite inverse-limit compactness — proved through mathlib's
`exists_seq_forall_proj_of_forall_finite` with the iterated bond `efilcDown` as the
projection, exactly as `WKL.dom_iff` uses prefix restriction.

This presentation deliberately mirrors the enumerated-fiber EFILC statement variant of
the `reverse-mathlib` catalog (adjacent bonds, explicitly enumerated fibers); the
crosswalk between the two catalogs is registered there by name, never inferred.
-/

namespace ComputableAnalysis

open Encodable Denumerable

/-! ### The presented system -/

/-- The level-`k` fiber list presented by `q`: track `0`, decoded through the
`Denumerable (List ℕ)` coding. Total — every natural decodes to some list. -/
def efilcFiber (q : Baire) (k : ℕ) : List ℕ := ofNat (List ℕ) (q (Nat.pair 0 k))

/-- The bond value `q` assigns to the level-`(k + 1)` element `x`, landing at level `k`:
track `1`. Total — constrained only on fiber members, and only by the promise. -/
def efilcBond (q : Baire) (k x : ℕ) : ℕ := q (Nat.pair 1 (Nat.pair k x))

/-- Every presented fiber is nonempty. -/
def FibersNonempty (q : Baire) : Prop := ∀ k, efilcFiber q k ≠ []

/-- Every bond of a fiber member lands in the fiber below. -/
def BondsIntoFiber (q : Baire) : Prop :=
  ∀ k, ∀ x ∈ efilcFiber q (k + 1), efilcBond q k x ∈ efilcFiber q k

/-! ### Building a name from the semantic data

A reduction *into* `EFILC` has to write the wire format: track `0` the coded fibers,
track `1` the bonds, everything else inert. `efilcSystemName` is that encoder once, so a
reduction supplies only the two semantic functions and reads them back through the two
simp lemmas — no reduction needs to know the track layout. -/

/-- The name presenting the system with the given fibers and bonds. -/
def efilcSystemName (fiber : ℕ → List ℕ) (bond : ℕ → ℕ → ℕ) : Baire := fun n =>
  if n.unpair.1 = 0 then encode (fiber n.unpair.2)
  else if n.unpair.1 = 1 then bond n.unpair.2.unpair.1 n.unpair.2.unpair.2
  else 0

@[simp]
theorem efilcFiber_efilcSystemName (fiber : ℕ → List ℕ) (bond : ℕ → ℕ → ℕ) (k : ℕ) :
    efilcFiber (efilcSystemName fiber bond) k = fiber k := by
  simp [efilcFiber, efilcSystemName, Nat.unpair_pair]

@[simp]
theorem efilcBond_efilcSystemName (fiber : ℕ → List ℕ) (bond : ℕ → ℕ → ℕ) (k x : ℕ) :
    efilcBond (efilcSystemName fiber bond) k x = bond k x := by
  simp [efilcBond, efilcSystemName, Nat.unpair_pair]

/-- `s` is a section of the system presented by `q`: at every level a fiber element,
coherent under the bonds. -/
def IsEfilcSection (q s : Baire) : Prop :=
  (∀ k, s k ∈ efilcFiber q k) ∧ ∀ k, efilcBond q k (s (k + 1)) = s k

/-- **Explicit finite inverse-limit compactness** as a problem: on a sequential system of
explicitly enumerated nonempty finite fibers with adjacent bonds, produce a section. -/
def EFILC : Problem baireSpace baireSpace :=
  ⟨fun q s => FibersNonempty q ∧ BondsIntoFiber q ∧ IsEfilcSection q s⟩

/-- **Definitional unfolding of `EFILC.accepts`.** An explicit rewrite lemma, deliberately
not a global `simp` rule. -/
theorem EFILC.accepts_iff {q s : Baire} :
    EFILC.accepts q s ↔ FibersNonempty q ∧ BondsIntoFiber q ∧ IsEfilcSection q s :=
  Iff.rfl

/-! ### The iterated bond -/

/-- Push an element down from level `j` to level `i ≤ j`, one bond at a time. Total on all
inputs; the fiber-membership and composition laws below are the ones that matter. -/
def efilcDown (q : Baire) : ℕ → ℕ → ℕ → ℕ
  | 0, _, x => x
  | j + 1, i, x => if j + 1 ≤ i then x else efilcDown q j i (efilcBond q j x)

@[simp]
theorem efilcDown_self (q : Baire) (i x : ℕ) : efilcDown q i i x = x := by
  cases i with
  | zero => rfl
  | succ j => rw [efilcDown, ite_eq_left le_rfl]

theorem efilcDown_succ (q : Baire) {j i : ℕ} (h : i ≤ j) (x : ℕ) :
    efilcDown q (j + 1) i x = efilcDown q j i (efilcBond q j x) := by
  rw [efilcDown, ite_eq_right (by omega)]

theorem efilcDown_succ_self (q : Baire) (j x : ℕ) :
    efilcDown q (j + 1) j x = efilcBond q j x := by
  rw [efilcDown_succ q le_rfl, efilcDown_self]

theorem efilcDown_mem {q : Baire} (hB : BondsIntoFiber q) :
    ∀ {j i : ℕ}, i ≤ j → ∀ {x : ℕ}, x ∈ efilcFiber q j → efilcDown q j i x ∈ efilcFiber q i := by
  intro j
  induction j with
  | zero =>
    intro i hij x hx
    obtain rfl : i = 0 := by omega
    exact hx
  | succ j ih =>
    intro i hij x hx
    rcases Nat.eq_or_lt_of_le hij with rfl | hlt
    · rwa [efilcDown_self]
    · rw [efilcDown_succ q (by omega)]
      exact ih (by omega) (hB j x hx)

theorem efilcDown_trans (q : Baire) :
    ∀ {k j i : ℕ}, i ≤ j → j ≤ k → ∀ x : ℕ,
      efilcDown q j i (efilcDown q k j x) = efilcDown q k i x := by
  intro k
  induction k with
  | zero =>
    intro j i hij hjk x
    obtain rfl : j = 0 := by omega
    obtain rfl : i = 0 := by omega
    rfl
  | succ k ih =>
    intro j i hij hjk x
    rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
    · rw [efilcDown_self]
    · rw [efilcDown_succ q (by omega), efilcDown_succ q (by omega : i ≤ k),
        ih hij (by omega)]

/-! ### The domain is exactly the promised systems -/

/-- **Explicit finite inverse-limit compactness**: a promised system has a section —
mathlib's ℕ-indexed inverse-system lemma applied to the fibers under the iterated bond. -/
theorem exists_section_of_promises {q : Baire} (hne : FibersNonempty q)
    (hB : BondsIntoFiber q) : ∃ s : Baire, IsEfilcSection q s := by
  classical
  let α : ℕ → Type := fun k => {x : ℕ // x ∈ efilcFiber q k}
  let proj : {i j : ℕ} → (hij : i ≤ j) → α j → α i := fun {i j} hij a =>
    ⟨efilcDown q j i a.1, efilcDown_mem hB hij a.2⟩
  have : ∀ k, Finite (α k) := fun k => (List.finite_toSet _).to_subtype
  have : ∀ k, Nonempty (α k) := fun k => by
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne k)
    exact ⟨⟨x, hx⟩⟩
  obtain ⟨f, hf⟩ := exists_seq_forall_proj_of_forall_finite (α := α) proj
    (fun {i} a => Subtype.ext (efilcDown_self q i a.1))
    (fun {i j _} hij hjk a => Subtype.ext (efilcDown_trans q hij hjk a.1))
    (fun i a => Set.toFinite _)
  refine ⟨fun k => (f k).1, fun k => (f k).2, fun k => ?_⟩
  have hcoh := congrArg Subtype.val (hf (Nat.le_succ k))
  simpa [proj, efilcDown_succ_self] using hcoh

/-- **The semantic anchor**: `EFILC`'s domain is exactly the promised systems. -/
theorem EFILC.dom_iff {q : Baire} : EFILC.Dom q ↔ FibersNonempty q ∧ BondsIntoFiber q := by
  constructor
  · rintro ⟨s, hne, hB, -⟩
    exact ⟨hne, hB⟩
  · rintro ⟨hne, hB⟩
    obtain ⟨s, hs⟩ := exists_section_of_promises hne hB
    exact ⟨s, hne, hB, hs⟩

end ComputableAnalysis
