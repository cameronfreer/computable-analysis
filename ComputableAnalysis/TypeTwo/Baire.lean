/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.GetD
import Mathlib.Computability.Primrec.List
import Mathlib.Topology.MetricSpace.PiNat

/-!
# Baire space: finite words, prefixes, and cylinders

`Baire := ℕ → ℕ` carries the product topology (each factor discrete). This file
provides the finite-observation layer used by every later file: stream prefixes
(`streamTake`), extension of a finite word to a stream (`streamExtend`), word
cylinders (`cylinder`), their clopenness, and first-order computability of the
finite-word operations.

The definitions are stated for streams `ℕ → α` over an arbitrary type so that
Cantor space (`ℕ → Bool`) reuses them verbatim.

No Type-2 statement appears in this file: `Baire` is not `Primcodable`, so
mathlib's first-order `Computable` applies only to the `List` side. Computability
of stream operators is introduced with the oracle-code layer.

The stream operations are deliberately defined arithmetically (`fun n => p (2 * n)`
etc.) rather than through mathlib's corecursive `Stream'` API (`Stream'.even`,
`Stream'.interleave`, ...): the oracle-machine layer manipulates index arithmetic
directly (a realizer for `evenPart` is `query ∘ (· * 2)`), so definitional
transparency at each coordinate is load-bearing, where the corecursive definitions
unfold only through their fixpoint equations.
-/

namespace ComputableAnalysis

/-- Baire space: streams of natural numbers, with the product topology. -/
abbrev Baire : Type := ℕ → ℕ

variable {α : Type*}

/-! ### Prefixes, extensions, and cylinders -/

/-- The length-`n` prefix of a stream, as a finite word. -/
def streamTake (p : ℕ → α) (n : ℕ) : List α :=
  List.ofFn fun i : Fin n => p i

/-- Extend a finite word to a stream, continuing with (a shifted copy of) `p`. -/
def streamExtend (s : List α) (p : ℕ → α) : ℕ → α := fun n =>
  if h : n < s.length then s[n] else p (n - s.length)

/-- The cylinder of streams beginning with the finite word `s`. -/
def cylinder (s : List α) : Set (ℕ → α) :=
  {p | ∀ i, (h : i < s.length) → p i = s[i]}

@[simp]
theorem length_streamTake (p : ℕ → α) (n : ℕ) : (streamTake p n).length = n := by
  simp [streamTake]

@[simp]
theorem getElem_streamTake (p : ℕ → α) (n i : ℕ) (h : i < (streamTake p n).length) :
    (streamTake p n)[i] = p i := by
  simp [streamTake]

/-- Reading a taken prefix below its length returns the stream's value, for any default.
The default is implicit: it is determined by the goal. -/
@[simp] theorem streamTake_getD (p : ℕ → α) {n i : ℕ} {d : α} (h : i < n) :
    (streamTake p n).getD i d = p i := by
  rw [List.getD_eq_getElem _ _ (by rw [length_streamTake]; exact h), getElem_streamTake]

@[simp]
theorem streamExtend_apply_lt (s : List α) (p : ℕ → α) {n : ℕ} (h : n < s.length) :
    streamExtend s p n = s[n] :=
  dif_pos h

@[simp]
theorem streamExtend_apply_ge (s : List α) (p : ℕ → α) {n : ℕ} (h : s.length ≤ n) :
    streamExtend s p n = p (n - s.length) :=
  dif_neg (Nat.not_lt.mpr h)

theorem mem_cylinder_iff {s : List α} {p : ℕ → α} :
    p ∈ cylinder s ↔ streamTake p s.length = s := by
  constructor
  · intro hp
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    simpa using hp i h₂
  · intro hp i h
    calc p i = (streamTake p s.length)[i]'(by simpa using h) := by simp
      _ = s[i] := List.getElem_of_eq hp _

theorem streamExtend_mem_cylinder (s : List α) (p : ℕ → α) :
    streamExtend s p ∈ cylinder s :=
  fun _ h => streamExtend_apply_lt s p h

theorem streamTake_streamExtend (s : List α) (p : ℕ → α) :
    streamTake (streamExtend s p) s.length = s :=
  mem_cylinder_iff.mp (streamExtend_mem_cylinder s p)

theorem mem_cylinder_streamTake (p : ℕ → α) (n : ℕ) : p ∈ cylinder (streamTake p n) := by
  intro i h
  simp

theorem getElem?_streamTake_of_lt (p : ℕ → α) {m i : ℕ} (h : i < m) :
    (streamTake p m)[i]? = some (p i) := by
  rw [List.getElem?_eq_getElem (by simpa using h)]
  simp

/-- Prefixes of a stream are nested. -/
theorem streamTake_prefix (p : ℕ → α) {m n : ℕ} (h : m ≤ n) :
    streamTake p m <+: streamTake p n := by
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simpa using h) fun i h₁ h₂ => ?_
  simp

@[simp]
theorem cylinder_nil : cylinder ([] : List α) = Set.univ := by
  ext p
  simp [cylinder]

/-- Word cylinders around a point are `PiNat` cylinders. -/
theorem cylinder_streamTake (p : ℕ → α) (n : ℕ) :
    cylinder (streamTake p n) = PiNat.cylinder p n := by
  ext q
  constructor
  · intro hq i hi
    have h := hq i (by simpa using hi)
    rwa [getElem_streamTake] at h
  · intro hq i hi
    rw [getElem_streamTake]
    exact hq i (by simpa using hi)

/-- Every nonempty-domain word cylinder arises from any of its members. -/
theorem cylinder_eq_of_mem {s : List α} {p : ℕ → α} (hp : p ∈ cylinder s) :
    cylinder s = PiNat.cylinder p s.length := by
  rw [← cylinder_streamTake, mem_cylinder_iff.mp hp]

theorem cylinder_eq_iInter (s : List α) :
    cylinder s = ⋂ i : Fin s.length, (fun p : ℕ → α => p i.1) ⁻¹' {s[i.1]} := by
  ext p
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
    Set.mem_singleton_iff]
  exact ⟨fun h i => h i.1 i.2, fun h i hi => h ⟨i, hi⟩⟩

section Topology

variable [TopologicalSpace α] [DiscreteTopology α]

theorem isClopen_cylinder (s : List α) : IsClopen (cylinder s) := by
  rw [cylinder_eq_iInter]
  constructor
  · exact isClosed_iInter fun i =>
      (isClosed_singleton (x := s[i.1])).preimage (continuous_apply i.1)
  · exact isOpen_iInter_of_finite fun i =>
      (isOpen_discrete {s[i.1]}).preimage (continuous_apply i.1)

theorem isOpen_cylinder (s : List α) : IsOpen (cylinder s) :=
  (isClopen_cylinder s).isOpen

theorem isClosed_cylinder (s : List α) : IsClosed (cylinder s) :=
  (isClopen_cylinder s).isClosed

end Topology

/-! ### First-order computability of word operations

The stream-level operations above are not first-order objects; the word-level
operations are, and later files rely on their (primitive-recursive, hence
computable) closure properties. Append, `take`, `length`, `getD`, and `map` come
directly from mathlib (`Primrec.list_append`, `Primrec.list_take`, …); prefix
comparison is provided here.
-/

section WordComputability

variable [Primcodable α]

theorem primrec_isPrefix :
    PrimrecRel fun s t : List α => s <+: t := by
  have h : PrimrecPred fun q : List α × List α => q.1 = q.2.take q.1.length :=
    Primrec.eq.comp Primrec.fst
      (Primrec.list_take.comp (Primrec.list_length.comp Primrec.fst) Primrec.snd)
  exact PrimrecPred.of_eq h fun q => List.prefix_iff_eq_take.symm

end WordComputability

/-- `streamTake` grows by snoc. -/
theorem streamTake_succ (p : ℕ → α) (k : ℕ) :
    streamTake p (k + 1) = streamTake p k ++ [p k] := by
  simp only [streamTake, List.ofFn_succ_last, Fin.val_last, Fin.val_castSucc]

/-! ### Interleaving and deinterleaving of Baire names -/

/-- Interleave two streams: even coordinates from `p`, odd from `q`. -/
def Baire.interleave (p q : Baire) : Baire :=
  fun n => if n % 2 = 0 then p (n / 2) else q (n / 2)

@[simp] theorem Baire.interleave_even (p q : Baire) (n : ℕ) :
    Baire.interleave p q (2 * n) = p n := by
  have h1 : 2 * n % 2 = 0 := by omega
  have h2 : 2 * n / 2 = n := by omega
  simp [Baire.interleave, h1, h2]

@[simp] theorem Baire.interleave_odd (p q : Baire) (n : ℕ) :
    Baire.interleave p q (2 * n + 1) = q n := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp [Baire.interleave, h1, h2]

/-- The even-coordinate projection of a stream. -/
def Baire.evenPart (p : Baire) : Baire := fun n => p (2 * n)

/-- The odd-coordinate projection of a stream. -/
def Baire.oddPart (p : Baire) : Baire := fun n => p (2 * n + 1)

@[simp] theorem Baire.evenPart_apply (p : Baire) (n : ℕ) : Baire.evenPart p n = p (2 * n) := rfl
@[simp] theorem Baire.oddPart_apply (p : Baire) (n : ℕ) : Baire.oddPart p n = p (2 * n + 1) := rfl

/-- Interleaving is inverse to the two projections. -/
theorem Baire.interleave_evenPart_oddPart (p : Baire) :
    Baire.interleave (Baire.evenPart p) (Baire.oddPart p) = p := by
  funext n; rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩ <;> simp

@[simp] theorem Baire.evenPart_interleave (p q : Baire) :
    Baire.evenPart (Baire.interleave p q) = p := by funext n; simp

@[simp] theorem Baire.oddPart_interleave (p q : Baire) :
    Baire.oddPart (Baire.interleave p q) = q := by funext n; simp

end ComputableAnalysis
