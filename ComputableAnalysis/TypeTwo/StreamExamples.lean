/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Continuity
import ComputableAnalysis.TypeTwo.Cantor

/-!
# Stream-operator examples

Worked instances of the stream layer: identity, constants, the stream shift, and the
name-level `truncate` retraction (defined in `Cantor.lean`) are all `Type2Computable`;
and a total discontinuous map is proved **not** `Type2Computable` via the continuity
theorem. The underlying stream constructions live in the core modules
`Baire.lean`/`Cantor.lean`; the closure lemmas consumed by the represented-space layer
(`type2Computable_const_stream`/`query_comp`/`evenPart`/`oddPart`, output pairing) live
in `Continuity.lean`. This file holds only worked instances and the separating example.
-/

namespace ComputableAnalysis

open OracleCode

/-! ### `Type2Computable` examples -/

/-- The identity stream operator is Type-2 computable (via `query`). -/
theorem type2Computable_id : Type2Computable (id : Baire → Baire) :=
  ⟨query, fun p n => eval_query p n⟩

/-- The constant map to the value-`k` stream is Type-2 computable (via `const`). -/
theorem type2Computable_const (k : ℕ) : Type2Computable (fun _ : Baire => fun _ : ℕ => k) :=
  ⟨OracleCode.const k, fun p n => by simp⟩

/-- The stream shift `p ↦ (n ↦ p (n+1))` is Type-2 computable. -/
theorem type2Computable_shift : Type2Computable (fun p : Baire => fun n => p (n + 1)) :=
  ⟨comp query succ, fun p n => by simp [eval_comp, eval_succ, some_bind_pfun]⟩

/-- The name-level `truncate` retraction (defined in `Cantor.lean`) is Type-2 computable. -/
theorem type2Computable_truncate : Type2Computable truncate := by
  have hmin : Computable (fun m : ℕ => min m 1) :=
    ((Primrec.nat_sub.comp (Primrec.const 1)
      (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id)).to_comp).of_eq
      (fun m => by simp only [id_eq]; omega)
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1 hmin.partrec
  refine ⟨comp (ofPartrecCode E) query, fun p n => ?_⟩
  rw [eval_comp, eval_query, some_bind_pfun, eval_ofPartrecCode, hE]
  simp [truncate]

/-! ### A total discontinuous map that is not Type-2 computable -/

/-- The all-zero stream. -/
def zeroStream : Baire := fun _ => 0

open Classical in
/-- A total map whose value flags whether the input is not identically zero. It is
discontinuous at the all-zero stream, hence not Type-2 computable. -/
noncomputable def notAllZero (p : Baire) : Baire := fun _ => if ∀ n, p n = 0 then 0 else 1

theorem not_type2Computable_notAllZero : ¬ Type2Computable notAllZero := by
  intro h
  have hc0 : Continuous fun p : Baire => notAllZero p 0 :=
    (continuous_apply 0).comp (type2Computable_continuous h)
  have hpre : (fun p : Baire => notAllZero p 0) ⁻¹' {0} = {zeroStream} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, notAllZero]
    by_cases hp : ∀ n, p n = 0
    · rw [ite_eq_left hp]
      exact ⟨fun _ => funext hp, fun _ => rfl⟩
    · rw [ite_eq_right hp]
      exact ⟨fun h1 => absurd h1 one_ne_zero, fun hpz => absurd (fun n => hpz ▸ rfl) hp⟩
  have hopen : IsOpen ({zeroStream} : Set Baire) :=
    hpre ▸ hc0.isOpen_preimage {0} (isOpen_discrete _)
  rw [isOpen_pi_iff] at hopen
  obtain ⟨I, t, ht, hsub⟩ := hopen zeroStream rfl
  obtain ⟨m, hm⟩ : ∃ m, m ∉ I :=
    ⟨I.sup id + 1, fun hmem => Nat.not_succ_le_self _ (Finset.le_sup (f := id) hmem)⟩
  have hqmem : (fun n => if n ∈ I then (0 : ℕ) else 1) ∈ (I : Set ℕ).pi t := by
    intro i hi
    simp only [ite_eq_left (Finset.mem_coe.mp hi)]
    simpa [zeroStream] using (ht i (Finset.mem_coe.mp hi)).2
  have hqz := hsub hqmem
  rw [Set.mem_singleton_iff] at hqz
  have hm' := congrFun hqz m
  simp only [ite_eq_right hm, zeroStream] at hm'
  exact one_ne_zero hm'

end ComputableAnalysis
