/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Reduction
import ComputableAnalysis.Weihrauch.Principles.LPO

/-!
# The lesser limited principle of omniscience and its reductions

`LLPO` receives a stream with **at most one** nonzero entry and must point at a track that
is entirely zero: answer `0` asserts the even track vanishes, answer `1` the odd track. On
the all-zero input both answers are permitted — the genuinely multivalued content, recorded
by the `example` below. `llpoSwap` is the same problem with the two tracks exchanged.

`llpo_le_lpo` reduces `LLPO` to `LPO`: preprocess by projecting the even track, ask `LPO`
whether it vanishes, and postprocess the `LPO` answer bit unchanged — a nonzero even entry
forces the odd track to vanish by the at-most-one constraint. `llpo_swap_le_llpo` reduces
`llpoSwap` to `LLPO` by the parity-swap preprocessor `p ↦ interleave p.oddPart p.evenPart`,
again forwarding the answer bit unchanged.
-/

namespace ComputableAnalysis

/-- **The lesser limited principle of omniscience**: on a stream with at most one nonzero
entry, answer `0` if the even track vanishes, `1` if the odd track vanishes. Multivalued:
on the all-zero stream both answers are accepted. -/
def LLPO : Problem baireSpace natSpace :=
  ⟨fun p (i : ℕ) => (∀ a b, p a ≠ 0 → p b ≠ 0 → a = b) ∧
    ((i = 0 ∧ ∀ n, p (2 * n) = 0) ∨ (i = 1 ∧ ∀ n, p (2 * n + 1) = 0))⟩

/-- `LLPO` with the roles of the two tracks exchanged: answer `0` asserts the odd track
vanishes, `1` the even track. Reduces to `LLPO` by the parity-swap preprocessor
(`llpo_swap_le_llpo`). -/
def llpoSwap : Problem baireSpace natSpace :=
  ⟨fun p (i : ℕ) => (∀ a b, p a ≠ 0 → p b ≠ 0 → a = b) ∧
    ((i = 0 ∧ ∀ n, p (2 * n + 1) = 0) ∨ (i = 1 ∧ ∀ n, p (2 * n) = 0))⟩

/-- Definitional unfolding of `LPO.accepts` (restated here because the copy in `LPO.lean`
is private to that file). -/
private theorem lpo_accepts_iff {p : Baire} {b : ℕ} :
    LPO.accepts p b ↔ (b = 0 ∧ ∀ n, p n = 0) ∨ (b = 1 ∧ ∃ n, p n ≠ 0) :=
  Iff.rfl

/-- Definitional unfolding of `LLPO.accepts`, so proofs never depend on `rcases`
unfolding the structure projection. -/
private theorem llpo_accepts_iff {p : Baire} {i : ℕ} :
    LLPO.accepts p i ↔ (∀ a b, p a ≠ 0 → p b ≠ 0 → a = b) ∧
      ((i = 0 ∧ ∀ n, p (2 * n) = 0) ∨ (i = 1 ∧ ∀ n, p (2 * n + 1) = 0)) :=
  Iff.rfl

/-- Definitional unfolding of `llpoSwap.accepts`. -/
private theorem llpoSwap_accepts_iff {p : Baire} {i : ℕ} :
    llpoSwap.accepts p i ↔ (∀ a b, p a ≠ 0 → p b ≠ 0 → a = b) ∧
      ((i = 0 ∧ ∀ n, p (2 * n + 1) = 0) ∨ (i = 1 ∧ ∀ n, p (2 * n) = 0)) :=
  Iff.rfl

/-- On the all-zero input, BOTH answers are permitted (the multivalued content). -/
example : LLPO.accepts (fun _ => 0) (0 : ℕ) ∧ LLPO.accepts (fun _ => 0) (1 : ℕ) :=
  ⟨llpo_accepts_iff.mpr ⟨fun _ _ ha _ => absurd rfl ha, Or.inl ⟨rfl, fun _ => rfl⟩⟩,
   llpo_accepts_iff.mpr ⟨fun _ _ ha _ => absurd rfl ha, Or.inr ⟨rfl, fun _ => rfl⟩⟩⟩

/-- The shared postprocessor `comp query (const 1)`: on any oracle `r` its stream value is
the constant stream at `r 1` — coordinate `1` of the interleaved input is the oracle
answer's coordinate `0`. -/
private theorem const_query_one_mem_evalStream (r : Baire) :
    (fun _ => r 1 : Baire) ∈ (OracleCode.comp .query (.const 1)).evalStream r := by
  refine OracleCode.mem_evalStream.mpr fun n => ?_
  rw [OracleCode.eval_comp_some (OracleCode.eval_const r 1 n), OracleCode.eval_query]
  exact Part.mem_some _

/-- **`LLPO ≤W LPO`.** Preprocess by projecting the even track and ask `LPO` whether it
vanishes; forward the answer bit unchanged. If `LPO` answers `1`, some even entry is
nonzero, and the at-most-one constraint forces the odd track to vanish. -/
theorem llpo_le_lpo : LLPO ≤W LPO := by
  obtain ⟨ce, hce⟩ := type2Computable_evenPart
  refine reduction_iff_exists_reductionPair.mpr
    ⟨ce, .comp .query (.const 1), fun p x hpx hdom => ?_⟩
  obtain rfl := (baireRep_names_iff.mp hpx).symm
  obtain ⟨i, hi⟩ := hdom
  obtain ⟨hone, -⟩ := llpo_accepts_iff.mp hi
  have hk : Baire.evenPart p ∈ ce.evalStream p := by
    rw [OracleCode.computes_iff_evalStream.mp hce p]
    exact Part.mem_some _
  refine ⟨Baire.evenPart p, hk, Baire.evenPart p, baireRep_names_iff.mpr rfl,
    LPO.dom_total _, fun a y' hay' hacc => ?_⟩
  obtain rfl := natRep_names_iff.mp hay'
  have h1 : Baire.interleave p a 1 = a 0 := by simpa using Baire.interleave_odd p a 0
  refine ⟨fun _ => Baire.interleave p a 1, const_query_one_mem_evalStream _, a 0,
    natRep_names_iff.mpr h1.symm, llpo_accepts_iff.mpr ⟨hone, ?_⟩⟩
  rcases lpo_accepts_iff.mp hacc with ⟨h0, hall⟩ | ⟨h1', n₀, hn₀⟩
  · exact Or.inl ⟨h0, fun n => hall n⟩
  · refine Or.inr ⟨h1', fun n => ?_⟩
    by_contra hodd
    have hcol := hone (2 * n₀) (2 * n + 1) hn₀ hodd
    omega

/-- **`llpoSwap ≤W LLPO`.** Preprocess by the parity swap `p ↦ interleave p.oddPart
p.evenPart`, which exchanges the two tracks; the at-most-one constraint transfers through
the swap, and the `LLPO` answer bit is forwarded unchanged. -/
theorem llpo_swap_le_llpo : llpoSwap ≤W LLPO := by
  obtain ⟨cs, hcs⟩ := type2Computable_oddPart.interleave type2Computable_evenPart
  refine reduction_iff_exists_reductionPair.mpr
    ⟨cs, .comp .query (.const 1), fun p x hpx hdom => ?_⟩
  obtain rfl := (baireRep_names_iff.mp hpx).symm
  have hSe : ∀ n, Baire.interleave p.oddPart p.evenPart (2 * n) = p (2 * n + 1) :=
    fun n => by simp
  have hSo : ∀ n, Baire.interleave p.oddPart p.evenPart (2 * n + 1) = p (2 * n) :=
    fun n => by simp
  obtain ⟨i, hi⟩ := hdom
  obtain ⟨hone, hdisj⟩ := llpoSwap_accepts_iff.mp hi
  -- The at-most-one-nonzero constraint transfers through the parity swap.
  have honeS : ∀ a b, Baire.interleave p.oddPart p.evenPart a ≠ 0 →
      Baire.interleave p.oddPart p.evenPart b ≠ 0 → a = b := by
    intro a b ha hb
    rcases Nat.even_or_odd' a with ⟨j, rfl | rfl⟩ <;>
      rcases Nat.even_or_odd' b with ⟨k, rfl | rfl⟩
    · rw [hSe] at ha hb; have := hone _ _ ha hb; omega
    · rw [hSe] at ha; rw [hSo] at hb; have := hone _ _ ha hb; omega
    · rw [hSo] at ha; rw [hSe] at hb; have := hone _ _ ha hb; omega
    · rw [hSo] at ha hb; have := hone _ _ ha hb; omega
  have hk : Baire.interleave p.oddPart p.evenPart ∈ cs.evalStream p := by
    rw [OracleCode.computes_iff_evalStream.mp hcs p]
    exact Part.mem_some _
  have hdomS : LLPO.Dom (Baire.interleave p.oddPart p.evenPart) := by
    rcases hdisj with ⟨-, hall⟩ | ⟨-, hall⟩
    · exact ⟨(0 : ℕ), llpo_accepts_iff.mpr
        ⟨honeS, Or.inl ⟨rfl, fun n => (hSe n).trans (hall n)⟩⟩⟩
    · exact ⟨(1 : ℕ), llpo_accepts_iff.mpr
        ⟨honeS, Or.inr ⟨rfl, fun n => (hSo n).trans (hall n)⟩⟩⟩
  refine ⟨Baire.interleave p.oddPart p.evenPart, hk, Baire.interleave p.oddPart p.evenPart,
    baireRep_names_iff.mpr rfl, hdomS, fun a y' hay' hacc => ?_⟩
  obtain rfl := natRep_names_iff.mp hay'
  have h1 : Baire.interleave p a 1 = a 0 := by simpa using Baire.interleave_odd p a 0
  refine ⟨fun _ => Baire.interleave p a 1, const_query_one_mem_evalStream _, a 0,
    natRep_names_iff.mpr h1.symm, llpoSwap_accepts_iff.mpr ⟨hone, ?_⟩⟩
  obtain ⟨-, hdisjS⟩ := llpo_accepts_iff.mp hacc
  rcases hdisjS with ⟨h0, hallS⟩ | ⟨h1', hallS⟩
  · exact Or.inl ⟨h0, fun n => (hSe n).symm.trans (hallS n)⟩
  · exact Or.inr ⟨h1', fun n => (hSo n).symm.trans (hallS n)⟩

end ComputableAnalysis
