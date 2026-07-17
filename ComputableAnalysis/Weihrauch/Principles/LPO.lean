/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Problem

/-!
# The limited principle of omniscience as a Weihrauch problem

`LPO` asks, for a stream `p : Baire`, whether `p` is identically zero: the accepted answer
is `0` when every coordinate vanishes and `1` when some coordinate does not. The problem is
total (`LPO.dom_total`) but not computable (`not_computableProblem_LPO`): any single oracle
code realizing it would answer `0` on the all-zero stream after reading only a finite use
set of coordinates, and flipping one unread coordinate to `1` forces the answer `1` on a
stream where the code still returns `0` — contradicting single-valuedness of `Part`.
-/

namespace ComputableAnalysis

/-- **The limited principle of omniscience** as a problem on Baire space: answer `0` when
the input stream is identically zero, `1` when some coordinate is nonzero. Total but not
computable. -/
def LPO : Problem baireSpace natSpace :=
  ⟨fun p (b : ℕ) => (b = 0 ∧ ∀ n, p n = 0) ∨ (b = 1 ∧ ∃ n, p n ≠ 0)⟩

/-- Definitional unfolding of `LPO.accepts`, so proofs never depend on `rcases`
unfolding the structure projection. -/
private theorem lpo_accepts_iff {p : Baire} {b : ℕ} :
    LPO.accepts p b ↔ (b = 0 ∧ ∀ n, p n = 0) ∨ (b = 1 ∧ ∃ n, p n ≠ 0) :=
  Iff.rfl

/-- `LPO` is a total problem: every stream is either identically zero or not. -/
theorem LPO.dom_total (p : Baire) : LPO.Dom p := by
  by_cases h : ∀ n, p n = 0
  · exact ⟨(0 : ℕ), lpo_accepts_iff.mpr (Or.inl ⟨rfl, h⟩)⟩
  · exact ⟨(1 : ℕ), lpo_accepts_iff.mpr (Or.inr ⟨rfl, not_forall.mp h⟩)⟩

/-- **`LPO` is not computable.** A realizing code would answer `0` on the all-zero stream
after reading only a finite use set; flipping one coordinate outside that set forces the
answer `1` while the code still outputs `0` at coordinate `0` — contradicting the
single-valuedness of `Part`. -/
theorem not_computableProblem_LPO : ¬ ComputableProblem LPO := by
  rintro ⟨c, hc⟩
  -- Run the realizer on the all-zero stream: the accepted answer must be `0`.
  obtain ⟨q, hq, b, hqb, hacc⟩ :=
    hc (fun _ => 0) (fun _ => 0) (baireRep_names_iff.mpr rfl) (LPO.dom_total _)
  have hb0 : b = (0 : ℕ) := by
    rcases lpo_accepts_iff.mp hacc with ⟨hb, -⟩ | ⟨-, n, hn⟩
    · exact hb
    · exact absurd rfl hn
  have hq0 : (0 : ℕ) ∈ c.eval (fun _ => 0) 0 := by
    have hmem := OracleCode.mem_evalStream.mp hq 0
    rwa [(natRep_names_iff.mp hqb).symm.trans hb0] at hmem
  -- Finite use: the answer `0` depends only on coordinates in a finite set `u`.
  obtain ⟨u, hu⟩ := OracleCode.eval_eq_of_agree_on_use hq0
  set m := u.sup id + 1 with hm_def
  have hm : m ∉ u := fun hmem => by
    have hle := Finset.le_sup (f := id) hmem
    simp only [id_eq] at hle
    omega
  -- Flip the unread coordinate `m`: the code still outputs `0` at coordinate `0`.
  set p' : Baire := fun n => if n = m then 1 else 0 with hp'_def
  have h0mem : (0 : ℕ) ∈ c.eval p' 0 := by
    refine hu p' fun i hi => ?_
    have hine : i ≠ m := fun h => hm (h ▸ hi)
    simp [hp'_def, hine]
  -- But the realizer on `p'` must answer `1`, since `p' m = 1 ≠ 0`.
  obtain ⟨q', hq', b', hq'b', hacc'⟩ := hc p' p' (baireRep_names_iff.mpr rfl) (LPO.dom_total _)
  have hb1 : b' = (1 : ℕ) := by
    rcases lpo_accepts_iff.mp hacc' with ⟨-, hall⟩ | ⟨hb, -⟩
    · have hpm : (1 : ℕ) = 0 := by simpa [hp'_def] using hall m
      exact absurd hpm one_ne_zero
    · exact hb
  have h1mem : (1 : ℕ) ∈ c.eval p' 0 := by
    have hmem := OracleCode.mem_evalStream.mp hq' 0
    rwa [(natRep_names_iff.mp hq'b').symm.trans hb1] at hmem
  exact one_ne_zero (Part.mem_unique h1mem h0mem)

end ComputableAnalysis
