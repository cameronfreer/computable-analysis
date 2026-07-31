/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Parallelize
import ComputableAnalysis.Weihrauch.Principles.Limit

/-!
# Uniform reduction compilers for the standard targets

Constructors that discharge, once and for all, the representation plumbing of a strong
reduction to a standard target, so individual reductions state only their mathematical
content.

* `isStrongReductionPair_parallelize_lpo_of_questions`: to reduce to parallelized `LPO`,
  it suffices to produce from each valid input name a packed **question family** `G` and
  to convert any **bit-consistent** answer stream — any `a` whose bit at `Nat.pair j 0`
  is `0` when question `j` is everywhere zero and `1` when it is somewhere nonzero —
  into an accepted output name. The constructor handles the countable-product names, the
  bit decoding through `natRep`, and the totality of `LPO` on every track.
* `isStrongReductionPair_lim_of_table`: to reduce to `Lim`, it suffices to produce a
  **table** in `Lim`'s domain and decode any of its limit streams. The constructor
  handles the Baire-name identities on both sides.

Both come with propositional corollaries (`sigma1Family_le_parallelize_lpo`,
`stabilizationTable_le_lim`). The composite entry point sending Σ₁ question families
through the calibration to `Lim` lives with the calibration
(`sigma1Family_le_lim` in `Principles/LimParallelizeLPO.lean`), which also re-derives
its explicit reduction pair through the first constructor — the adequacy test that the
interface captures the plumbing.
-/

namespace ComputableAnalysis

universe u v

variable {X : RepSpace.{u}} {Y : RepSpace.{v}}

/-- An answer stream is **bit-consistent** with a packed question family when its bit at
`Nat.pair j 0` answers question `j`: `0` if track `j` is everywhere zero, `1` if it is
somewhere nonzero. This is exactly what an accepted `LPO.parallelize` answer name
provides. -/
def BitConsistent (G a : Baire) : Prop :=
  ∀ j : ℕ, (a (Nat.pair j 0) = 0 ∧ ∀ k, Baire.track j G k = 0) ∨
    (a (Nat.pair j 0) = 1 ∧ ∃ k, Baire.track j G k ≠ 0)

/-- **The `LPO.parallelize` compiler.** To exhibit `(K, H)` as a strong reduction pair
into parallelized `LPO`, it suffices that on every valid input name `K` produces a
packed question family and `H` converts every bit-consistent answer stream into an
accepted output name. The countable-product names, the `natRep` bit decoding, and the
totality of `LPO` on the tracks are discharged here. -/
theorem isStrongReductionPair_parallelize_lpo_of_questions {f : Problem X Y}
    {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ G ∈ K.evalStream p,
        ∀ a : Baire, BitConsistent G a →
          ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y) :
    IsStrongReductionPair f LPO.parallelize K H := by
  intro p x hpx hdom
  obtain ⟨G, hG, hpost⟩ := h p x hpx hdom
  refine ⟨G, hG, fun j => Baire.track j G, ?_, ?_, ?_⟩
  · exact Representation.sequence_names_iff.mpr fun j => baireRep_names_iff.mpr rfl
  · rw [Problem.parallelize_dom_iff]
    intro j
    by_cases hall : ∀ k, Baire.track j G k = 0
    · exact ⟨(0 : ℕ), LPO.accepts_iff.mpr (Or.inl ⟨rfl, hall⟩)⟩
    · obtain ⟨k, hk⟩ := not_forall.mp hall
      exact ⟨(1 : ℕ), LPO.accepts_iff.mpr (Or.inr ⟨rfl, k, hk⟩)⟩
  · intro a ys hays hacc
    have hacc' := Problem.parallelize_accepts_iff.mp hacc
    have hbit : ∀ j, ys j = a (Nat.pair j 0) := natSequence_names_iff.mp hays
    refine hpost a fun j => ?_
    rcases LPO.accepts_iff.mp (hacc' j) with ⟨hb, hall⟩ | ⟨hb, hne⟩
    · exact Or.inl ⟨(hbit j).symm.trans hb, hall⟩
    · exact Or.inr ⟨(hbit j).symm.trans hb, hne⟩

/-- **The Σ₁-family compiler**, propositionally: a problem whose instances can uniformly
pose countably many Σ₁ questions and decode any consistent answer bits reduces strongly
to parallelized `LPO`. -/
theorem sigma1Family_le_parallelize_lpo {f : Problem X Y} {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ G ∈ K.evalStream p,
        ∀ a : Baire, BitConsistent G a →
          ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y) :
    f ≤sW LPO.parallelize :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨K, H, isStrongReductionPair_parallelize_lpo_of_questions h⟩

/-- **The `Lim` compiler.** To exhibit `(K, H)` as a strong reduction pair into `Lim`,
it suffices that on every valid input name `K` produces a table in `Lim`'s domain and
`H` decodes every limit stream of that table into an accepted output name. The
Baire-name identities on both sides are discharged here. -/
theorem isStrongReductionPair_lim_of_table {f : Problem X Y} {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ z ∈ K.evalStream p, Lim.Dom z ∧
        ∀ q : Baire, Lim.accepts z q →
          ∃ r ∈ H.evalStream q, ∃ y, Y.rep.Names r y ∧ f.accepts x y) :
    IsStrongReductionPair f Lim K H := by
  intro p x hpx hdom
  obtain ⟨z, hz, hzdom, hpost⟩ := h p x hpx hdom
  refine ⟨z, hz, z, baireRep_names_iff.mpr rfl, hzdom, ?_⟩
  intro a y' hay' hacc
  obtain rfl : y' = a := baireRep_names_iff.mp hay'
  exact hpost y' hacc

/-- **The stabilization-table compiler**, propositionally: a problem whose instances can
uniformly build an eventually-constant table and decode its limit stream reduces
strongly to `Lim`. -/
theorem stabilizationTable_le_lim {f : Problem X Y} {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ z ∈ K.evalStream p, Lim.Dom z ∧
        ∀ q : Baire, Lim.accepts z q →
          ∃ r ∈ H.evalStream q, ∃ y, Y.rep.Names r y ∧ f.accepts x y) :
    f ≤sW Lim :=
  strongReduction_iff_exists_reductionPair.mpr ⟨K, H, isStrongReductionPair_lim_of_table h⟩

end ComputableAnalysis
