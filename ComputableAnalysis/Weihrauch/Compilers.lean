/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Parallelize
import ComputableAnalysis.Weihrauch.Principles.Limit
import ComputableAnalysis.Weihrauch.Principles.LLPO

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

* `isStrongReductionPair_parallelize_llpo_of_flags`: to reduce to parallelized `LLPO`, it
  suffices to produce a coded family of `LLPO` instances and to decode every stream of
  accepted answers. `LLPO`'s at-most-one promise is the obligation such a reduction owes,
  and `firstOccurrenceFlags` is one general way to discharge it — kept as a separate
  layer, since flagging first occurrences is not part of every `LLPO` reduction.

Each comes with a propositional corollary (`sigma1Family_le_parallelize_lpo`,
`stabilizationTable_le_lim`, `flagFamily_le_parallelize_llpo`). The composite entry point
sending Σ₁ question families
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
  · refine Problem.parallelize_dom_iff.mpr fun j => ?_
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

/-! ### Parallelized `LLPO`

`LLPO`'s at-most-one-nonzero promise is the obligation a reduction into it must discharge.
One general way to discharge it — not the only one, so it is kept as a separate layer —
is to flag only the **first occurrence** of each of two mutually exclusive families of
events. `firstOccurrenceFlags` builds such an instance and
`firstOccurrenceFlags_atMostOne` discharges the promise from incompatibility alone. -/

open Classical in
/-- The first-occurrence flags of a two-sided event family: coordinate `2n` (resp. `2n+1`)
is `1` exactly when `n` is the least level at which the `false` (resp. `true`) event
occurs. -/
noncomputable def firstOccurrenceFlags (E : Bool → ℕ → Prop) : Baire := fun k =>
  if E (decide (k % 2 = 1)) (k / 2) ∧ ∀ m < k / 2, ¬ E (decide (k % 2 = 1)) m then 1 else 0

theorem firstOccurrenceFlags_ne_zero {E : Bool → ℕ → Prop} {k : ℕ}
    (h : firstOccurrenceFlags E k ≠ 0) :
    E (decide (k % 2 = 1)) (k / 2) ∧ ∀ m < k / 2, ¬ E (decide (k % 2 = 1)) m := by
  by_contra hc
  exact h (ite_eq_right hc)

/-- **The promise, from incompatibility alone.** If the two sides of the family never both
occur — at any pair of levels — then flagging first occurrences yields an at-most-one
instance. Within a side the flag is unique because first occurrences are; across sides it
is unique by incompatibility. -/
theorem firstOccurrenceFlags_atMostOne {E : Bool → ℕ → Prop}
    (hincompat : ∀ n m, E false n → E true m → False) :
    ∀ a b : ℕ, firstOccurrenceFlags E a ≠ 0 → firstOccurrenceFlags E b ≠ 0 → a = b := by
  intro a b ha hb
  obtain ⟨hea, hmina⟩ := firstOccurrenceFlags_ne_zero ha
  obtain ⟨heb, hminb⟩ := firstOccurrenceFlags_ne_zero hb
  have hpar : a % 2 = b % 2 := by
    by_contra hne
    rcases Nat.mod_two_eq_zero_or_one a with h | h
    · have hb1 : b % 2 = 1 := by omega
      rw [h] at hea; rw [hb1] at heb
      exact hincompat _ _ (by simpa using hea) (by simpa using heb)
    · have hb0 : b % 2 = 0 := by omega
      rw [h] at hea; rw [hb0] at heb
      exact hincompat _ _ (by simpa using heb) (by simpa using hea)
  have hdiv : a / 2 = b / 2 := by
    rcases Nat.lt_trichotomy (a / 2) (b / 2) with h | h | h
    · exact absurd (hpar ▸ hea) (hminb _ h)
    · exact h
    · exact absurd (hpar ▸ heb) (hmina _ h)
  omega

/-- A vanishing track of the flags means that side's events never occur: the least
occurrence would have been flagged. -/
theorem not_event_of_track_zero {E : Bool → ℕ → Prop} {b : Bool}
    (hall : ∀ n, firstOccurrenceFlags E (2 * n + if b then 1 else 0) = 0) :
    ∀ n, ¬ E b n := by
  classical
  intro n hev
  have hex : ∃ n, E b n := ⟨n, hev⟩
  have hfind := Nat.find_spec hex
  have hmin : ∀ m < Nat.find hex, ¬ E b m := fun m hm => Nat.find_min hex hm
  set k := 2 * Nat.find hex + (if b then 1 else 0) with hk
  have hkdiv : k / 2 = Nat.find hex := by
    rw [hk]; cases b
    · simp
    · simp only [ite_true]
      omega
  have hkmod : (decide (k % 2 = 1)) = b := by rw [hk]; cases b <;> simp
  have hone : firstOccurrenceFlags E k = 1 := by
    rw [firstOccurrenceFlags, ite_eq_left]
    rw [hkdiv, hkmod]
    exact ⟨hfind, hmin⟩
  rw [hall (Nat.find hex)] at hone
  exact absurd hone (by omega)

/-- An at-most-one instance always has an accepted answer, so it lies in `LLPO`'s
domain. -/
theorem llpo_dom_of_atMostOne {g : Baire}
    (hone : ∀ a b : ℕ, g a ≠ 0 → g b ≠ 0 → a = b) : LLPO.Dom g := by
  classical
  by_cases hev : ∀ n, g (2 * n) = 0
  · exact ⟨(0 : ℕ), LLPO.accepts_iff.mpr ⟨hone, Or.inl ⟨rfl, hev⟩⟩⟩
  · obtain ⟨n₀, hn₀⟩ := not_forall.mp hev
    refine ⟨(1 : ℕ), LLPO.accepts_iff.mpr ⟨hone, Or.inr ⟨rfl, fun n => ?_⟩⟩⟩
    by_contra hne
    have := hone (2 * n₀) (2 * n + 1) hn₀ hne
    omega

/-- **The `LLPO.parallelize` compiler.** To exhibit `(K, H)` as a strong pair into
parallelized `LLPO`, it suffices that on every valid input name `K` produces the packing
of a family of `LLPO` instances and `H` decodes every stream of accepted answers. The
countable-product names, the `natRep` bit decoding, and the domain bookkeeping are
discharged here. -/
theorem isStrongReductionPair_parallelize_llpo_of_flags {f : Problem X Y} {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ fam : ℕ → Baire, Baire.packTracks fam ∈ K.evalStream p ∧ (∀ j, LLPO.Dom (fam j)) ∧
        ∀ a : Baire, (∀ j, LLPO.accepts (fam j) (a (Nat.pair j 0))) →
          ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y) :
    IsStrongReductionPair f LLPO.parallelize K H := by
  intro p x hpx hdom
  obtain ⟨fam, hmem, hfamdom, hpost⟩ := h p x hpx hdom
  refine ⟨_, hmem, fam, ?_, Problem.parallelize_dom_iff.mpr hfamdom, ?_⟩
  · exact Representation.sequence_names_packTracks_iff.mpr fun j => baireRep_names_iff.mpr rfl
  · intro a ys hays hacc
    have hbit : ∀ j, ys j = a (Nat.pair j 0) := natSequence_names_iff.mp hays
    exact hpost a fun j => hbit j ▸ Problem.parallelize_accepts_iff.mp hacc j

/-- **The flag-family compiler**, propositionally: a problem whose instances can uniformly
pose a coded family of `LLPO` questions and decode any stream of accepted answers reduces
strongly to parallelized `LLPO`. -/
theorem flagFamily_le_parallelize_llpo {f : Problem X Y} {K H : OracleCode}
    (h : ∀ p x, X.rep.Names p x → f.Dom x →
      ∃ fam : ℕ → Baire, Baire.packTracks fam ∈ K.evalStream p ∧ (∀ j, LLPO.Dom (fam j)) ∧
        ∀ a : Baire, (∀ j, LLPO.accepts (fam j) (a (Nat.pair j 0))) →
          ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y) :
    f ≤sW LLPO.parallelize :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨K, H, isStrongReductionPair_parallelize_llpo_of_flags h⟩

end ComputableAnalysis
