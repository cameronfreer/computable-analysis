/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Cantor
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Cantor measurable structure and cylinder masses

`Cantor = ℕ → Bool` carries mathlib's Pi measurable structure (discrete factors) — no new
`MeasurableSpace`/Borel instances are introduced. The word cylinders form a π-system of
measurable sets generating that σ-algebra (`generateFrom_cantorCylinders`).

`cylMass μ s` is the mass a probability measure gives the cylinder of the word `s`, as a
plain real (represented `[0,1]` values arrive with the metric layer and enter at unit 20).
It is normalized, nonnegative, at most one, and splits binarily
(`cylMass_split`); `IsConsistentCylinderMass` abstracts exactly these — normalization,
nonnegativity, binary splitting; boundedness is derived, never assumed — and
`cylMass_injective` shows cylinder masses determine the measure, by π-system uniqueness.
Existence (every consistent mass function arises) is unit 19.
-/

namespace ComputableAnalysis

open MeasureTheory

/-! ### Measurable structure -/

/-- The word cylinders of Cantor space, as a family of sets. -/
def cantorCylinders : Set (Set Cantor) := Set.range (cylinder : List Bool → Set Cantor)

/-- Word cylinders are measurable: finite intersections of coordinate constraints. -/
theorem measurableSet_cylinder (s : List Bool) : MeasurableSet (cylinder s : Set Cantor) := by
  rw [cylinder_eq_iInter]
  exact MeasurableSet.iInter fun i =>
    measurable_pi_apply i.1 (measurableSet_singleton s[i.1])

/-- The cylinders form a π-system: a nonempty intersection of two cylinders is the one
with the longer word (both are prefix constraints on a common member). -/
theorem isPiSystem_cantorCylinders : IsPiSystem cantorCylinders := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ ⟨x, hxs, hxt⟩
  rw [cylinder_eq_of_mem hxs, cylinder_eq_of_mem hxt]
  rcases le_total s.length t.length with h | h
  · rw [Set.inter_eq_right.mpr (PiNat.cylinder_anti x h)]
    exact ⟨streamTake x t.length, by rw [cylinder_streamTake]⟩
  · rw [Set.inter_eq_left.mpr (PiNat.cylinder_anti x h)]
    exact ⟨streamTake x s.length, by rw [cylinder_streamTake]⟩

/-- A coordinate constraint is a countable union of cylinders: fix any word for the
earlier coordinates and append the constrained value. -/
private theorem eval_preimage_singleton_eq_iUnion (i : ℕ) (b : Bool) :
    (fun p : Cantor => p i) ⁻¹' {b} =
      ⋃ (w : List Bool) (_ : w.length = i), (cylinder (w ++ [b]) : Set Cantor) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion]
  constructor
  · intro hpb
    refine ⟨streamTake p i, length_streamTake p i, ?_⟩
    have h := mem_cylinder_streamTake p (i + 1)
    rwa [streamTake_succ, hpb] at h
  · rintro ⟨w, hw, hpw⟩
    subst hw
    have h := hpw w.length (by simp)
    simpa using h

/-- The cylinders generate the Pi σ-algebra of Cantor space. -/
theorem generateFrom_cantorCylinders :
    MeasurableSpace.generateFrom cantorCylinders = (inferInstance : MeasurableSpace Cantor) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro _ ⟨s, rfl⟩
    exact measurableSet_cylinder s
  · refine iSup_le fun i => MeasurableSpace.le_def.mpr fun t ht => ?_
    obtain ⟨B, -, rfl⟩ := ht
    have hB : (fun p : Cantor => p i) ⁻¹' B = ⋃ b ∈ B, (fun p : Cantor => p i) ⁻¹' {b} := by
      rw [← Set.preimage_iUnion₂]
      congr
      exact (Set.biUnion_of_singleton B).symm
    rw [hB]
    refine MeasurableSet.biUnion B.to_countable fun b _ => ?_
    rw [eval_preimage_singleton_eq_iUnion i b]
    exact .iUnion fun w => .iUnion fun _ => .basic _ ⟨w ++ [b], rfl⟩

/-! ### Cylinder splitting -/

/-- Membership in an extended cylinder: the original constraint plus one more
coordinate. -/
theorem mem_cylinder_append_iff {s : List Bool} {b : Bool} {p : Cantor} :
    p ∈ (cylinder (s ++ [b]) : Set Cantor) ↔ p ∈ (cylinder s : Set Cantor) ∧ p s.length = b := by
  constructor
  · intro hp
    refine ⟨fun i hi => ?_, ?_⟩
    · have h := hp i (by simp; omega)
      rwa [List.getElem_append_left hi] at h
    · have h := hp s.length (by simp)
      simpa using h
  · rintro ⟨hps, hpb⟩ i hi
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp (by simpa using hi)) with h | h
    · rw [List.getElem_append_left h]
      exact hps i h
    · subst h
      simpa using hpb

/-- A cylinder splits as the disjoint union of its two one-bit extensions. -/
theorem cylinder_eq_union_append (s : List Bool) :
    (cylinder s : Set Cantor) = cylinder (s ++ [false]) ∪ cylinder (s ++ [true]) := by
  ext p
  simp only [Set.mem_union, mem_cylinder_append_iff]
  rcases hb : p s.length with _ | _
  · exact ⟨fun h => Or.inl ⟨h, rfl⟩, fun h => (h.elim And.left And.left)⟩
  · exact ⟨fun h => Or.inr ⟨h, rfl⟩, fun h => (h.elim And.left And.left)⟩

/-- The two one-bit extensions of a cylinder are disjoint. -/
theorem disjoint_cylinder_append (s : List Bool) :
    Disjoint (cylinder (s ++ [false]) : Set Cantor) (cylinder (s ++ [true])) := by
  rw [Set.disjoint_left]
  intro p hpf hpt
  have h1 := (mem_cylinder_append_iff.mp hpf).2
  have h2 := (mem_cylinder_append_iff.mp hpt).2
  simp [h1] at h2

/-! ### Cylinder masses -/

/-- The mass a probability measure gives the cylinder of the word `s`, as a plain real. -/
noncomputable def cylMass (μ : ProbabilityMeasure Cantor) (s : List Bool) : ℝ :=
  (μ.toMeasure (cylinder s)).toReal

/-- Normalization: the empty word names the whole space. -/
@[simp]
theorem cylMass_nil (μ : ProbabilityMeasure Cantor) : cylMass μ [] = 1 := by
  simp [cylMass]

theorem cylMass_nonneg (μ : ProbabilityMeasure Cantor) (s : List Bool) :
    0 ≤ cylMass μ s :=
  ENNReal.toReal_nonneg

theorem cylMass_le_one (μ : ProbabilityMeasure Cantor) (s : List Bool) :
    cylMass μ s ≤ 1 := by
  have h := prob_le_one (μ := μ.toMeasure) (s := cylinder s)
  simpa [cylMass] using ENNReal.toReal_mono ENNReal.one_ne_top h

/-- Binary consistency: a cylinder's mass is the sum of its one-bit extensions'. -/
theorem cylMass_split (μ : ProbabilityMeasure Cantor) (s : List Bool) :
    cylMass μ s = cylMass μ (s ++ [false]) + cylMass μ (s ++ [true]) := by
  rw [cylMass, cylinder_eq_union_append,
    measure_union (disjoint_cylinder_append s) (measurableSet_cylinder _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  rfl

/-- Abstract consistency of a cylinder-mass function: normalization, nonnegativity, and
binary splitting. Boundedness (`m s ≤ 1`) is derived, never assumed. -/
def IsConsistentCylinderMass (m : List Bool → ℝ) : Prop :=
  m [] = 1 ∧ (∀ s, 0 ≤ m s) ∧ ∀ s, m s = m (s ++ [false]) + m (s ++ [true])

/-- The cylinder masses of a probability measure are consistent. -/
theorem cylMass_isConsistent (μ : ProbabilityMeasure Cantor) :
    IsConsistentCylinderMass (cylMass μ) :=
  ⟨cylMass_nil μ, cylMass_nonneg μ, cylMass_split μ⟩

namespace IsConsistentCylinderMass

variable {m : List Bool → ℝ}

/-- Extending a word by one bit cannot increase a consistent mass. -/
theorem append_le (hm : IsConsistentCylinderMass m) (s : List Bool) (b : Bool) :
    m (s ++ [b]) ≤ m s := by
  obtain ⟨-, hpos, hsplit⟩ := hm
  have h := hsplit s
  cases b
  · linarith [hpos (s ++ [true])]
  · linarith [hpos (s ++ [false])]

/-- Prefix monotonicity: a consistent mass is antitone along word extension. -/
theorem le_of_prefix (hm : IsConsistentCylinderMass m) {s t : List Bool}
    (h : s <+: t) : m t ≤ m s := by
  obtain ⟨r, rfl⟩ := h
  induction r using List.reverseRecOn with
  | nil => rw [List.append_nil]
  | append_singleton r b ih =>
    rw [← List.append_assoc]
    exact (hm.append_le (s ++ r) b).trans ih

/-- A consistent mass is bounded by one — derived from normalization, never assumed. -/
theorem le_one (hm : IsConsistentCylinderMass m) (s : List Bool) : m s ≤ 1 :=
  hm.1 ▸ hm.le_of_prefix s.nil_prefix

end IsConsistentCylinderMass

/-- **Uniqueness.** Cylinder masses determine the probability measure: the cylinders are
a generating π-system, and both measures are finite. Existence is unit 19. -/
theorem cylMass_injective : Function.Injective cylMass := by
  intro μ ν h
  refine ProbabilityMeasure.toMeasure_injective ?_
  refine Measure.ext_of_generateFrom_of_iUnion cantorCylinders (fun _ => Set.univ)
    generateFrom_cantorCylinders.symm isPiSystem_cantorCylinders
    (Set.iUnion_const Set.univ)
    (fun _ => ⟨[], cylinder_nil⟩) (fun _ => measure_ne_top _ _) ?_
  rintro _ ⟨s, rfl⟩
  have hs := congrFun h s
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hs

end ComputableAnalysis
