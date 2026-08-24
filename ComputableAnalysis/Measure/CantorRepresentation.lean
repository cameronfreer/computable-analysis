/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.Real
import ComputableAnalysis.Measure.CylinderMass

/-!
# The Cantor computable-measure representation

A name of a probability measure on Cantor space carries, for every word `s`, a
`unitIntervalRep` name of the mass of `s` as the pinned component
`fun n => F (Nat.pair (Encodable.encode s) n)` (the `Primcodable (List Bool)` numbering).

The representation is partial with no default measure: a stream denotes nothing unless
*every* component names the corresponding mass of one single measure. It is single-valued
because component names are single-valued and cylinder masses determine the measure
(`cylMass_injective`), and onto by choosing a `unitIntervalRep` name per word.
-/

open MeasureTheory

namespace ComputableAnalysis

/-- The mass of a word, as a point of `[0,1]` (bounds from unit 18). -/
noncomputable def cylMass01 (μ : ProbabilityMeasure Cantor) (s : List Bool) :
    Set.Icc (0 : ℝ) 1 :=
  ⟨cylMass μ s, cylMass_nonneg μ s, cylMass_le_one μ s⟩

/-- `F` names `μ`: for every word `s`, the pinned component
`fun n => F (Nat.pair (Encodable.encode s) n)` is a `unitIntervalRep` name of the mass
of `s`. -/
def MeasureNames (F : Baire) (μ : ProbabilityMeasure Cantor) : Prop :=
  ∀ s : List Bool,
    unitIntervalRep.Names (fun n => F (Nat.pair (Encodable.encode s) n)) (cylMass01 μ s)

/-- A measure name determines its measure: component names are single-valued, and
cylinder masses determine the measure. -/
theorem measureNames_unique {F : Baire} {μ ν : ProbabilityMeasure Cantor}
    (hμ : MeasureNames F μ) (hν : MeasureNames F ν) : μ = ν := by
  apply cylMass_injective
  funext s
  have h : cylMass01 μ s = cylMass01 ν s := Representation.names_unique (hμ s) (hν s)
  exact congrArg (fun z : Set.Icc (0 : ℝ) 1 => (z : ℝ)) h

/-- The Cantor computable-measure representation: `F` is valid exactly when some (unique)
measure has all its masses named by the pinned components. No default measure: invalid
components, or components naming masses of no single measure, denote nothing. -/
noncomputable def cantorMeasureRep : Representation (ProbabilityMeasure Cantor) where
  rep F := ⟨∃ μ, MeasureNames F μ, fun h => h.choose⟩
  onto μ := by
    classical
    have h : ∀ s : List Bool, ∃ p : Baire, unitIntervalRep.Names p (cylMass01 μ s) :=
      fun s => unitIntervalRep.onto (cylMass01 μ s)
    set G : List Bool → Baire := fun s => (h s).choose with hG
    refine ⟨fun m => G ((Encodable.decode m.unpair.1).getD []) m.unpair.2, ?_⟩
    have hM : MeasureNames
        (fun m => G ((Encodable.decode m.unpair.1).getD []) m.unpair.2) μ := by
      intro s
      have hcomp : (fun n => G ((Encodable.decode
            (Nat.pair (Encodable.encode s) n).unpair.1).getD [])
            (Nat.pair (Encodable.encode s) n).unpair.2) = G s := by
        funext n
        rw [Nat.unpair_pair, Encodable.encodek]
      rw [hcomp]
      exact (h s).choose_spec
    exact ⟨⟨μ, hM⟩, measureNames_unique (Exists.choose_spec _) hM⟩

/-- Names of `cantorMeasureRep` are exactly `MeasureNames`. -/
@[simp]
theorem cantorMeasureRep_names_iff {F : Baire} {μ : ProbabilityMeasure Cantor} :
    cantorMeasureRep.Names F μ ↔ MeasureNames F μ := by
  constructor
  · rintro ⟨hex, rfl⟩
    exact hex.choose_spec
  · intro h
    exact ⟨⟨μ, h⟩, measureNames_unique (Exists.choose_spec _) h⟩

/-- Cantor probability measures as a represented space. -/
noncomputable def cantorMeasureSpace : RepSpace :=
  ⟨ProbabilityMeasure Cantor, cantorMeasureRep⟩

end ComputableAnalysis
