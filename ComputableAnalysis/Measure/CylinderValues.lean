/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.CantorRepresentation

/-!
# Uniform cylinder-value characterization of computable measures

A probability measure on Cantor space is a computable point of `cantorMeasureRep` exactly
when **one** first-order computable procedure uniformly produces the `[0,1]`-names of all
its cylinder masses from the encoded word: the packing of unit 20 makes the measure name
and the uniform procedure interconvertible through `Nat.pair`/`Nat.unpair`.
-/

open MeasureTheory

namespace ComputableAnalysis

/-- **Uniform cylinder-value equivalence.** A measure is a computable point iff a single
first-order computable procedure produces, from the encoded word, all coordinates of a
`unitIntervalRep` name of its mass. -/
theorem computablePoint_cantorMeasureRep_iff {μ : ProbabilityMeasure Cantor} :
    cantorMeasureRep.ComputablePoint μ ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ ∀ s : List Bool,
        unitIntervalRep.Names (f (Encodable.encode s)) (cylMass01 μ s) := by
  constructor
  · rintro ⟨F, hF, hFμ⟩
    have hM : MeasureNames F μ := cantorMeasureRep_names_iff.mp hFμ
    exact ⟨fun e n => F (Nat.pair e n), hF.comp Primrec₂.natPair.to_comp,
      fun s => hM s⟩
  · rintro ⟨f, hf, hnames⟩
    refine ⟨fun m => f m.unpair.1 m.unpair.2,
      hf.comp (Primrec.fst.comp Primrec.unpair).to_comp
        (Primrec.snd.comp Primrec.unpair).to_comp, ?_⟩
    refine cantorMeasureRep_names_iff.mpr fun s => ?_
    have hcomp : (fun n =>
        (fun m => f m.unpair.1 m.unpair.2) (Nat.pair (Encodable.encode s) n))
        = f (Encodable.encode s) := by
      funext n
      simp only [Nat.unpair_pair]
    rw [hcomp]
    exact hnames s

end ComputableAnalysis
