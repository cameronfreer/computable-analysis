/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Principles.MetricLimit
import ComputableAnalysis.Measure.WeakRepresentation

/-!
# Weak limits of named probability measures reduce to `Lim`

The measure-facing form of `exists_limitDecoder`. From the `Lim` answer alone, one fixed code
decodes a weak name of the weak limit of a convergent sequence of weakly named probability
measures, with convergence meaning `Tendsto` in `ProbabilityMeasure Y`.

The proof runs the generic decoder over the Prokhorov presentation. The identification of weak
names with Cauchy names on the `LevyProkhorov` synonym is private to this file, so nothing on
the synonym is exported. Separability, which makes the Lévy–Prokhorov topology agree with the
weak topology, follows from the presentation.

## Main results

* `exists_weakLimitDecoder` — the answer-only weak-limit decoder.
-/

open MeasureTheory Filter Topology

namespace ComputableAnalysis

section Measures

variable {Y : Type} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Weak names are fast Cauchy names over the Prokhorov presentation. The synonym appears only
inside this proof-local bridge. -/
private theorem weakMeasureNames_iff_prokhorov (Q : ComputableMetricPresentation Y) (p : Baire)
    (μ : ProbabilityMeasure Y) :
    WeakMeasureNames Q p μ ↔
      (prokhorovPresentation Q).NamesPoint p (LevyProkhorov.ofMeasure μ) := by
  unfold WeakMeasureNames ComputableMetricPresentation.NamesPoint
  refine forall_congr' fun n => ?_
  rw [show (prokhorovPresentation Q).dense (p n) = LevyProkhorov.ofMeasure (atomic Q (p n)) from
    rfl, LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist_comm]

/-- **The weak-limit decoder.** From the `Lim` answer alone, one fixed code decodes a weak name
of the weak limit of a convergent sequence of weakly named probability measures. -/
theorem exists_weakLimitDecoder (Q : ComputableMetricPresentation Y) :
    ∃ H : OracleCode, ∀ (w a : Baire) (ν : ℕ → ProbabilityMeasure Y)
        (νlim : ProbabilityMeasure Y),
      (∀ n, WeakMeasureNames Q (Baire.track n w) (ν n)) →
      Tendsto ν atTop (𝓝 νlim) →
      Lim.accepts (limTable w) a →
      ∃ r ∈ H.evalStream a, WeakMeasureNames Q r νlim := by
  have := Q.separableSpace
  obtain ⟨H, hH⟩ := exists_limitDecoder (prokhorovPresentation Q)
  refine ⟨H, fun w a ν νlim hν hlim hacc => ?_⟩
  have htend : Tendsto (fun n => LevyProkhorov.ofMeasure (ν n)) atTop
      (𝓝 (LevyProkhorov.ofMeasure νlim)) :=
    (LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto νlim).comp hlim
  obtain ⟨r, hr, hname⟩ := hH w a _ _
    (fun n => (weakMeasureNames_iff_prokhorov Q _ _).mp (hν n)) htend hacc
  exact ⟨r, hr, (weakMeasureNames_iff_prokhorov Q _ _).mpr hname⟩

end Measures

end ComputableAnalysis
