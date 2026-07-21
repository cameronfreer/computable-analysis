/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.Admissibility
import ComputableAnalysis.Measure.WeakRepresentation
import Mathlib.Probability.Kernel.Basic

/-!
# Continuous Markov kernels and their represented-side bridges

The carrier `ContinuousMarkovKernel X Y` of weakly continuous Markov kernels (unit 30),
law-first, bundling ALL THREE facets as data:

* `law : X → ProbabilityMeasure Y` — the kernel as a map into probability measures,
  carrying Markov as data (the subtype component);
* `continuous_law` — weak continuity of the law;
* `measurable_toMeasure` — Giry measurability, the `ProbabilityTheory.Kernel` field.

**Bundle rationale (mathlib survey at this pin).**  `ProbabilityTheory.Kernel X Y`
demands measurability of `x ↦ κ x` for the Giry measurable space on `Measure Y`
(`⨆ (s) (_ : MeasurableSet s), (borel ℝ≥0∞).comap fun μ => μ s`), while
`ProbabilityMeasure Y` carries the weak topology induced from `FiniteMeasure` (needing
`[OpensMeasurableSpace Y]`).  NOTHING at this pin connects the two: there is no
`OpensMeasurableSpace (ProbabilityMeasure Y)` or `BorelSpace (ProbabilityMeasure Y)`
instance, no lemma identifying the Giry σ-algebra with the Borel σ-algebra of the weak
topology, and no construction of a `Kernel` from a weakly continuous
`X → ProbabilityMeasure Y`.  Hence none of the three facets is derived from another:
`toKernel` and its `IsMarkovKernel` instance are rfl-level repackagings of the bundled
data, and `ofRealizableFun` takes BOTH continuity and measurability as supplied
hypotheses — measurability is never derived.

**Bridges.**  `advisedRealizable`: between presented spaces, the law of a continuous
Markov kernel is advice-realizable into the generic weak measure representation
(unit 27) — only the continuity facet is consumed, through unit 29's
`continuous_advisedRealizable` applied to the effective Prokhorov presentation; the
advice is classical, so this carries no computable-point claim.  `toRealizableFun` and
`ofRealizableFun` package the two directions between the carrier and the represented
measure function space.  Quarantine rule: the `LevyProkhorov` synonym appears in no
public statement; the names-level transport to unit 27's `prokhorovPresentation` is
re-proved privately here (unit 27 keeps its own synonym bridge private).
-/

namespace ComputableAnalysis

open MeasureTheory ProbabilityTheory

/-! ### The continuous-kernel carrier -/

section Carrier

variable (X Y : Type*) [MeasurableSpace X] [TopologicalSpace X]
  [MeasurableSpace Y] [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- **The continuous Markov kernel carrier** (law-first).  All three facets are present
as data: `law` lands in `ProbabilityMeasure Y` (Markov, as the subtype component),
`continuous_law` is weak continuity, and `measurable_toMeasure` is Giry (Kernel)
measurability as an EXPLICIT field — at this mathlib pin nothing connects weak
continuity to Giry measurability, so no facet is derivable from the others (see the
module docstring).

The instance context needs `[OpensMeasurableSpace Y]` beyond the four measurable /
topological instances, because the weak topology on `ProbabilityMeasure Y` itself
requires it. -/
structure ContinuousMarkovKernel where
  /-- The kernel as a map into probability measures (Markov is data here). -/
  law : X → ProbabilityMeasure Y
  /-- Weak continuity of the law. -/
  continuous_law : Continuous law
  /-- Giry measurability of the law — the `ProbabilityTheory.Kernel` field.  A
  hypothesis bundled as data, never derived from `continuous_law` (no such derivation
  exists at this mathlib pin). -/
  measurable_toMeasure : Measurable fun x => (law x).toMeasure

variable {X Y}

/-- The bundled `ProbabilityTheory.Kernel` — an rfl-level repackaging of the `law` and
`measurable_toMeasure` fields. -/
def ContinuousMarkovKernel.toKernel (κ : ContinuousMarkovKernel X Y) : Kernel X Y :=
  ⟨fun x => (κ.law x).toMeasure, κ.measurable_toMeasure⟩

/-- The bundled kernel evaluates to the law's underlying measure (rfl-level). -/
@[simp]
theorem ContinuousMarkovKernel.toKernel_apply (κ : ContinuousMarkovKernel X Y) (x : X) :
    κ.toKernel x = (κ.law x).toMeasure := rfl

/-- The bundled kernel is Markov — an rfl-level repackaging of the subtype component of
`law` (not derived from measurability or continuity). -/
instance ContinuousMarkovKernel.isMarkov (κ : ContinuousMarkovKernel X Y) :
    IsMarkovKernel κ.toKernel :=
  ⟨fun x => (κ.law x).prop⟩

end Carrier

/-! ### The represented-side bridges -/

section Bridge

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y)

/-- Weak names are exactly fast-Cauchy `NamesPoint` on the Lévy–Prokhorov synonym, for
any presentation of the synonym whose dense sequence is `ofMeasure ∘ atomic Q`.  The
names-level transport is re-proved here privately because unit 27 keeps its synonym
bridge private (quarantine rule: `LevyProkhorov` appears in no public statement). -/
private theorem weakMeasureNames_iff_namesPoint
    (Q' : ComputableMetricPresentation (LevyProkhorov (ProbabilityMeasure Y)))
    (hd : ∀ m, Q'.dense m = LevyProkhorov.ofMeasure (atomic Q m))
    {p : Baire} {μ : ProbabilityMeasure Y} :
    WeakMeasureNames Q p μ ↔ Q'.NamesPoint p (LevyProkhorov.ofMeasure μ) := by
  unfold WeakMeasureNames ComputableMetricPresentation.NamesPoint
  refine forall_congr' fun n => ?_
  rw [hd, LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist_comm]

/-- The names-level identification of `weakMeasureRep Q` with the fast Cauchy
representation of any Prokhorov-type presentation of the synonym. -/
private theorem weakMeasureRep_names_iff_cauchyRep
    (Q' : ComputableMetricPresentation (LevyProkhorov (ProbabilityMeasure Y)))
    (hd : ∀ m, Q'.dense m = LevyProkhorov.ofMeasure (atomic Q m))
    {p : Baire} {μ : ProbabilityMeasure Y} :
    (weakMeasureRep Q).Names p μ ↔ Q'.cauchyRep.Names p (LevyProkhorov.ofMeasure μ) := by
  rw [weakMeasureRep_names_iff, Q'.cauchyRep_names_iff,
    weakMeasureNames_iff_namesPoint Q Q' hd]

/-- **The law of a continuous Markov kernel between presented spaces is
advice-realizable** into the generic weak measure representation.  The honest
composition: `κ.law` is weakly continuous; separability of `Y` (derived from `Q`'s
dense sequence) makes the weak topology the Lévy–Prokhorov metric topology
(`LevyProkhorov.continuous_ofMeasure_probabilityMeasure`); unit 29's
`continuous_advisedRealizable` realizes the resulting continuous map into the
effective Prokhorov presentation of the synonym (unit 27), whose dense sequence is
the decoded atomics definitionally; and the private names-level transport carries the
realizer to `weakMeasureRep Q`.  Only `κ.continuous_law` is consumed — the
measurability facet plays no role on the represented side, which is exactly why the
carrier must bundle it.  The advice is classical (a certificate table), so this
carries no computable-point claim. -/
theorem ContinuousMarkovKernel.advisedRealizable (κ : ContinuousMarkovKernel X Y) :
    ∃ c q, AdvisedRealizes P.cauchyRep (weakMeasureRep Q) c q κ.law := by
  haveI : TopologicalSpace.SeparableSpace Y :=
    ⟨⟨Set.range Q.dense, Set.countable_range _, Q.denseRange⟩⟩
  have hg : Continuous fun x =>
      (LevyProkhorov.ofMeasure (κ.law x) : LevyProkhorov (ProbabilityMeasure Y)) :=
    LevyProkhorov.continuous_ofMeasure_probabilityMeasure.comp κ.continuous_law
  obtain ⟨c, q, hcq⟩ := continuous_advisedRealizable P (prokhorovPresentation Q) hg
  refine ⟨c, q, fun p x hp => ?_⟩
  obtain ⟨r, hr, hname⟩ := hcq p x hp
  exact ⟨r, hr, (weakMeasureRep_names_iff_cauchyRep Q (prokhorovPresentation Q)
    fun _ => rfl).mpr hname⟩

/-- A continuous Markov kernel as a point of the represented measure function space:
its law bundled with the advice-realizability certificate of `advisedRealizable`. -/
noncomputable def ContinuousMarkovKernel.toRealizableFun
    (κ : ContinuousMarkovKernel X Y) : RealizableFun P.cauchyRep (weakMeasureRep Q) :=
  ⟨κ.law, κ.advisedRealizable P Q⟩

/-- From a point of the represented measure function space together with the two facet
HYPOTHESES — weak continuity and Giry measurability — a `ContinuousMarkovKernel`.
Purely definitional packaging: measurability is always a supplied hypothesis, never
derived from continuity or from realizability (no such derivation exists at this
mathlib pin). -/
def ContinuousMarkovKernel.ofRealizableFun
    (f : RealizableFun P.cauchyRep (weakMeasureRep Q)) (hc : Continuous f.toFun)
    (hm : Measurable fun x => (f.toFun x).toMeasure) : ContinuousMarkovKernel X Y where
  law := f.toFun
  continuous_law := hc
  measurable_toMeasure := hm

/-- The law of the repackaged kernel is the underlying function (rfl-level). -/
@[simp]
theorem ContinuousMarkovKernel.law_ofRealizableFun
    (f : RealizableFun P.cauchyRep (weakMeasureRep Q)) (hc : Continuous f.toFun)
    (hm : Measurable fun x => (f.toFun x).toMeasure) :
    (ContinuousMarkovKernel.ofRealizableFun P Q f hc hm).law = f.toFun := rfl

/-- The bundled kernel of the repackaged kernel evaluates to the underlying function's
measure (rfl-level). -/
@[simp]
theorem ContinuousMarkovKernel.toKernel_ofRealizableFun
    (f : RealizableFun P.cauchyRep (weakMeasureRep Q)) (hc : Continuous f.toFun)
    (hm : Measurable fun x => (f.toFun x).toMeasure) (x : X) :
    (ContinuousMarkovKernel.ofRealizableFun P Q f hc hm).toKernel x =
      (f.toFun x).toMeasure := rfl

end Bridge

end ComputableAnalysis
