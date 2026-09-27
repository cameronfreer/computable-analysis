/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.ContinuityOpenRestriction
import ComputableAnalysis.Measure.Marginals
import ComputableAnalysis.TypeTwo.Tracks
import ComputableAnalysis.Weihrauch.Problem

/-!
# The Vitali-limit conditional

Ackerman–Freer–Roy's conditional of a *fixed* joint law along a class of conditioning sets
(*On computability and disintegration*, §5, after Fraser–Naderi). For a joint law `μ` on
`X × Y` and a class `V` of subsets of `X`, the Vitali limit at `x` is the weak limit of the
conditionals of `μ` given `E n`, along every admissible sequence `E`. A sequence is admissible
when its members lie in `V`, are measurable, have positive first-marginal mass, and converge
regularly to `x`.

`VitaliDisintegrate P Q μ V` is the represented problem: input a Cauchy name of a point, output a
weak name of the limit there. The input is a point and the joint law is a fixed parameter, so
this is not an operator on measures. The problem is single-valued (`isVitaliLimit_unique`) and
partial: its domain is the set of points where the limit exists. No everywhere-definedness is
claimed.

There is no almost-everywhere quotient: at each point the output is one specific measure, and
other versions of the same disintegration can differ from it. This module does not establish
that the Vitali limit is a version of the disintegration. The Vitali covering property, which
the paper uses for that, plays no role here.

`IsVitaliWitness` is the effective half of the paper's strong Vitali covering property: a code
turning names of points into effective continuity opens, each inner to and of equal mass with
the terms of an admissible sequence. `condSnd_eq_of_subset_of_measure_eq` is why that suffices:
an inner set of equal marginal mass has the same conditional.

## Main definitions and results

* `ConvergesRegularly`, `AdmissibleSeq` — regular convergence with a positive finite constant,
  and the admissible conditioning sequences.
* `condSnd` — the conditional law on `Y` given that the first coordinate lies in a set.
* `IsVitaliLimit`, `isVitaliLimit_unique` — the Vitali limit and its uniqueness.
* `VitaliDisintegrate` — the problem.
* `IsVitaliWitness` — the effective witness.
* `condSnd_eq_of_subset_of_measure_eq` — null enlargement.

## Implementation notes

Convergence is weak convergence in `ProbabilityMeasure Y`, the topology the output
representation names. The paper instead takes setwise limits for each Borel set. Positivity is
part of admissibility rather than a conclusion about every regularly converging sequence: a
constant null singleton in `V` converges regularly, and must not exclude a point whose
positive-mass approximations have a limit.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ComputableAnalysis

section Definitions

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- `E` converges regularly to `x` with respect to `ν`, with a positive finite regularity
constant. The covering closed balls need not be centred at `x`. -/
def ConvergesRegularly (ν : Measure X) (E : ℕ → Set X) (x : X) : Prop :=
  ∃ c : ℕ → X, ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝 0) ∧ ∃ α : ℝ≥0, 0 < α ∧
    ∀ n, x ∈ E n ∧ E n ⊆ closedBall (c n) (r n) ∧
      (α : ℝ≥0∞) * ν (closedBall (c n) (r n)) ≤ ν (E n)

/-- An admissible conditioning sequence at `x`: members of `V`, measurable, of positive marginal
mass, converging regularly to `x`. -/
def AdmissibleSeq (μX : ProbabilityMeasure X) (V : Set (Set X)) (x : X) (E : ℕ → Set X) :
    Prop :=
  (∀ n, E n ∈ V ∧ MeasurableSet (E n) ∧ μX.toMeasure (E n) ≠ 0) ∧
    ConvergesRegularly μX.toMeasure E x

/-- The conditional of `μ` given that the first coordinate lies in `E`, as a law on `Y`. -/
noncomputable def condSnd (μ : ProbabilityMeasure (X × Y)) (E : Set X) : Measure Y :=
  (normalizedRestriction μ (E ×ˢ Set.univ)).map Prod.snd

/-- `ν` is the Vitali limit of `μ` at `x` along `V`: an admissible sequence exists, and along
every admissible sequence the conditionals converge weakly to `ν`. -/
structure IsVitaliLimit (μ : ProbabilityMeasure (X × Y)) (V : Set (Set X)) (x : X)
    (ν : ProbabilityMeasure Y) : Prop where
  exists_admissible : ∃ E, AdmissibleSeq (fstMarginal μ) V x E
  tendsto : ∀ E, AdmissibleSeq (fstMarginal μ) V x E →
    ∃ σ : ℕ → ProbabilityMeasure Y, (∀ n, (σ n).toMeasure = condSnd μ (E n)) ∧
      Tendsto σ atTop (𝓝 ν)

omit [BorelSpace X] in
/-- **Uniqueness**: the Vitali limit is single-valued. -/
theorem isVitaliLimit_unique {μ : ProbabilityMeasure (X × Y)} {V : Set (Set X)} {x : X}
    {ν ν' : ProbabilityMeasure Y} (h : IsVitaliLimit μ V x ν) (h' : IsVitaliLimit μ V x ν') :
    ν = ν' := by
  obtain ⟨E, hE⟩ := h.exists_admissible
  obtain ⟨σ, hσ, hlim⟩ := h.tendsto E hE
  obtain ⟨σ', hσ', hlim'⟩ := h'.tendsto E hE
  have hsame : σ = σ' := funext fun n => Subtype.ext ((hσ n).trans (hσ' n).symm)
  subst hsame
  exact tendsto_nhds_unique hlim hlim'

variable (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y)

/-- **The Vitali-limit conditional problem** (the paper's Def. 5.3, in partial form): input a
point, output the Vitali limit there. -/
noncomputable def VitaliDisintegrate (μ : ProbabilityMeasure (X × Y)) (V : Set (Set X)) :
    Problem ⟨X, P.cauchyRep⟩ ⟨ProbabilityMeasure Y, weakMeasureRep Q⟩ :=
  ⟨fun x ν => IsVitaliLimit μ V x ν⟩

/-- **The effective Vitali witness** (the paper's Def. 5.1(2)). On names of points that have
an admissible sequence, `W` emits packed effective continuity opens, inner to and of equal mass
with some admissible sequence. Nothing is required at other points. -/
def IsVitaliWitness (μX : ProbabilityMeasure X) (V : Set (Set X)) (W : OracleCode) : Prop :=
  ∀ p x, P.cauchyRep.Names p x → (∃ E, AdmissibleSeq μX V x E) →
    ∃ s ∈ W.evalStream p, ∃ E, AdmissibleSeq μX V x E ∧ ∀ n,
      ContinuityOpenNames P μX (Baire.track n s) ∧
      openOf P (Baire.track n s).evenPart ⊆ E n ∧
      μX.toMeasure (openOf P (Baire.track n s).evenPart) = μX.toMeasure (E n)

end Definitions

/-! ### Null enlargement -/

section NullEnlargement

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]

/-- The first-marginal mass of `U` is the joint mass of the cylinder `U × univ`. -/
private theorem fstMarginal_apply_eq {μ : ProbabilityMeasure (X × Y)} {U : Set X}
    (hU : MeasurableSet U) :
    (fstMarginal μ).toMeasure U = μ.toMeasure (U ×ˢ Set.univ) := by
  rw [fstMarginal_toMeasure, Measure.fst_apply hU, ← Set.prod_univ]

/-- **Null enlargement.** An inner set of equal marginal mass has the same conditional. -/
theorem condSnd_eq_of_subset_of_measure_eq {μ : ProbabilityMeasure (X × Y)} {U E : Set X}
    (hU : MeasurableSet U) (hUE : U ⊆ E)
    (hmass : (fstMarginal μ).toMeasure U = (fstMarginal μ).toMeasure E) (hE : MeasurableSet E) :
    condSnd μ U = condSnd μ E := by
  have hUc : μ.toMeasure (U ×ˢ Set.univ) = μ.toMeasure (E ×ˢ Set.univ) := by
    rw [← fstMarginal_apply_eq hU, ← fstMarginal_apply_eq hE, hmass]
  have hae : (U ×ˢ (Set.univ : Set Y) : Set (X × Y)) =ᵐ[μ.toMeasure] E ×ˢ Set.univ :=
    ae_eq_of_subset_of_measure_ge (Set.prod_mono hUE le_rfl) hUc.ge
      (hU.prod MeasurableSet.univ).nullMeasurableSet (measure_ne_top _ _)
  rw [condSnd, condSnd, normalizedRestriction, normalizedRestriction, hUc,
    Measure.restrict_congr_set hae]

end NullEnlargement

end ComputableAnalysis
