/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.Kernel
import ComputableAnalysis.Weihrauch.Problem
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.MeasureTheory.Measure.Support

/-!
# The conditioning layer: `Condition` and `Disintegrate` over presented factors

This library conditions **Y given X**: the disintegration is over the first marginal
`μ.fst`, matching mathlib's `MeasureTheory.Measure.IsCondKernel` orientation
`ρ.fst ⊗ₘ ρCond = ρ` exactly.

The binding distinction: **general conditional kernels** are measurable, versioned, and
identified a.e. (`IsCondKernel` through mathlib's `Measure.IsCondKernel`, with the
`CondKernelAEEq` version relation; never claimed continuous); **continuous
disintegrations** are the restricted `ContinuousMarkovKernel` carrier
(`continuousKernelSpace`, bridged by the exact `continuousKernelEquiv`).

Two problems, two output carriers, never conflated:

* `Condition`: input a joint law in `jointMeasureSpace`, output an advice-realizable map
  in `condFunSpace`, accepted iff it agrees with SOME version on a `μ.fst`-full set
  (a.e.-flexible; multivalued).
* `Disintegrate`: output a continuous-kernel point whose induced kernel disintegrates
  the input; the domain further demands full first-marginal support
  (`FullFirstMarginalSupport`), which makes the accepted output pointwise **unique**
  (`disintegrate_accepts_unique`) — a theorem, not a definition.

The product-Borel instance is DERIVED (`ComputableMetricPresentation.borelSpace_prod`),
never a hypothesis.
-/

namespace ComputableAnalysis

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

section Conditioning

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable (P : ComputableMetricPresentation X) (Q : ComputableMetricPresentation Y)

include P in
/-- The Borel structure of the presented product: second countability of the first
factor comes from its dense sequence, so `Prod.borelSpace` applies. Always derived,
never a hypothesis. -/
theorem ComputableMetricPresentation.borelSpace_prod : BorelSpace (X × Y) := by
  haveI := P.separableSpace
  haveI : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  exact Prod.borelSpace

/-! ### (a) The version relation, through mathlib's `Measure.IsCondKernel`

`MeasureTheory.Measure.IsCondKernel` is a class with the single field
`disintegrate : ρ.fst ⊗ₘ ρCond = ρ` for `ρ : Measure (α × Ω)` and `ρCond : Kernel α Ω` —
it conditions the SECOND coordinate on the FIRST, matching this library's Y-given-X
orientation with `(X, Y) = (α, Ω)` exactly. -/

/-- The version relation: `κ` is a Markov conditional kernel of the joint law `μ`
(through mathlib's `Measure.IsCondKernel`; orientation `fst ⊗ₘ κ = μ`). -/
def IsCondKernel (μ : ProbabilityMeasure (X × Y)) (κ : Kernel X Y) : Prop :=
  IsMarkovKernel κ ∧ μ.toMeasure.IsCondKernel κ

/-! ### (b) The a.e. convention -/

/-- Versions identified a.e. against the conditioning (first) marginal. -/
def CondKernelAEEq (μ : ProbabilityMeasure (X × Y)) (κ κ' : Kernel X Y) : Prop :=
  ∀ᵐ x ∂μ.toMeasure.fst, κ x = κ' x

namespace CondKernelAEEq

variable {μ : ProbabilityMeasure (X × Y)} {κ κ' κ'' : Kernel X Y}

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The a.e. version relation is reflexive. -/
protected theorem refl (μ : ProbabilityMeasure (X × Y)) (κ : Kernel X Y) :
    CondKernelAEEq μ κ κ :=
  Filter.Eventually.of_forall fun _ => rfl

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The a.e. version relation is symmetric. -/
protected theorem symm (h : CondKernelAEEq μ κ κ') : CondKernelAEEq μ κ' κ :=
  h.mono fun _ hx => hx.symm

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The a.e. version relation is transitive. -/
protected theorem trans (h : CondKernelAEEq μ κ κ') (h' : CondKernelAEEq μ κ' κ'') :
    CondKernelAEEq μ κ κ'' := by
  filter_upwards [h, h'] with x hx hx'
  rw [hx, hx']

end CondKernelAEEq

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- Any two Markov conditional kernels of one joint law agree a.e. against the first
marginal — exactly the hypotheses of mathlib's
`ProbabilityTheory.eq_condKernel_of_measure_eq_compProd` (Disintegration/Unique.lean),
routed through `Measure.condKernel` twice. -/
theorem isCondKernel_ae_unique [StandardBorelSpace Y] [Nonempty Y]
    {μ : ProbabilityMeasure (X × Y)} {κ κ' : Kernel X Y}
    (h : IsCondKernel μ κ) (h' : IsCondKernel μ κ') : CondKernelAEEq μ κ κ' := by
  haveI := h.1
  haveI := h'.1
  haveI := h.2
  haveI := h'.2
  have h1 := eq_condKernel_of_measure_eq_compProd κ (μ.toMeasure.disintegrate κ).symm
  have h2 := eq_condKernel_of_measure_eq_compProd κ' (μ.toMeasure.disintegrate κ').symm
  filter_upwards [h1, h2] with x hx hx'
  rw [hx, hx']

/-! ### (c) The joint-law input -/

/-- The joint-law input space: probability measures on the presented product, under the
weak measure representation. -/
noncomputable def jointMeasureSpace : RepSpace :=
  letI : BorelSpace (X × Y) := P.borelSpace_prod
  ⟨ProbabilityMeasure (X × Y), weakMeasureRep (P.prod Q)⟩

/-! ### (d) The output carriers — two, never conflated -/

/-- The GENERAL output carrier (parts A/B): advice-realizable maps into the weak
measure space. -/
noncomputable def condFunSpace : RepSpace :=
  ⟨RealizableFun P.cauchyRep (weakMeasureRep Q), funRep _ _⟩

/-- The general conditioning problem: an output is accepted iff it agrees with SOME
version on a `μ.fst`-full set. -/
noncomputable def Condition : Problem (jointMeasureSpace P Q) (condFunSpace P Q) :=
  ⟨fun μ f => ∃ κ : Kernel X Y, IsCondKernel μ κ ∧
    ∀ᵐ x ∂μ.toMeasure.fst, (f.toFun x).toMeasure = κ x⟩

/-- The CONTINUOUS output carrier (part C): realizable maps that are weakly continuous
and Giry measurable — the subtype whose bundled form is `ContinuousMarkovKernel`. -/
abbrev ContinuousKernelPoint :=
  {f : RealizableFun P.cauchyRep (weakMeasureRep Q) //
    Continuous f.toFun ∧ Measurable fun x => (f.toFun x).toMeasure}

/-- The continuous-kernel output space: the subtype representation over `funRep`. -/
noncomputable def continuousKernelSpace : RepSpace :=
  ⟨ContinuousKernelPoint P Q, (funRep _ _).subtype _⟩

variable {P Q}

/-- The kernel induced by a continuous-kernel point (Markov via
`isMarkovKernel_inducedKernel`). -/
def inducedKernel (f : ContinuousKernelPoint P Q) : Kernel X Y :=
  ⟨fun x => (f.val.toFun x).toMeasure, f.prop.2⟩

/-- The induced kernel of a continuous-kernel point is Markov: each value is a bundled
probability measure. -/
instance isMarkovKernel_inducedKernel (f : ContinuousKernelPoint P Q) :
    IsMarkovKernel (inducedKernel f) :=
  ⟨fun x => (f.val.toFun x).prop⟩

omit [BorelSpace X] in
/-- The induced kernel applies as the underlying map into unbundled measures. -/
@[simp]
theorem inducedKernel_apply (f : ContinuousKernelPoint P Q) (x : X) :
    inducedKernel f x = (f.val.toFun x).toMeasure := rfl

variable (P Q)

/-- The EXACT bridge between the continuous-kernel carrier and the bundled
`ContinuousMarkovKernel` — a named `Equiv`, not commentary. -/
noncomputable def continuousKernelEquiv :
    ContinuousKernelPoint P Q ≃ ContinuousMarkovKernel X Y where
  toFun f := ContinuousMarkovKernel.ofRealizableFun P Q f.val f.prop.1 f.prop.2
  invFun κ := ⟨κ.toRealizableFun P Q, κ.continuous_law, κ.measurable_toMeasure⟩
  left_inv _ := Subtype.ext (RealizableFun.ext fun _ => rfl)
  right_inv _ := rfl

/-! ### Part C's domain and the `Disintegrate` problem -/

/-- Full support of the conditioning (first) marginal (`Measure.support` is
`Mathlib/MeasureTheory/Measure/Support.lean`). -/
def FullFirstMarginalSupport (μ : ProbabilityMeasure (X × Y)) : Prop :=
  μ.toMeasure.fst.support = Set.univ

omit [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- Full first-marginal support makes the first marginal an open-positive measure. -/
theorem FullFirstMarginalSupport.isOpenPosMeasure {μ : ProbabilityMeasure (X × Y)}
    (h : FullFirstMarginalSupport μ) : μ.toMeasure.fst.IsOpenPosMeasure :=
  ⟨fun _U hU ⟨x, hx⟩ =>
    ((Measure.mem_support_iff_forall x).mp (Set.eq_univ_iff_forall.mp h x) _
      (hU.mem_nhds hx)).ne'⟩

/-- **The continuous disintegration problem** (part C): input a joint law on the
presented product, output a continuous-kernel point whose induced kernel disintegrates
it; the domain further demands full first-marginal support. -/
noncomputable def Disintegrate :
    Problem (jointMeasureSpace P Q) (continuousKernelSpace P Q) :=
  ⟨fun μ f => FullFirstMarginalSupport μ ∧ IsCondKernel μ (inducedKernel f)⟩

variable {P Q}

/-- The domain of `Disintegrate`, unfolded: full first-marginal support together with
the existence of a continuous-kernel point whose induced kernel is a version. -/
theorem disintegrate_dom_iff {μ : ProbabilityMeasure (X × Y)} :
    (Disintegrate P Q).Dom μ ↔
      FullFirstMarginalSupport μ
        ∧ ∃ f : ContinuousKernelPoint P Q, IsCondKernel μ (inducedKernel f) := by
  constructor
  · rintro ⟨f, hs, hk⟩
    exact ⟨hs, f, hk⟩
  · rintro ⟨hs, f, hk⟩
    exact ⟨f, hs, hk⟩

/-- **Pointwise uniqueness of the accepted output** (full support ⇒ two continuous
versions agreeing a.e. agree everywhere):

* `isCondKernel_ae_unique` gives `CondKernelAEEq` (mathlib Disintegration/Unique.lean);
* `ProbabilityMeasure.toMeasure_injective` transports it to the carrier maps;
* the weak topology on `ProbabilityMeasure Y` is T2 (mathlib instance
  `ProbabilityMeasure.t2Space`, via `[HasOuterApproxClosed Y]`, automatic for metric
  `Y`), and the first marginal is open-positive by full support, so mathlib's
  `Measure.eq_of_ae_eq` (OpenPos.lean) upgrades a.e. to everywhere;
* `RealizableFun.ext` and `Subtype.ext` finish. -/
theorem disintegrate_accepts_unique [StandardBorelSpace Y] [Nonempty Y]
    {μ : ProbabilityMeasure (X × Y)} {f f' : ContinuousKernelPoint P Q}
    (h : (Disintegrate P Q).accepts μ f) (h' : (Disintegrate P Q).accepts μ f') :
    f = f' := by
  obtain ⟨hs, hk⟩ := h
  obtain ⟨-, hk'⟩ := h'
  have hae : CondKernelAEEq μ (inducedKernel f) (inducedKernel f') :=
    isCondKernel_ae_unique hk hk'
  haveI : μ.toMeasure.fst.IsOpenPosMeasure := hs.isOpenPosMeasure
  have haefun : f.val.toFun =ᵐ[μ.toMeasure.fst] f'.val.toFun := by
    filter_upwards [hae] with x hx
    rw [inducedKernel_apply, inducedKernel_apply] at hx
    exact MeasureTheory.ProbabilityMeasure.toMeasure_injective hx
  have htofun : f.val.toFun = f'.val.toFun :=
    Measure.eq_of_ae_eq haefun f.prop.1 f'.prop.1
  exact Subtype.ext (RealizableFun.ext (congrFun htofun))

end Conditioning

end ComputableAnalysis
