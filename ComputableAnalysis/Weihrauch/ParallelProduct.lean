/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Witness
import ComputableAnalysis.Weihrauch.ProblemAlgebra

/-!
# The parallel product on reductions, cylinders, and the ordinary-to-strong upgrade

The semantic parallel product `f ×ₚ g` (`Problem.prod`) gains its executable reduction
witnesses: monotonicity in both arguments for ordinary and strong reductions, with the
composite codes explicit — preprocessors act on the even/odd halves of the product name
and re-pair by `OracleCode.pairCode`; the strong postprocessor does the same on the
answer, and the ordinary one first reassembles the interleaved halves each factor's
postprocessor expects.

`IsCylinder g` says the product with the Baire identity reduces strongly back to `g`.
The payoff is the **upgrade theorem** `IsCylinder.weihrauch_iff_strong`: against a
cylinder target, ordinary and strong reducibility agree. The bridge is
`IsReductionPair.toProdId` — an ordinary pair `(K, H)` is already a *strong* pair for
`f ≤sW id ×ₚ g` with preprocessor `pairCode query K` and postprocessor `H` unchanged:
the identity side routes the original input through the oracle answer, whose even track
is then (by single-valuedness of Baire names and acceptance by the identity) the input
itself, so the interleaved answer is exactly the stream the ordinary postprocessor
expects. Cylinders are from Brattka–Gherardi (arXiv:0905.4679).
-/

namespace ComputableAnalysis

@[inherit_doc] infixr:67 " ×ₚ " => Problem.prod

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {X₁ : RepSpace.{u₁}} {Y₁ : RepSpace.{v₁}} {X₂ : RepSpace.{u₂}} {Y₂ : RepSpace.{v₂}}
  {X₃ : RepSpace.{u₃}} {Y₃ : RepSpace.{v₃}} {X₄ : RepSpace.{u₄}} {Y₄ : RepSpace.{v₄}}

/-- The even half of a stream, as a stream value of `evenCode`. -/
private theorem evenPart_mem (p : Baire) : p.evenPart ∈ OracleCode.evenCode.evalStream p := by
  rw [OracleCode.evalStream_evenCode]; exact Part.mem_some _

/-- The odd half of a stream, as a stream value of `oddCode`. -/
private theorem oddPart_mem (p : Baire) : p.oddPart ∈ OracleCode.oddCode.evalStream p := by
  rw [OracleCode.evalStream_oddCode]; exact Part.mem_some _

/-- Names of an interleaving under a product representation, from names of the halves. -/
private theorem prod_names_interleave {α β : Type*} {A : Representation α}
    {B : Representation β} {p q : Baire} {a : α} {b : β} (ha : A.Names p a)
    (hb : B.Names q b) : (A.prod B).Names (Baire.interleave p q) (a, b) := by
  rw [Representation.prod_names_iff, Baire.evenPart_interleave, Baire.oddPart_interleave]
  exact ⟨ha, hb⟩

/-- **Strong monotonicity of the parallel product**, with explicit codes: each factor's
codes act on its half of the interleaving, re-paired by `pairCode`. -/
protected theorem IsStrongReductionPair.prod {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} {K₁ H₁ K₂ H₂ : OracleCode}
    (hp₁ : IsStrongReductionPair f₁ g₁ K₁ H₁) (hp₂ : IsStrongReductionPair f₂ g₂ K₂ H₂) :
    IsStrongReductionPair (f₁ ×ₚ f₂) (g₁ ×ₚ g₂)
      (.pairCode (K₁.subst .evenCode) (K₂.subst .oddCode))
      (.pairCode (H₁.subst .evenCode) (H₂.subst .oddCode)) := by
  intro w x hwx hdom
  obtain ⟨hx₁, hx₂⟩ := Representation.prod_names_iff.mp hwx
  rw [Problem.prod_dom_iff] at hdom
  obtain ⟨k₁, hk₁, x₁', hk₁x, hdom₁, hH₁⟩ := hp₁ w.evenPart x.1 hx₁ hdom.1
  obtain ⟨k₂, hk₂, x₂', hk₂x, hdom₂, hH₂⟩ := hp₂ w.oddPart x.2 hx₂ hdom.2
  have hkmem : Baire.interleave k₁ k₂ ∈
      (OracleCode.pairCode (K₁.subst .evenCode) (K₂.subst .oddCode)).evalStream w := by
    refine OracleCode.pairCode_spec ?_ ?_
    · rw [OracleCode.evalStream_subst (evenPart_mem w)]; exact hk₁
    · rw [OracleCode.evalStream_subst (oddPart_mem w)]; exact hk₂
  refine ⟨Baire.interleave k₁ k₂, hkmem, (x₁', x₂'), prod_names_interleave hk₁x hk₂x,
    Problem.prod_dom_iff.mpr ⟨hdom₁, hdom₂⟩, fun a y' hay' hacc => ?_⟩
  obtain ⟨hy₁, hy₂⟩ := Representation.prod_names_iff.mp hay'
  rw [Problem.prod_accepts_iff] at hacc
  obtain ⟨q₁, hq₁, y₁, hq₁y, hacc₁⟩ := hH₁ a.evenPart y'.1 hy₁ hacc.1
  obtain ⟨q₂, hq₂, y₂, hq₂y, hacc₂⟩ := hH₂ a.oddPart y'.2 hy₂ hacc.2
  have hqmem : Baire.interleave q₁ q₂ ∈
      (OracleCode.pairCode (H₁.subst .evenCode) (H₂.subst .oddCode)).evalStream a := by
    refine OracleCode.pairCode_spec ?_ ?_
    · rw [OracleCode.evalStream_subst (evenPart_mem a)]; exact hq₁
    · rw [OracleCode.evalStream_subst (oddPart_mem a)]; exact hq₂
  exact ⟨Baire.interleave q₁ q₂, hqmem, (y₁, y₂), prod_names_interleave hq₁y hq₂y,
    Problem.prod_accepts_iff.mpr ⟨hacc₁, hacc₂⟩⟩

/-- **Ordinary monotonicity of the parallel product**, with explicit codes: as in the
strong case, except each factor's postprocessor is fed the interleaving of its half of
the original input with its half of the answer. -/
protected theorem IsReductionPair.prod {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} {K₁ H₁ K₂ H₂ : OracleCode}
    (hp₁ : IsReductionPair f₁ g₁ K₁ H₁) (hp₂ : IsReductionPair f₂ g₂ K₂ H₂) :
    IsReductionPair (f₁ ×ₚ f₂) (g₁ ×ₚ g₂)
      (.pairCode (K₁.subst .evenCode) (K₂.subst .oddCode))
      (.pairCode
        (H₁.subst (.pairCode (OracleCode.evenCode.subst .evenCode)
          (OracleCode.evenCode.subst .oddCode)))
        (H₂.subst (.pairCode (OracleCode.oddCode.subst .evenCode)
          (OracleCode.oddCode.subst .oddCode)))) := by
  intro w x hwx hdom
  obtain ⟨hx₁, hx₂⟩ := Representation.prod_names_iff.mp hwx
  rw [Problem.prod_dom_iff] at hdom
  obtain ⟨k₁, hk₁, x₁', hk₁x, hdom₁, hH₁⟩ := hp₁ w.evenPart x.1 hx₁ hdom.1
  obtain ⟨k₂, hk₂, x₂', hk₂x, hdom₂, hH₂⟩ := hp₂ w.oddPart x.2 hx₂ hdom.2
  have hkmem : Baire.interleave k₁ k₂ ∈
      (OracleCode.pairCode (K₁.subst .evenCode) (K₂.subst .oddCode)).evalStream w := by
    refine OracleCode.pairCode_spec ?_ ?_
    · rw [OracleCode.evalStream_subst (evenPart_mem w)]; exact hk₁
    · rw [OracleCode.evalStream_subst (oddPart_mem w)]; exact hk₂
  refine ⟨Baire.interleave k₁ k₂, hkmem, (x₁', x₂'), prod_names_interleave hk₁x hk₂x,
    Problem.prod_dom_iff.mpr ⟨hdom₁, hdom₂⟩, fun a y' hay' hacc => ?_⟩
  obtain ⟨hy₁, hy₂⟩ := Representation.prod_names_iff.mp hay'
  rw [Problem.prod_accepts_iff] at hacc
  obtain ⟨q₁, hq₁, y₁, hq₁y, hacc₁⟩ := hH₁ a.evenPart y'.1 hy₁ hacc.1
  obtain ⟨q₂, hq₂, y₂, hq₂y, hacc₂⟩ := hH₂ a.oddPart y'.2 hy₂ hacc.2
  have hwr : w ∈ OracleCode.evenCode.evalStream (Baire.interleave w a) := by
    rw [OracleCode.evalStream_evenCode_interleave]; exact Part.mem_some _
  have har : a ∈ OracleCode.oddCode.evalStream (Baire.interleave w a) := by
    rw [OracleCode.evalStream_oddCode_interleave]; exact Part.mem_some _
  have hin₁ : Baire.interleave w.evenPart a.evenPart ∈
      (OracleCode.pairCode (OracleCode.evenCode.subst .evenCode)
        (OracleCode.evenCode.subst .oddCode)).evalStream (Baire.interleave w a) := by
    refine OracleCode.pairCode_spec ?_ ?_
    · rw [OracleCode.evalStream_subst hwr]; exact evenPart_mem w
    · rw [OracleCode.evalStream_subst har]; exact evenPart_mem a
  have hin₂ : Baire.interleave w.oddPart a.oddPart ∈
      (OracleCode.pairCode (OracleCode.oddCode.subst .evenCode)
        (OracleCode.oddCode.subst .oddCode)).evalStream (Baire.interleave w a) := by
    refine OracleCode.pairCode_spec ?_ ?_
    · rw [OracleCode.evalStream_subst hwr]; exact oddPart_mem w
    · rw [OracleCode.evalStream_subst har]; exact oddPart_mem a
  have hqmem : Baire.interleave q₁ q₂ ∈
      (OracleCode.pairCode
        (H₁.subst (.pairCode (OracleCode.evenCode.subst .evenCode)
          (OracleCode.evenCode.subst .oddCode)))
        (H₂.subst (.pairCode (OracleCode.oddCode.subst .evenCode)
          (OracleCode.oddCode.subst .oddCode)))).evalStream (Baire.interleave w a) := by
    refine OracleCode.pairCode_spec ?_ ?_
    · rw [OracleCode.evalStream_subst hin₁]; exact hq₁
    · rw [OracleCode.evalStream_subst hin₂]; exact hq₂
  exact ⟨Baire.interleave q₁ q₂, hqmem, (y₁, y₂), prod_names_interleave hq₁y hq₂y,
    Problem.prod_accepts_iff.mpr ⟨hacc₁, hacc₂⟩⟩

/-- The parallel product of bundled strong reductions, fields explicit. -/
noncomputable def StrongWeihrauchReduction.prod {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (r₁ : StrongWeihrauchReduction f₁ g₁)
    (r₂ : StrongWeihrauchReduction f₂ g₂) :
    StrongWeihrauchReduction (f₁ ×ₚ f₂) (g₁ ×ₚ g₂) :=
  ⟨.pairCode (r₁.pre.subst .evenCode) (r₂.pre.subst .oddCode),
   .pairCode (r₁.post.subst .evenCode) (r₂.post.subst .oddCode),
   r₁.spec.prod r₂.spec⟩

@[simp] theorem StrongWeihrauchReduction.prod_pre {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (r₁ : StrongWeihrauchReduction f₁ g₁)
    (r₂ : StrongWeihrauchReduction f₂ g₂) :
    (r₁.prod r₂).pre = .pairCode (r₁.pre.subst .evenCode) (r₂.pre.subst .oddCode) := rfl

@[simp] theorem StrongWeihrauchReduction.prod_post {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (r₁ : StrongWeihrauchReduction f₁ g₁)
    (r₂ : StrongWeihrauchReduction f₂ g₂) :
    (r₁.prod r₂).post = .pairCode (r₁.post.subst .evenCode) (r₂.post.subst .oddCode) := rfl

/-- The parallel product of bundled ordinary reductions, fields explicit. -/
noncomputable def WeihrauchReduction.prod {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (r₁ : WeihrauchReduction f₁ g₁)
    (r₂ : WeihrauchReduction f₂ g₂) : WeihrauchReduction (f₁ ×ₚ f₂) (g₁ ×ₚ g₂) :=
  ⟨.pairCode (r₁.pre.subst .evenCode) (r₂.pre.subst .oddCode),
   .pairCode
     (r₁.post.subst (.pairCode (OracleCode.evenCode.subst .evenCode)
       (OracleCode.evenCode.subst .oddCode)))
     (r₂.post.subst (.pairCode (OracleCode.oddCode.subst .evenCode)
       (OracleCode.oddCode.subst .oddCode))),
   r₁.spec.prod r₂.spec⟩

@[simp] theorem WeihrauchReduction.prod_pre {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (r₁ : WeihrauchReduction f₁ g₁)
    (r₂ : WeihrauchReduction f₂ g₂) :
    (r₁.prod r₂).pre = .pairCode (r₁.pre.subst .evenCode) (r₂.pre.subst .oddCode) := rfl

@[simp] theorem WeihrauchReduction.prod_post {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (r₁ : WeihrauchReduction f₁ g₁)
    (r₂ : WeihrauchReduction f₂ g₂) :
    (r₁.prod r₂).post = .pairCode
      (r₁.post.subst (.pairCode (OracleCode.evenCode.subst .evenCode)
        (OracleCode.evenCode.subst .oddCode)))
      (r₂.post.subst (.pairCode (OracleCode.oddCode.subst .evenCode)
        (OracleCode.oddCode.subst .oddCode))) := rfl

/-- Strong reducibility is monotone under the parallel product. -/
theorem StrongWeihrauchReducible.prod {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (h₁ : f₁ ≤sW g₁) (h₂ : f₂ ≤sW g₂) :
    f₁ ×ₚ f₂ ≤sW g₁ ×ₚ g₂ := by
  obtain ⟨K₁, H₁, hp₁⟩ := strongReduction_iff_exists_reductionPair.mp h₁
  obtain ⟨K₂, H₂, hp₂⟩ := strongReduction_iff_exists_reductionPair.mp h₂
  exact strongReduction_iff_exists_reductionPair.mpr ⟨_, _, hp₁.prod hp₂⟩

/-- Ordinary reducibility is monotone under the parallel product. -/
theorem WeihrauchReducible.prod {f₁ : Problem X₁ Y₁} {g₁ : Problem X₂ Y₂}
    {f₂ : Problem X₃ Y₃} {g₂ : Problem X₄ Y₄} (h₁ : f₁ ≤W g₁) (h₂ : f₂ ≤W g₂) :
    f₁ ×ₚ f₂ ≤W g₁ ×ₚ g₂ := by
  obtain ⟨K₁, H₁, hp₁⟩ := reduction_iff_exists_reductionPair.mp h₁
  obtain ⟨K₂, H₂, hp₂⟩ := reduction_iff_exists_reductionPair.mp h₂
  exact reduction_iff_exists_reductionPair.mpr ⟨_, _, hp₁.prod hp₂⟩

/-! ### Cylinders and the ordinary-to-strong upgrade -/

universe u v u' v'

variable {X : RepSpace.{u}} {Y : RepSpace.{v}} {X' : RepSpace.{u'}} {Y' : RepSpace.{v'}}

/-- **Cylinders**: the product with the Baire identity reduces strongly back to the
problem. Against a cylinder target, ordinary reducibility upgrades to strong
(`IsCylinder.weihrauch_iff_strong`). -/
def IsCylinder (g : Problem X' Y') : Prop := idProblem baireSpace ×ₚ g ≤sW g

/-- An ordinary reduction pair to `g` is a **strong** pair to `id ×ₚ g`: the preprocessor
additionally routes the input name through the identity side, and the answer's even track
is forced (by acceptance and single-valuedness of Baire names) to be the original input,
so the unchanged ordinary postprocessor already runs on the interleaving it expects. -/
theorem IsReductionPair.toProdId {f : Problem X Y} {g : Problem X' Y'} {K H : OracleCode}
    (hp : IsReductionPair f g K H) :
    IsStrongReductionPair f (idProblem baireSpace ×ₚ g) (.pairCode .query K) H := by
  intro p x hpx hdom
  obtain ⟨k, hk, x', hkx, hdom', hH⟩ := hp p x hpx hdom
  have hpmem : p ∈ OracleCode.query.evalStream p := by simp
  refine ⟨Baire.interleave p k, OracleCode.pairCode_spec hpmem hk, (p, x'),
    prod_names_interleave (baireRep_names_iff.mpr rfl) hkx,
    Problem.prod_dom_iff.mpr ⟨⟨p, rfl⟩, hdom'⟩, fun a y' hay' hacc => ?_⟩
  obtain ⟨hy₁, hy₂⟩ := Representation.prod_names_iff.mp hay'
  rw [Problem.prod_accepts_iff] at hacc
  have hpa : a.evenPart = p := (baireRep_names_iff.mp hy₁).symm.trans hacc.1
  obtain ⟨q, hq, y, hqy, hfacc⟩ := hH a.oddPart y'.2 hy₂ hacc.2
  refine ⟨q, ?_, y, hqy, hfacc⟩
  rwa [← hpa, Baire.interleave_evenPart_oddPart] at hq

/-- Every ordinary reduction is a strong reduction to the product with the identity. -/
theorem WeihrauchReducible.strong_le_prod_id {f : Problem X Y} {g : Problem X' Y'}
    (h : f ≤W g) : f ≤sW idProblem baireSpace ×ₚ g := by
  obtain ⟨K, H, hp⟩ := reduction_iff_exists_reductionPair.mp h
  exact strongReduction_iff_exists_reductionPair.mpr ⟨_, _, hp.toProdId⟩

/-- **The upgrade theorem**: against a cylinder target, ordinary and strong Weihrauch
reducibility agree. -/
theorem IsCylinder.weihrauch_iff_strong {g : Problem X' Y'} (hg : IsCylinder g)
    {f : Problem X Y} : f ≤W g ↔ f ≤sW g :=
  ⟨fun h => StrongWeihrauchReducible.trans (WeihrauchReducible.strong_le_prod_id h) hg,
   strongWeihrauch_le_weihrauch⟩

end ComputableAnalysis
