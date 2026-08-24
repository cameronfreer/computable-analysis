/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Problem

/-!
# Ordinary Weihrauch reduction

`f ≤W g` (convention 6): there exist **fixed** codes `K` (preprocessor) and `H`
(postprocessor) such that for *every* realizer `G` of `g`, the transformer
`p ↦ H (interleave p (G (K p)))` realizes `f`. The quantifier order is structural —
`∃ K H, ∀ G` — and the postprocessor sees the *original input* through
`Baire.interleave`, which is exactly what strong reduction removes (unit 11).

`IsReductionPair` is the fixed-witness local condition on `(K, H)` with no quantification
over realizers; `reduction_iff_exists_reductionPair` proves it equivalent to `≤W`. The
forward direction probes the reduction with adversarial realizers — a realizer erased at
one name (forcing the preprocessed name to denote an in-domain input, by
single-valuedness of `Part`) and the patched realizer of `Problem.exists_realizer_patch`
(forcing the postprocessor to handle every permitted answer).

Reflexivity, transitivity, and the calibration `ComputableProblem f ↔ f ≤W idProblem X`
are all proved through reduction pairs, assembling the fixed codes from `query`,
the deinterleaving codes, `OracleCode.pairCode`, and oracle substitution. The identity
and composition constructions are exposed as `isReductionPair_refl` and
`IsReductionPair.comp` (composite postprocessor `ordinaryCompPost`), with codes explicit,
so the bundled-witness layer composes them without re-deriving the codes.
-/

namespace ComputableAnalysis

universe u v u' v' u'' v''

variable {X : RepSpace.{u}} {Y : RepSpace.{v}} {X' : RepSpace.{u'}} {Y' : RepSpace.{v'}}
  {X'' : RepSpace.{u''}} {Y'' : RepSpace.{v''}}

/-- **Ordinary Weihrauch reduction** (convention 6): fixed codes `K, H` transform every
realizer of `g` into a realizer of `f`, the postprocessor seeing the original input via
`Baire.interleave`. -/
def WeihrauchReducible (f : Problem X Y) (g : Problem X' Y') : Prop :=
  ∃ K H : OracleCode, ∀ G, g.Realizes G →
    f.Realizes fun p => do
      let k ← K.evalStream p; let a ← G k; H.evalStream (Baire.interleave p a)

@[inherit_doc] infix:50 " ≤W " => WeihrauchReducible

/-- **Ordinary Weihrauch equivalence.** Mutual `≤W`. Distinct from `Problem.Equivalent`, which
is extensional equality of `accepts`: equivalent problems need not accept the same pairs, only
reduce to each other. -/
def WeihrauchEquivalent (f : Problem X Y) (g : Problem X' Y') : Prop := f ≤W g ∧ g ≤W f

@[inherit_doc] infix:50 " ≡W " => WeihrauchEquivalent

/-- Membership in the ordinary transformer, unfolded. Stated on `Part.bind` (definitionally
the do-block of `WeihrauchReducible`), so use sites convert by `exact`. -/
private theorem mem_transform_iff {K H : OracleCode} {G : Baire →. Baire} {p q : Baire} :
    q ∈ (K.evalStream p).bind (fun k => (G k).bind fun a =>
      H.evalStream (Baire.interleave p a)) ↔
    ∃ k ∈ K.evalStream p, ∃ a ∈ G k, q ∈ H.evalStream (Baire.interleave p a) := by
  simp only [Part.mem_bind_iff]

/-- The fixed-witness transformer condition on `(K, H)`: no quantification over
realizers. The preprocessed name must denote an in-domain input of `g`, and the
postprocessor must convert *every* permitted answer name into an accepted output name. -/
def IsReductionPair (f : Problem X Y) (g : Problem X' Y') (K H : OracleCode) : Prop :=
  ∀ p x, X.rep.Names p x → f.Dom x →
    ∃ k ∈ K.evalStream p, ∃ x', X'.rep.Names k x' ∧ g.Dom x' ∧
      ∀ a y', Y'.rep.Names a y' → g.accepts x' y' →
        ∃ q ∈ H.evalStream (Baire.interleave p a), ∃ y, Y.rep.Names q y ∧ f.accepts x y

/-- **The transformer characterization.** `f ≤W g` iff some fixed pair `(K, H)` satisfies
the local condition `IsReductionPair`. The forward direction probes the reduction with an
erased realizer (single-valuedness forces the preprocessed name into the domain) and with
patched realizers (every permitted answer must be handled). -/
theorem reduction_iff_exists_reductionPair {f : Problem X Y} {g : Problem X' Y'} :
    f ≤W g ↔ ∃ K H, IsReductionPair f g K H := by
  classical
  constructor
  · rintro ⟨K, H, hKH⟩
    refine ⟨K, H, fun p x hpx hdom => ?_⟩
    obtain ⟨G₀, hG₀⟩ := g.exists_realizer
    obtain ⟨q₀, hq₀, -⟩ := hKH G₀ hG₀ p x hpx hdom
    obtain ⟨k, hk, a₀, ha₀, -⟩ := mem_transform_iff.mp hq₀
    refine ⟨k, hk, ?_⟩
    have hx' : ∃ x', X'.rep.Names k x' ∧ g.Dom x' := by
      by_contra hno
      have hG₁ : g.Realizes fun r => if r = k then Part.none else G₀ r := by
        intro r x' hrx' hdom'
        have hr : r ≠ k := fun hrk => hno ⟨x', hrk ▸ hrx', hdom'⟩
        simpa only [ite_eq_right hr] using hG₀ r x' hrx' hdom'
      obtain ⟨q₁, hq₁, -⟩ := hKH _ hG₁ p x hpx hdom
      obtain ⟨k₁, hk₁, a₁, ha₁, -⟩ := mem_transform_iff.mp hq₁
      rw [Part.mem_unique hk₁ hk] at ha₁
      simp at ha₁
    obtain ⟨x', hkx', hdom'⟩ := hx'
    refine ⟨x', hkx', hdom', fun a y' hay' hacc => ?_⟩
    obtain ⟨G₂, hG₂, haG₂⟩ := Problem.exists_realizer_patch hkx' hacc hay'
    obtain ⟨q, hq, y, hqy, hfacc⟩ := hKH G₂ hG₂ p x hpx hdom
    obtain ⟨k₂, hk₂, a₂, ha₂, hqH⟩ := mem_transform_iff.mp hq
    rw [Part.mem_unique hk₂ hk] at ha₂
    rw [Part.mem_unique ha₂ haG₂] at hqH
    exact ⟨q, hqH, y, hqy, hfacc⟩
  · rintro ⟨K, H, hpair⟩
    refine ⟨K, H, fun G hG p x hpx hdom => ?_⟩
    obtain ⟨k, hk, x', hkx', hdom', hH⟩ := hpair p x hpx hdom
    obtain ⟨a, haG, y', hay', hacc⟩ := hG k x' hkx' hdom'
    obtain ⟨q, hqH, y, hqy, hfacc⟩ := hH a y' hay' hacc
    exact ⟨q, mem_transform_iff.mpr ⟨k, hk, a, haG, hqH⟩, y, hqy, hfacc⟩

/-! ### The executable reduction-pair calculus

Identity, composition, and congruence at the level of `IsReductionPair`, each with its
codes stated explicitly. These are the constructions previously welded inside
`WeihrauchReducible.refl`/`trans`; the bundled-witness combinators consume them without
passing through the existential propositions. -/

/-- The identity reduction pair: query the oracle, and read the answer off the odd track
of the interleaving. -/
theorem isReductionPair_refl (f : Problem X Y) : IsReductionPair f f .query .oddCode := by
  intro p x hpx hdom
  refine ⟨p, by simp, x, hpx, hdom, fun a y' hay' hacc => ⟨a, ?_, y', hay', hacc⟩⟩
  rw [OracleCode.evalStream_oddCode_interleave]
  exact Part.mem_some a

/-- The composite ordinary postprocessor: on the original input interleaved with the outer
answer, rebuild the middle name (the preprocessor `K₁` run on the even track), pair it with
the answer on the odd track, run the middle postprocessor `H₂`, re-pair its output with the
original input, and run `H₁`. -/
noncomputable def ordinaryCompPost (K₁ H₁ H₂ : OracleCode) : OracleCode :=
  H₁.subst (.pairCode .evenCode (H₂.subst (.pairCode (K₁.subst .evenCode) .oddCode)))

/-- Composition of reduction pairs, with the composite codes explicit: the preprocessors
compose by substitution, the postprocessors by `ordinaryCompPost`. -/
protected theorem IsReductionPair.comp {f : Problem X Y} {g : Problem X' Y'}
    {h : Problem X'' Y''} {K₁ H₁ K₂ H₂ : OracleCode} (hp₁ : IsReductionPair f g K₁ H₁)
    (hp₂ : IsReductionPair g h K₂ H₂) :
    IsReductionPair f h (K₂.subst K₁) (ordinaryCompPost K₁ H₁ H₂) := by
  intro p x hpx hdom
  obtain ⟨k₁, hk₁, x₁, hkx₁, hdom₁, hH₁⟩ := hp₁ p x hpx hdom
  obtain ⟨k₂, hk₂, x₂, hkx₂, hdom₂, hH₂⟩ := hp₂ k₁ x₁ hkx₁ hdom₁
  refine ⟨k₂, ?_, x₂, hkx₂, hdom₂, fun a y'' hay'' hacc => ?_⟩
  · rw [OracleCode.evalStream_subst hk₁]; exact hk₂
  · -- Run the middle postprocessor, then the outer one, tracking the interleavings.
    obtain ⟨a₁, ha₁, y', hay', hacc'⟩ := hH₂ a y'' hay'' hacc
    obtain ⟨q, hq, y, hqy, hfacc⟩ := hH₁ a₁ y' hay' hacc'
    set r := Baire.interleave p a with hr
    have hpr : p ∈ OracleCode.evenCode.evalStream r := by
      rw [hr, OracleCode.evalStream_evenCode_interleave]; exact Part.mem_some p
    have har : a ∈ OracleCode.oddCode.evalStream r := by
      rw [hr, OracleCode.evalStream_oddCode_interleave]; exact Part.mem_some a
    have hk₁r : k₁ ∈ (K₁.subst .evenCode).evalStream r := by
      rw [OracleCode.evalStream_subst hpr]; exact hk₁
    have hka : Baire.interleave k₁ a ∈
        (OracleCode.pairCode (K₁.subst .evenCode) .oddCode).evalStream r :=
      OracleCode.pairCode_spec hk₁r har
    have ha₁r : a₁ ∈ (H₂.subst
        (OracleCode.pairCode (K₁.subst .evenCode) .oddCode)).evalStream r := by
      rw [OracleCode.evalStream_subst hka]; exact ha₁
    have hpa₁ : Baire.interleave p a₁ ∈
        (OracleCode.pairCode .evenCode (H₂.subst
          (OracleCode.pairCode (K₁.subst .evenCode) .oddCode))).evalStream r :=
      OracleCode.pairCode_spec hpr ha₁r
    refine ⟨q, ?_, y, hqy, hfacc⟩
    change q ∈ (H₁.subst _).evalStream r
    rw [OracleCode.evalStream_subst hpa₁]
    exact hq

/-- A reduction pair transports along problem equivalences, with the same codes. -/
protected theorem IsReductionPair.congr {f f' : Problem X Y} {g g' : Problem X' Y'}
    {K H : OracleCode} (hf : f.Equivalent f') (hg : g.Equivalent g')
    (hp : IsReductionPair f g K H) : IsReductionPair f' g' K H := by
  intro p x hpx hdom
  obtain ⟨y₀, hy₀⟩ := hdom
  obtain ⟨k, hk, x', hkx', hdom', hH⟩ := hp p x hpx ⟨y₀, (hf x y₀).mpr hy₀⟩
  refine ⟨k, hk, x', hkx', ?_, fun a y' hay' hacc => ?_⟩
  · obtain ⟨y₁, hy₁⟩ := hdom'
    exact ⟨y₁, (hg x' y₁).mp hy₁⟩
  · obtain ⟨q, hq, y, hqy, hfacc⟩ := hH a y' hay' ((hg x' y').mpr hacc)
    exact ⟨q, hq, y, hqy, (hf x y).mp hfacc⟩

namespace WeihrauchReducible

protected theorem refl (f : Problem X Y) : f ≤W f :=
  reduction_iff_exists_reductionPair.mpr ⟨_, _, isReductionPair_refl f⟩

protected theorem trans {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (hfg : f ≤W g) (hgh : g ≤W h) : f ≤W h := by
  obtain ⟨K₁, H₁, hp₁⟩ := reduction_iff_exists_reductionPair.mp hfg
  obtain ⟨K₂, H₂, hp₂⟩ := reduction_iff_exists_reductionPair.mp hgh
  exact reduction_iff_exists_reductionPair.mpr ⟨_, _, hp₁.comp hp₂⟩

/-- Reduction is invariant under problem equivalence. -/
theorem congr {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') : (f ≤W g) ↔ (f' ≤W g') := by
  constructor <;> rintro ⟨K, H, hKH⟩ <;> refine ⟨K, H, fun G hG => ?_⟩
  · exact (hf.realizes_iff).mp (hKH G ((hg.realizes_iff).mpr hG))
  · exact (hf.realizes_iff).mpr (hKH G ((hg.realizes_iff).mp hG))

end WeihrauchReducible

/-- **Calibration.** A problem is computable exactly when it reduces to the identity: the
oracle contributes nothing beyond echoing a name of the input. -/
theorem computableProblem_iff_le_idProblem {f : Problem X Y} :
    ComputableProblem f ↔ f ≤W idProblem X := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨co, hco⟩ := type2Computable_oddPart
    refine reduction_iff_exists_reductionPair.mpr
      ⟨.query, c.subst co, fun p x hpx hdom =>
        ⟨p, by simp, x, hpx, ⟨x, rfl⟩, fun a y' hay' hacc => ?_⟩⟩
    obtain ⟨q, hq, y, hqy, hfacc⟩ := hc a x (show X.rep.Names a x from hacc ▸ hay') hdom
    refine ⟨q, ?_, y, hqy, hfacc⟩
    have har : a ∈ co.evalStream (Baire.interleave p a) := by
      rw [OracleCode.computes_iff_evalStream.mp hco, Baire.oddPart_interleave]
      exact Part.mem_some a
    rw [OracleCode.evalStream_subst har]
    exact hq
  · rintro ⟨K, H, hKH⟩
    have hGid : (idProblem X).Realizes fun p => Part.some p :=
      fun p x hpx _ => ⟨p, Part.mem_some p, x, hpx, rfl⟩
    refine ⟨H.subst (OracleCode.pairCode .query K), fun p x hpx hdom => ?_⟩
    obtain ⟨q, hq, y, hqy, hfacc⟩ := hKH _ hGid p x hpx hdom
    obtain ⟨k, hk, a, ha, hqH⟩ := mem_transform_iff.mp hq
    rw [Part.mem_some_iff] at ha
    subst ha
    have hpk : Baire.interleave p a ∈
        (OracleCode.pairCode OracleCode.query K).evalStream p :=
      OracleCode.pairCode_spec (by simp) hk
    refine ⟨q, ?_, y, hqy, hfacc⟩
    rw [OracleCode.evalStream_subst hpk]
    exact hqH

end ComputableAnalysis
