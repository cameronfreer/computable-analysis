/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Reduction

/-!
# Strong Weihrauch reduction and the `≤W`/`≤sW` separation

Strong reduction differs from ordinary reduction in exactly one structural point: the
postprocessor sees **only the oracle answer**, not the original input (no
`Baire.interleave`). `IsStrongReductionPair` is the corresponding fixed-witness condition,
equivalent to `≤sW` by the same adversarial-realizer probes as the ordinary case; strong
transitivity composes postprocessors by bare substitution (`H₁.subst H₂`), with no
input-tracking plumbing.

**Headline separation** (both over `baireSpace`): the identity problem reduces ordinarily
to the constant-zero problem — the ordinary postprocessor recovers the input as
`Baire.evenPart` of the interleaved name — but *not* strongly: a strong postprocessor sees
only the unique zero answer, and single-valuedness of `Part` forces it to emit one fixed
name, which cannot name two distinct inputs.
-/

namespace ComputableAnalysis

universe u v u' v' u'' v''

variable {X : RepSpace.{u}} {Y : RepSpace.{v}} {X' : RepSpace.{u'}} {Y' : RepSpace.{v'}}
  {X'' : RepSpace.{u''}} {Y'' : RepSpace.{v''}}

/-- **Strong Weihrauch reduction**: as `WeihrauchReducible`, but the postprocessor sees
only the oracle answer. -/
def StrongWeihrauchReducible (f : Problem X Y) (g : Problem X' Y') : Prop :=
  ∃ K H : OracleCode, ∀ G, g.Realizes G →
    f.Realizes fun p => do
      let k ← K.evalStream p; let a ← G k; H.evalStream a

@[inherit_doc] infix:50 " ≤sW " => StrongWeihrauchReducible

/-- Membership in the strong transformer, unfolded. Stated on `Part.bind` (definitionally
the do-block of `StrongWeihrauchReducible`), so use sites convert by `exact`. -/
private theorem mem_strongTransform_iff {K H : OracleCode} {G : Baire →. Baire}
    {p q : Baire} :
    q ∈ (K.evalStream p).bind (fun k => (G k).bind fun a => H.evalStream a) ↔
    ∃ k ∈ K.evalStream p, ∃ a ∈ G k, q ∈ H.evalStream a := by
  simp only [Part.mem_bind_iff]

/-- The fixed-witness transformer condition for strong reduction: as `IsReductionPair`,
but the postprocessor runs on the answer alone. -/
def IsStrongReductionPair (f : Problem X Y) (g : Problem X' Y') (K H : OracleCode) :
    Prop :=
  ∀ p x, X.rep.Names p x → f.Dom x →
    ∃ k ∈ K.evalStream p, ∃ x', X'.rep.Names k x' ∧ g.Dom x' ∧
      ∀ a y', Y'.rep.Names a y' → g.accepts x' y' →
        ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y

/-- **The strong transformer characterization**, by the same adversarial-realizer probes
as `reduction_iff_exists_reductionPair`. -/
theorem strongReduction_iff_exists_reductionPair {f : Problem X Y} {g : Problem X' Y'} :
    f ≤sW g ↔ ∃ K H, IsStrongReductionPair f g K H := by
  classical
  constructor
  · rintro ⟨K, H, hKH⟩
    refine ⟨K, H, fun p x hpx hdom => ?_⟩
    obtain ⟨G₀, hG₀⟩ := g.exists_realizer
    obtain ⟨q₀, hq₀, -⟩ := hKH G₀ hG₀ p x hpx hdom
    obtain ⟨k, hk, a₀, ha₀, -⟩ := mem_strongTransform_iff.mp hq₀
    refine ⟨k, hk, ?_⟩
    have hx' : ∃ x', X'.rep.Names k x' ∧ g.Dom x' := by
      by_contra hno
      have hG₁ : g.Realizes fun r => if r = k then Part.none else G₀ r := by
        intro r x' hrx' hdom'
        have hr : r ≠ k := fun hrk => hno ⟨x', hrk ▸ hrx', hdom'⟩
        simpa only [if_neg hr] using hG₀ r x' hrx' hdom'
      obtain ⟨q₁, hq₁, -⟩ := hKH _ hG₁ p x hpx hdom
      obtain ⟨k₁, hk₁, a₁, ha₁, -⟩ := mem_strongTransform_iff.mp hq₁
      rw [Part.mem_unique hk₁ hk] at ha₁
      simp at ha₁
    obtain ⟨x', hkx', hdom'⟩ := hx'
    refine ⟨x', hkx', hdom', fun a y' hay' hacc => ?_⟩
    obtain ⟨G₂, hG₂, haG₂⟩ := Problem.exists_realizer_patch hkx' hacc hay'
    obtain ⟨q, hq, y, hqy, hfacc⟩ := hKH G₂ hG₂ p x hpx hdom
    obtain ⟨k₂, hk₂, a₂, ha₂, hqH⟩ := mem_strongTransform_iff.mp hq
    rw [Part.mem_unique hk₂ hk] at ha₂
    rw [Part.mem_unique ha₂ haG₂] at hqH
    exact ⟨q, hqH, y, hqy, hfacc⟩
  · rintro ⟨K, H, hpair⟩
    refine ⟨K, H, fun G hG p x hpx hdom => ?_⟩
    obtain ⟨k, hk, x', hkx', hdom', hH⟩ := hpair p x hpx hdom
    obtain ⟨a, haG, y', hay', hacc⟩ := hG k x' hkx' hdom'
    obtain ⟨q, hqH, y, hqy, hfacc⟩ := hH a y' hay' hacc
    exact ⟨q, mem_strongTransform_iff.mpr ⟨k, hk, a, haG, hqH⟩, y, hqy, hfacc⟩

/-- Strong reduction implies ordinary reduction: precompose the strong postprocessor with
the odd-track projection, discarding the interleaved original input. -/
theorem strongWeihrauch_le_weihrauch {f : Problem X Y} {g : Problem X' Y'}
    (h : f ≤sW g) : f ≤W g := by
  obtain ⟨K, H, hpair⟩ := strongReduction_iff_exists_reductionPair.mp h
  obtain ⟨co, hco⟩ := type2Computable_oddPart
  refine reduction_iff_exists_reductionPair.mpr ⟨K, H.subst co, fun p x hpx hdom => ?_⟩
  obtain ⟨k, hk, x', hkx', hdom', hH⟩ := hpair p x hpx hdom
  refine ⟨k, hk, x', hkx', hdom', fun a y' hay' hacc => ?_⟩
  obtain ⟨q, hqH, y, hqy, hfacc⟩ := hH a y' hay' hacc
  have har : a ∈ co.evalStream (Baire.interleave p a) := by
    rw [OracleCode.computes_iff_evalStream.mp hco, Baire.oddPart_interleave]
    exact Part.mem_some a
  refine ⟨q, ?_, y, hqy, hfacc⟩
  rw [OracleCode.evalStream_subst har]
  exact hqH

namespace StrongWeihrauchReducible

protected theorem refl (f : Problem X Y) : f ≤sW f :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨.query, .query, fun p x hpx hdom =>
      ⟨p, by simp, x, hpx, hdom, fun a y' hay' hacc => ⟨a, by simp, y', hay', hacc⟩⟩⟩

protected theorem trans {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (hfg : f ≤sW g) (hgh : g ≤sW h) : f ≤sW h := by
  obtain ⟨K₁, H₁, hp₁⟩ := strongReduction_iff_exists_reductionPair.mp hfg
  obtain ⟨K₂, H₂, hp₂⟩ := strongReduction_iff_exists_reductionPair.mp hgh
  refine strongReduction_iff_exists_reductionPair.mpr
    ⟨K₂.subst K₁, H₁.subst H₂, fun p x hpx hdom => ?_⟩
  obtain ⟨k₁, hk₁, x₁, hkx₁, hdom₁, hH₁⟩ := hp₁ p x hpx hdom
  obtain ⟨k₂, hk₂, x₂, hkx₂, hdom₂, hH₂⟩ := hp₂ k₁ x₁ hkx₁ hdom₁
  refine ⟨k₂, ?_, x₂, hkx₂, hdom₂, fun a y'' hay'' hacc => ?_⟩
  · rw [OracleCode.evalStream_subst hk₁]; exact hk₂
  · obtain ⟨a₁, ha₁, y', hay', hacc'⟩ := hH₂ a y'' hay'' hacc
    obtain ⟨q, hq, y, hqy, hfacc⟩ := hH₁ a₁ y' hay' hacc'
    refine ⟨q, ?_, y, hqy, hfacc⟩
    rw [OracleCode.evalStream_subst ha₁]
    exact hq

/-- Strong reduction is invariant under problem equivalence. -/
theorem congr {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') : (f ≤sW g) ↔ (f' ≤sW g') := by
  constructor <;> rintro ⟨K, H, hKH⟩ <;> refine ⟨K, H, fun G hG => ?_⟩
  · exact (hf.realizes_iff).mp (hKH G ((hg.realizes_iff).mpr hG))
  · exact (hf.realizes_iff).mpr (hKH G ((hg.realizes_iff).mp hG))

end StrongWeihrauchReducible

/-! ### The headline `≤W`/`≤sW` separation -/

/-- The identity reduces **ordinarily** to the constant-zero problem: the ordinary
postprocessor recovers the original input as the even track of the interleaved name. -/
theorem idProblem_le_constZero : idProblem baireSpace ≤W constZeroProblem := by
  obtain ⟨ce, hce⟩ := type2Computable_evenPart
  refine reduction_iff_exists_reductionPair.mpr
    ⟨.query, ce, fun p x hpx hdom =>
      ⟨p, by simp, p, baireRep_names_iff.mpr rfl, ⟨_, rfl⟩, fun a y' hay' hacc => ?_⟩⟩
  refine ⟨p, ?_, x, ?_, rfl⟩
  · rw [OracleCode.computes_iff_evalStream.mp hce, Baire.evenPart_interleave]
    exact Part.mem_some p
  · exact hpx

/-- The identity does **not** reduce strongly to the constant-zero problem: a strong
postprocessor sees only the unique zero answer, so (by single-valuedness of `Part`) it
emits one fixed name, which cannot name two distinct inputs. -/
theorem idProblem_not_sle_constZero : ¬ idProblem baireSpace ≤sW constZeroProblem := by
  intro hsle
  obtain ⟨K, H, hpair⟩ := strongReduction_iff_exists_reductionPair.mp hsle
  have run : ∀ p : Baire, ∃ q ∈ H.evalStream (fun _ => 0), q = p := by
    intro p
    obtain ⟨k, -, x', -, -, hH⟩ :=
      hpair p p (baireRep_names_iff.mpr rfl) ⟨p, rfl⟩
    obtain ⟨q, hqH, y, hqy, hacc⟩ :=
      hH (fun _ => 0) (fun _ => 0) (baireRep_names_iff.mpr rfl) rfl
    exact ⟨q, hqH, (baireRep_names_iff.mp hqy).symm.trans hacc⟩
  obtain ⟨q₁, hq₁, hq₁e⟩ := run fun _ => 0
  obtain ⟨q₂, hq₂, hq₂e⟩ := run fun _ => 1
  have : (0 : ℕ) = 1 := by
    have hqq : q₁ = q₂ := Part.mem_unique hq₁ hq₂
    calc (0 : ℕ) = q₁ 0 := (congrFun hq₁e 0).symm
      _ = q₂ 0 := congrFun hqq 0
      _ = 1 := congrFun hq₂e 0
  exact absurd this (by omega)

/-- Some problem reduces ordinarily but not strongly — packaging of the headline
separation. -/
theorem exists_reduction_not_strong :
    ∃ (X Y X' Y' : RepSpace.{0}) (f : Problem X Y) (g : Problem X' Y'),
      (f ≤W g) ∧ ¬ (f ≤sW g) :=
  ⟨baireSpace, baireSpace, baireSpace, baireSpace, idProblem baireSpace,
    constZeroProblem, idProblem_le_constZero, idProblem_not_sle_constZero⟩

end ComputableAnalysis
