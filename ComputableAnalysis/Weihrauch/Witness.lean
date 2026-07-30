/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.StrongReduction

/-!
# Bundled reduction witnesses

`f ≤W g` and `f ≤sW g` are existential statements about a pair of `OracleCode`s. That is the
right *semantics*, but it makes structural proofs unpack and rebuild codes at every step. This
file adds the corresponding bundled witnesses and the bridges back to the propositions, leaving
the definitions of `≤W` and `≤sW` untouched.

* `WeihrauchReduction` / `StrongWeihrauchReduction`: a preprocessor, a postprocessor, and the
  `IsReductionPair` specification tying them to the two problems.
* `weihrauchReducible_iff_nonempty` / `strongWeihrauchReducible_iff_nonempty`: the bridges.
* `refl`, `trans`, `congr`, and `StrongWeihrauchReduction.toWeihrauch`, each an **executable
  composition**: the `pre` and `post` fields of a composite are built directly from the fields
  of the inputs (see the `@[simp]` field lemmas, all proved by `rfl`), by the corresponding
  calculus lemmas on `IsReductionPair` / `IsStrongReductionPair`. Nothing passes through the
  existential propositions or `Nonempty.some`.

The only remaining opacity is in the *atoms*: `OracleCode.pairCode`, `OracleCode.evenCode`,
and `OracleCode.oddCode` are shared constants extracted once from Prop-level existentials, so
combinators mentioning them are `noncomputable` in Lean's sense — but every composite exposes
its code structure over those atoms, which is what the congruence and closure proofs consume.
The strong combinators mention no atoms and are plain `def`s.
-/

namespace ComputableAnalysis

universe u v u' v' u'' v''

variable {X : RepSpace.{u}} {Y : RepSpace.{v}} {X' : RepSpace.{u'}} {Y' : RepSpace.{v'}}
  {X'' : RepSpace.{u''}} {Y'' : RepSpace.{v''}}

/-- A bundled ordinary Weihrauch reduction: the two codes together with their specification. -/
structure WeihrauchReduction (f : Problem X Y) (g : Problem X' Y') where
  /-- The preprocessor, run on a name of the input. -/
  pre : OracleCode
  /-- The postprocessor, run on the input interleaved with the oracle's answer. -/
  post : OracleCode
  /-- The two codes form a reduction pair. -/
  spec : IsReductionPair f g pre post

/-- A bundled strong Weihrauch reduction: as above, but the postprocessor sees only the
oracle's answer. -/
structure StrongWeihrauchReduction (f : Problem X Y) (g : Problem X' Y') where
  /-- The preprocessor, run on a name of the input. -/
  pre : OracleCode
  /-- The postprocessor, run on the oracle's answer alone. -/
  post : OracleCode
  /-- The two codes form a strong reduction pair. -/
  spec : IsStrongReductionPair f g pre post

theorem weihrauchReducible_iff_nonempty {f : Problem X Y} {g : Problem X' Y'} :
    f ≤W g ↔ Nonempty (WeihrauchReduction f g) := by
  rw [reduction_iff_exists_reductionPair]
  exact ⟨fun ⟨K, H, h⟩ => ⟨⟨K, H, h⟩⟩, fun ⟨r⟩ => ⟨r.pre, r.post, r.spec⟩⟩

theorem strongWeihrauchReducible_iff_nonempty {f : Problem X Y} {g : Problem X' Y'} :
    f ≤sW g ↔ Nonempty (StrongWeihrauchReduction f g) := by
  rw [strongReduction_iff_exists_reductionPair]
  exact ⟨fun ⟨K, H, h⟩ => ⟨⟨K, H, h⟩⟩, fun ⟨r⟩ => ⟨r.pre, r.post, r.spec⟩⟩

namespace WeihrauchReduction

/-- The identity reduction: query, and read the answer off the odd track. -/
noncomputable def refl (f : Problem X Y) : WeihrauchReduction f f :=
  ⟨.query, .oddCode, isReductionPair_refl f⟩

@[simp] theorem refl_pre (f : Problem X Y) : (refl f).pre = .query := rfl

@[simp] theorem refl_post (f : Problem X Y) : (refl f).post = .oddCode := rfl

/-- Composition of reductions: preprocessors compose by substitution, postprocessors by
`ordinaryCompPost`. -/
noncomputable def trans {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : WeihrauchReduction f g) (r₂ : WeihrauchReduction g h) : WeihrauchReduction f h :=
  ⟨r₂.pre.subst r₁.pre, ordinaryCompPost r₁.pre r₁.post r₂.post, r₁.spec.comp r₂.spec⟩

@[simp] theorem trans_pre {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : WeihrauchReduction f g) (r₂ : WeihrauchReduction g h) :
    (r₁.trans r₂).pre = r₂.pre.subst r₁.pre := rfl

@[simp] theorem trans_post {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : WeihrauchReduction f g) (r₂ : WeihrauchReduction g h) :
    (r₁.trans r₂).post = ordinaryCompPost r₁.pre r₁.post r₂.post := rfl

/-- A reduction transports along problem equivalences, with the same codes. -/
def congr {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') (r : WeihrauchReduction f g) : WeihrauchReduction f' g' :=
  ⟨r.pre, r.post, r.spec.congr hf hg⟩

@[simp] theorem congr_pre {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') (r : WeihrauchReduction f g) : (r.congr hf hg).pre = r.pre := rfl

@[simp] theorem congr_post {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') (r : WeihrauchReduction f g) : (r.congr hf hg).post = r.post := rfl

end WeihrauchReduction

namespace StrongWeihrauchReduction

/-- The identity strong reduction: query, and echo the answer. -/
def refl (f : Problem X Y) : StrongWeihrauchReduction f f :=
  ⟨.query, .query, isStrongReductionPair_refl f⟩

@[simp] theorem refl_pre (f : Problem X Y) : (refl f).pre = .query := rfl

@[simp] theorem refl_post (f : Problem X Y) : (refl f).post = .query := rfl

/-- Composition of strong reductions: preprocessors compose by substitution, postprocessors
by bare substitution the other way around. -/
def trans {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : StrongWeihrauchReduction f g) (r₂ : StrongWeihrauchReduction g h) :
    StrongWeihrauchReduction f h :=
  ⟨r₂.pre.subst r₁.pre, r₁.post.subst r₂.post, r₁.spec.comp r₂.spec⟩

@[simp] theorem trans_pre {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : StrongWeihrauchReduction f g) (r₂ : StrongWeihrauchReduction g h) :
    (r₁.trans r₂).pre = r₂.pre.subst r₁.pre := rfl

@[simp] theorem trans_post {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : StrongWeihrauchReduction f g) (r₂ : StrongWeihrauchReduction g h) :
    (r₁.trans r₂).post = r₁.post.subst r₂.post := rfl

/-- A strong reduction transports along problem equivalences, with the same codes. -/
def congr {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') (r : StrongWeihrauchReduction f g) :
    StrongWeihrauchReduction f' g' :=
  ⟨r.pre, r.post, r.spec.congr hf hg⟩

@[simp] theorem congr_pre {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') (r : StrongWeihrauchReduction f g) :
    (r.congr hf hg).pre = r.pre := rfl

@[simp] theorem congr_post {f f' : Problem X Y} {g g' : Problem X' Y'} (hf : f.Equivalent f')
    (hg : g.Equivalent g') (r : StrongWeihrauchReduction f g) :
    (r.congr hf hg).post = r.post := rfl

/-- A strong reduction is in particular an ordinary one: postcompose the postprocessor with
the odd-track projection. -/
noncomputable def toWeihrauch {f : Problem X Y} {g : Problem X' Y'}
    (r : StrongWeihrauchReduction f g) : WeihrauchReduction f g :=
  ⟨r.pre, r.post.subst .oddCode, r.spec.toReductionPair⟩

@[simp] theorem toWeihrauch_pre {f : Problem X Y} {g : Problem X' Y'}
    (r : StrongWeihrauchReduction f g) : r.toWeihrauch.pre = r.pre := rfl

@[simp] theorem toWeihrauch_post {f : Problem X Y} {g : Problem X' Y'}
    (r : StrongWeihrauchReduction f g) : r.toWeihrauch.post = r.post.subst .oddCode := rfl

end StrongWeihrauchReduction

end ComputableAnalysis
