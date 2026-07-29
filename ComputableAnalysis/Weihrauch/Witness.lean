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
* `refl`, `trans`, and `StrongWeihrauchReduction.toWeihrauch`.

## Scope note

The structures and the `Nonempty` bridges are usable as they stand. The **combinators are not
yet executable compositions**: `WeihrauchReduction.refl`, `WeihrauchReduction.trans`,
`StrongWeihrauchReduction.refl`, `StrongWeihrauchReduction.trans` and
`StrongWeihrauchReduction.toWeihrauch` all obtain their codes through `Nonempty.some`, so none
of them exposes the codes it "builds".

This is a real boundary, not a formality: the underlying proofs do construct the codes —
`K₂.subst K₁` with a nested `subst`/`pairCode` postprocessor for ordinary transitivity,
`K₂.subst K₁` with `H₁.subst H₂` for the strong one, and `query`/`query` for strong
reflexivity — but those constructions are welded into proofs rather than available as lemmas on
`IsReductionPair` / `IsStrongReductionPair`.

Until they are factored out, a proof that wants the actual codes must still unpack the
propositions and rebuild them by hand, which is exactly what the bundled form is meant to
avoid. Factoring them is the immediate follow-up, and should precede the product/cylinder work
that will consume them.

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

/-- Identity reduction. Choice-mediated: see the scope note. -/
noncomputable def refl (f : Problem X Y) : WeihrauchReduction f f :=
  (weihrauchReducible_iff_nonempty.mp (WeihrauchReducible.refl f)).some

/-- Composition of reductions. Choice-mediated: see the scope note. -/
noncomputable def trans {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : WeihrauchReduction f g) (r₂ : WeihrauchReduction g h) : WeihrauchReduction f h :=
  (weihrauchReducible_iff_nonempty.mp
    ((weihrauchReducible_iff_nonempty.mpr ⟨r₁⟩).trans
      (weihrauchReducible_iff_nonempty.mpr ⟨r₂⟩))).some

end WeihrauchReduction

namespace StrongWeihrauchReduction

/-- Identity strong reduction. Choice-mediated: see the scope note. -/
noncomputable def refl (f : Problem X Y) : StrongWeihrauchReduction f f :=
  (strongWeihrauchReducible_iff_nonempty.mp (StrongWeihrauchReducible.refl f)).some

/-- Composition of strong reductions. Choice-mediated: see the scope note. -/
noncomputable def trans {f : Problem X Y} {g : Problem X' Y'} {h : Problem X'' Y''}
    (r₁ : StrongWeihrauchReduction f g) (r₂ : StrongWeihrauchReduction g h) :
    StrongWeihrauchReduction f h :=
  (strongWeihrauchReducible_iff_nonempty.mp
    ((strongWeihrauchReducible_iff_nonempty.mpr ⟨r₁⟩).trans
      (strongWeihrauchReducible_iff_nonempty.mpr ⟨r₂⟩))).some

/-- A strong reduction is in particular an ordinary one. Choice-mediated: see the scope
note. -/
noncomputable def toWeihrauch {f : Problem X Y} {g : Problem X' Y'}
    (r : StrongWeihrauchReduction f g) : WeihrauchReduction f g :=
  (weihrauchReducible_iff_nonempty.mp
    (strongWeihrauch_le_weihrauch (strongWeihrauchReducible_iff_nonempty.mpr ⟨r⟩))).some

end StrongWeihrauchReduction

end ComputableAnalysis
