/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Combinatorics.Hall.Finite
import ComputableAnalysis.Weihrauch.Problem

/-!
# Countable Hall as a Weihrauch problem, one-sided relation-plus-enumerator presentation

`Hall` receives a name of an ℕ-indexed family of finite candidate sets — presented **both**
ways at once: a positive decidable candidate *relation* on track `1`, and an explicit
candidate-list *enumerator* on track `0` — and must produce an injective transversal.

**The presentation is total and positional**, and every stream names *some* family; the
family's laws are promises inside `accepts`, exactly as for `WKL` and `EFILC`:

* `HallMemIff`: the **membership equivalence** — the enumerator enumerates exactly the
  relation's candidates. This is what makes the double presentation one object rather
  than two.
* `HallMarriage`: the finite marriage condition over the enumerated lists — the
  finite-Hall hypothesis, a correctness promise only.

Answers are points of `baireSpace`: streams selecting, at every index, a candidate **of
the relation**, injectively (`IsHallTransversal`). One-sided: nothing is required of
candidates left unchosen.

The semantic anchor `Hall.dom_iff` lives with the reduction (`HallEfilc.lean`): the
domain characterization *is* countable Hall, obtained by compiling to `EFILC` and
decoding a section — so no separate compactness argument is duplicated here.

This presentation mirrors the enumerated-candidates Hall statement variant of the
`reverse-mathlib` catalog (internal candidate relation plus internal enumerator with a
checked membership-equivalence property); the crosswalk between the two catalogs is
registered there by name, never inferred.
-/

namespace ComputableAnalysis

open Encodable Denumerable

/-! ### The presented family -/

/-- The index-`n` candidate list presented by `p`: track `0`, decoded through the
`Denumerable (List ℕ)` coding. Total — every natural decodes to some list. -/
def hallCand (p : Baire) (n : ℕ) : List ℕ := ofNat (List ℕ) (p (Nat.pair 0 n))

/-- The candidate relation presented by `p`: track `1`, positively and decidably — `y` is
a candidate of `n` iff the stream is nonzero there. -/
def HallRel (p : Baire) (n y : ℕ) : Prop := p (Nat.pair 1 (Nat.pair n y)) ≠ 0

/-- **The membership equivalence**: the enumerator enumerates exactly the relation's
candidates. -/
def HallMemIff (p : Baire) : Prop := ∀ n y, y ∈ hallCand p n ↔ HallRel p n y

/-- **The marriage condition** over the enumerated lists: every finite index set has at
least as many combined candidates as members. -/
def HallMarriage (p : Baire) : Prop :=
  ∀ s : Finset ℕ, s.card ≤ (s.biUnion fun n => (hallCand p n).toFinset).card

/-- `f` is an injective transversal of the family: every value is a candidate of its
index through the **relation**, and no value is chosen twice. One-sided. -/
def IsHallTransversal (p f : Baire) : Prop :=
  (∀ n, HallRel p n (f n)) ∧ ∀ n n', f n = f n' → n = n'

/-- **Countable Hall** as a problem: on a one-sided family presented by relation and
enumerator with the membership equivalence and the marriage condition, produce an
injective transversal. -/
def Hall : Problem baireSpace baireSpace :=
  ⟨fun p f => HallMemIff p ∧ HallMarriage p ∧ IsHallTransversal p f⟩

/-- **Definitional unfolding of `Hall.accepts`.** An explicit rewrite lemma, deliberately
not a global `simp` rule. -/
theorem Hall.accepts_iff {p f : Baire} :
    Hall.accepts p f ↔ HallMemIff p ∧ HallMarriage p ∧ IsHallTransversal p f :=
  Iff.rfl

end ComputableAnalysis
