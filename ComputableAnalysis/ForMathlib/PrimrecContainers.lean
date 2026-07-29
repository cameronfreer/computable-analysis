/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Primrec.List

/-!
# Parameter-uniform primitive-recursive list combinators

Mathlib has the parameterized computational core — `Primrec.list_foldr` threads an external
parameter, `Primrec.listFilterMap` handles a parameter-dependent list *and* function,
`Primrec.list_findIdx` a parameter-dependent predicate, and `PrimrecRel.listFilter` a
separately supplied list and relation. What it lacks are direct lemmas for the corresponding
*semantic* operations, so developments reconstruct them at each use site.

This is a convenience layer, not new expressive power. In particular `List.filter` in the
Bool-valued form below is derivable from `PrimrecRel.listFilter`, at the cost of a Bool/Prop
bridge at every call; the wrapper exists to pay that once.

* `primrec_list_filter`, `primrec_list_all`, `primrec_list_any`: the predicate combinators,
  with the predicate depending on the same parameter as the list.
* `primrec_list_sum`: sums of natural-number lists.

`primrec_list_sum` is stated for `ℕ` because that is what the consumers need. The general
form does not follow from `Primcodable σ` alone — the addition itself must be primitive
recursive, so a generic version has to take `Primrec₂ ((· + ·) : σ → σ → σ)` as a hypothesis.

Upstreaming is tracked in issue #17; `primrec_list_filter` is deliberately *not* part of that
proposal's gap claim, being derivable upstream already.

## Upstream status

**Proposed as leanprover-community/mathlib4#42178** (`list_all`, `list_any`, natural-number
`list_sum`). `primrec_list_filter` is *not* part of that proposal: the Bool-valued parameterized
filter is derivable from `PrimrecRel.listFilter`, so it stays a local convenience.

Delete the upstreamed part at the first pin bump past the merge; keep `primrec_list_filter`.
Tracked in #17 and #21.
-/

namespace ComputableAnalysis

open Primrec

variable {α β : Type*} [Primcodable α] [Primcodable β]

/-- **Parameterized `List.filter`.** The predicate may depend on the same argument as the
list. Proved from `listFilterMap` without specializing its parameter to `id`. -/
theorem primrec_list_filter {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).filter (p a) :=
  (listFilterMap hf (Primrec.cond hp (option_some.comp snd) (const none)).to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons b l ih => cases h : p a b <;> simp [h, ih]

/-- **Parameterized `List.all`.** -/
theorem primrec_list_all {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).all (p a) :=
  (list_foldr hf (const true)
    (Primrec.and.comp (hp.comp fst (fst.comp snd)) (snd.comp snd)).to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons b l ih => simp [ih]

/-- **Parameterized `List.any`.** -/
theorem primrec_list_any {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec fun a => (f a).any (p a) :=
  (list_foldr hf (const false)
    (Primrec.or.comp (hp.comp fst (fst.comp snd)) (snd.comp snd)).to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons b l ih => simp [ih]

/-- **Sums of natural-number lists.** Stated at `ℕ` rather than a general `AddMonoid`: the
addition must itself be primitive recursive, which `Primcodable` does not supply. -/
theorem primrec_list_sum {f : α → List ℕ} (hf : Primrec f) :
    Primrec fun a => (f a).sum :=
  (list_foldr hf (const 0)
    (Primrec.nat_add.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun a => by
    induction f a with
    | nil => rfl
    | cons b l ih => simp [ih]

end ComputableAnalysis
