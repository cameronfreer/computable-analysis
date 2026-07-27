/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Primrec.List

/-!
# Primitive-recursive arithmetic helpers

Mathlib's `Computability/Primrec` closes `Primrec` under addition, multiplication,
subtraction, division and modular arithmetic, but has **no** lemma for exponentiation at the
current pin. Constructions that index anything dyadically therefore re-derive
`Primrec fun k => 2 ^ k` by hand, and this library had accumulated four independent private
copies of it before consolidation.

* `primrec_pow`: exponentiation with a fixed base is primitive recursive.

The proof is the obvious one — `b ^ k` as the `Nat.rec` that multiplies by `b` at each step,
which `Primrec.nat_rec'` accepts directly.

The two-argument form `Primrec₂ fun b k => b ^ k` is a natural generalization and is not
provided here; no consumer needs a varying base, and every use site fixes `b = 2`.
-/

namespace ComputableAnalysis

/-- **Exponentiation with a fixed base is primitive recursive.** Mathlib has no `Primrec`
lemma for `pow` at the current pin; this is the shared replacement for the private
re-derivations that used to sit in `Metric/CantorPresentation.lean`,
`Measure/WeakRepresentation.lean`, `Measure/DisintegrateLower.lean` and
`Measure/ConditionNoncomputable.lean`. -/
theorem primrec_pow (b : ℕ) : Primrec fun k : ℕ => b ^ k := by
  have h : Primrec fun k : ℕ =>
      Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => b * ih) k :=
    Primrec.nat_rec' Primrec.id (Primrec.const 1)
      ((Primrec.nat_mul.comp (Primrec.const b) (Primrec.snd.comp Primrec.snd)).to₂)
  refine h.of_eq fun k => ?_
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => b * ih) (k + 1)
        = b * Nat.rec (motive := fun _ => ℕ) 1 (fun _ ih => b * ih) k from rfl, ih, pow_succ]
      exact mul_comm b (b ^ k)

end ComputableAnalysis
