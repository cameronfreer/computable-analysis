/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.Basic
import ComputableAnalysis.TypeTwo.Continuity
import ComputableAnalysis.TypeTwo.Universal

/-!
# Realizers

`Realizes X Y c f` says the oracle code `c` tracks `f : α → β` on names: on every name `p`
of every point `a`, the stream value of `c` at `p` converges to a name of `f a`
(convention 2: behavior is constrained on valid names only).

The **foundation bridge** `OracleCode.computable_of_mem_evalStream` closes the loop with
first-order computability: a total stream value of a code on a computable input is itself
computable. It is the Type-2 fact behind preservation of computable points, proved here by
running the code at the fixed oracle (`exists_code_iff_recursiveIn`), eliminating the
computable oracle (`Nat.RecursiveIn.partrec_of_oracle`), and using totality coordinatewise.
-/

namespace ComputableAnalysis

universe u v

variable {α : Type u} {β : Type v}

namespace OracleCode

/-- The stream value of `query` on `p` is `p` itself: `query` realizes the identity. -/
@[simp]
theorem evalStream_query (p : Baire) : query.evalStream p = Part.some p :=
  Part.eq_some_iff.mpr (mem_evalStream.mpr fun n => by rw [eval_query]; exact Part.mem_some _)

/-- The stream value of `const k` on any `p` is the constant-`k` stream. -/
@[simp]
theorem evalStream_const (k : ℕ) (p : Baire) :
    (OracleCode.const k).evalStream p = Part.some fun _ => k :=
  Part.eq_some_iff.mpr (mem_evalStream.mpr fun n => by rw [eval_const]; exact Part.mem_some _)

/-- **Foundation bridge.** A total stream value of a code on a computable input is itself
computable. Run `c` at the fixed oracle `p` (`exists_code_iff_recursiveIn`), eliminate the
computable oracle (`Nat.RecursiveIn.partrec_of_oracle`), and conclude from coordinatewise
totality. Preservation of computable points consumes this; partial substitution alone does
not give it. -/
theorem computable_of_mem_evalStream {c : OracleCode} {p q : Baire}
    (hp : Computable p) (hq : q ∈ c.evalStream p) : Computable q := by
  have hrec : Nat.RecursiveIn {(p : ℕ →. ℕ)} (c.eval p) :=
    (exists_code_iff_recursiveIn p (c.eval p)).mp ⟨c, rfl⟩
  have hpart : Nat.Partrec (c.eval p) :=
    hrec.partrec_of_oracle fun g hg => by
      rcases Set.mem_singleton_iff.mp hg with rfl
      exact Partrec.nat_iff.mp hp.partrec
  exact (Partrec.nat_iff.mpr hpart).of_eq_tot (mem_evalStream.mp hq)

end OracleCode

/-- `c` **realizes** `f : α → β` from `X` to `Y`: on every name `p` of every point `a`, the
stream value of `c` at `p` converges to a name of `f a`. Convention 2: nothing is required
of `c` on invalid names. -/
def Realizes (X : Representation α) (Y : Representation β) (c : OracleCode) (f : α → β) :
    Prop :=
  ∀ p a, X.Names p a → ∃ q ∈ c.evalStream p, Y.Names q (f a)

/-- A totally computable stream function that maps names to names is a realizer. The
standard route from the `Computes` (total) view into the valid-name (partial) view. -/
theorem Realizes.of_computes {c : OracleCode} {F : Baire → Baire} {f : α → β}
    {X : Representation α} {Y : Representation β} (hc : c.Computes F)
    (h : ∀ p a, X.Names p a → Y.Names (F p) (f a)) : Realizes X Y c f := fun p a hpa =>
  ⟨F p, Part.eq_some_iff.mp (OracleCode.computes_iff_evalStream.mp hc p), h p a hpa⟩

end ComputableAnalysis
