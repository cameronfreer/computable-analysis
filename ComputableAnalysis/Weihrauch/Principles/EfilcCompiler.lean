/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.StrongReduction
import ComputableAnalysis.Weihrauch.Principles.EFILC

/-!
# The uniform strong-reduction compiler into `EFILC`

Every strong reduction into `EFILC` proved so far has the same shape: compile the input
name into a system name, check the two promises, and decode any accepted section into an
answer. `isStrongReductionPair_efilc_of_system` is that shape once — the `Baire`
representation bookkeeping and the `EFILC.accepts_iff` destructuring are discharged here,
so a consumer supplies only semantic data.

The three hypotheses are exactly the semantic obligations: the code produces the system
name, the compiled system keeps `EFILC`'s promises (`FibersNonempty`, `BondsIntoFiber`),
and every section of it decodes to an accepted answer.

**Strongness is enforced by the decoder's shape**: the decoding hypothesis is quantified
over the section `s` and its conclusion mentions `H.evalStream s`, so the postprocessor
runs on the answer stream and never on the input. A reduction that needs the input back
is an *ordinary* one and cannot be written through this compiler — which is the intended
discipline, not a limitation (compare `EfilcWKL.lean`, whose decoder legitimately consults
the input's chunk widths and so builds its `IsReductionPair` directly).

This mirrors the LPO/`Lim`/LLPO compilers of `Weihrauch/Compilers.lean`; it lives in its
own module so that reductions *out of* `EFILC`, which need no strong-reduction layer at
all, do not acquire one transitively.
-/

namespace ComputableAnalysis

universe u v

variable {X : RepSpace.{u}} {Y : RepSpace.{v}}

/-- **The uniform compiler for strong reductions into `EFILC`.** Given a code `K`
producing the compiled system name, the two promises for it, and an answer-only decoder
for its sections, the pair `(K, H)` is a strong reduction pair. -/
theorem isStrongReductionPair_efilc_of_system {f : Problem X Y} {K H : OracleCode}
    {system : Baire → Baire} (hK : ∀ p : Baire, system p ∈ K.evalStream p)
    (hne : ∀ p x, X.rep.Names p x → f.Dom x → FibersNonempty (system p))
    (hB : ∀ p x, X.rep.Names p x → f.Dom x → BondsIntoFiber (system p))
    (hdec : ∀ p x, X.rep.Names p x → f.Dom x → ∀ s : Baire, IsEfilcSection (system p) s →
      ∃ r ∈ H.evalStream s, ∃ y, Y.rep.Names r y ∧ f.accepts x y) :
    IsStrongReductionPair f EFILC K H := by
  intro p x hpx hdom
  refine ⟨system p, hK p, system p, baireRep_names_iff.mpr rfl,
    EFILC.dom_iff.mpr ⟨hne p x hpx hdom, hB p x hpx hdom⟩, ?_⟩
  intro a y' hay' hacc
  obtain rfl : y' = a := baireRep_names_iff.mp hay'
  obtain ⟨-, -, hsec⟩ := EFILC.accepts_iff.mp hacc
  exact hdec p x hpx hdom y' hsec

/-- The compiler's payoff at the level of the reduction itself. -/
theorem strongReduction_efilc_of_system {f : Problem X Y} {K H : OracleCode}
    {system : Baire → Baire} (hK : ∀ p : Baire, system p ∈ K.evalStream p)
    (hne : ∀ p x, X.rep.Names p x → f.Dom x → FibersNonempty (system p))
    (hB : ∀ p x, X.rep.Names p x → f.Dom x → BondsIntoFiber (system p))
    (hdec : ∀ p x, X.rep.Names p x → f.Dom x → ∀ s : Baire, IsEfilcSection (system p) s →
      ∃ r ∈ H.evalStream s, ∃ y, Y.rep.Names r y ∧ f.accepts x y) :
    f ≤sW EFILC :=
  strongReduction_iff_exists_reductionPair.mpr
    ⟨_, _, isStrongReductionPair_efilc_of_system hK hne hB hdec⟩

end ComputableAnalysis
