/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.Realizer

/-!
# Problems and their realizers

A **problem** between represented spaces is a relation `accepts : X → Y → Prop`
(convention 5): partial (the domain is the derived `∃ y, accepts x y`) and multivalued
(several answers may be accepted). A **realizer** is a partial stream function sending
each valid name of an in-domain input to a name of *some* accepted answer.

Every problem has a realizer (`exists_realizer`, classical choice of an accepted answer
name per valid input), and any permitted answer name at one valid input extends to a full
realizer (`exists_realizer_patch`) — the probe used to characterize reductions by
fixed-witness transformer pairs in `Reduction.lean`.

A problem is **computable** when a single oracle code realizes it — not when it has a
total extensional selection `X → Y`, which is strictly stronger.
-/

namespace ComputableAnalysis

universe u v

variable {X : RepSpace.{u}} {Y : RepSpace.{v}}

/-- A problem from `X` to `Y`: a relation accepting zero or more answers per input
(convention 5). The domain is derived, never stored. -/
structure Problem (X : RepSpace.{u}) (Y : RepSpace.{v}) where
  /-- `accepts x y`: the answer `y` is permitted on the input `x`. -/
  accepts : X → Y → Prop

namespace Problem

/-- The domain of a problem: inputs with at least one accepted answer. -/
def Dom (f : Problem X Y) (x : X) : Prop := ∃ y, f.accepts x y

/-- `G` realizes `f`: every valid name of an in-domain input is sent to a name of some
accepted answer. Behavior is unconstrained off valid in-domain names (convention 2). -/
def Realizes (f : Problem X Y) (G : Baire →. Baire) : Prop :=
  ∀ p x, X.rep.Names p x → f.Dom x → ∃ q ∈ G p, ∃ y, Y.rep.Names q y ∧ f.accepts x y

/-- Every problem has a realizer: classically choose an accepted answer and a name for it
at each valid in-domain input. -/
theorem exists_realizer (f : Problem X Y) : ∃ G, f.Realizes G := by
  classical
  refine ⟨fun p => if h : ∃ x, X.rep.Names p x ∧ f.Dom x
    then Part.some (Y.rep.onto h.choose_spec.2.choose).choose else Part.none,
    fun p x hpx hdom => ?_⟩
  have h : ∃ x, X.rep.Names p x ∧ f.Dom x := ⟨x, hpx, hdom⟩
  simp only [dif_pos h]
  refine ⟨_, Part.mem_some _, h.choose_spec.2.choose, (Y.rep.onto _).choose_spec, ?_⟩
  have hxx : h.choose = x := Representation.names_unique h.choose_spec.1 hpx
  exact hxx ▸ h.choose_spec.2.choose_spec

/-- **Patched realizer.** Any permitted answer name at one valid input extends to a full
realizer taking that value there: overwrite a classical realizer at the given name. The
probe behind the fixed-witness transformer characterization of reductions. -/
theorem exists_realizer_patch {f : Problem X Y} {p : Baire} {x : X} {y : Y} {q : Baire}
    (hp : X.rep.Names p x) (hy : f.accepts x y) (hq : Y.rep.Names q y) :
    ∃ G : Baire →. Baire, f.Realizes G ∧ q ∈ G p := by
  classical
  obtain ⟨G₀, hG₀⟩ := f.exists_realizer
  refine ⟨fun r => if r = p then Part.some q else G₀ r, fun r x' hrx' hdom => ?_, by simp⟩
  by_cases hr : r = p
  · subst hr
    simp only
    have hxx : x' = x := Representation.names_unique hrx' hp
    exact ⟨q, Part.mem_some _, y, hq, hxx ▸ hy⟩
  · simp only [if_neg hr]
    exact hG₀ r x' hrx' hdom

/-- Two problems with the same endpoints are equivalent when they accept the same
answers on every input. -/
def Equivalent (f f' : Problem X Y) : Prop := ∀ x y, f.accepts x y ↔ f'.accepts x y

/-- Equivalent problems have the same domain. -/
theorem Equivalent.dom_iff {f f' : Problem X Y} (h : f.Equivalent f') {x : X} :
    f.Dom x ↔ f'.Dom x :=
  exists_congr fun y => h x y

/-- Equivalent problems have the same realizers. -/
theorem Equivalent.realizes_iff {f f' : Problem X Y} (h : f.Equivalent f')
    {G : Baire →. Baire} : f.Realizes G ↔ f'.Realizes G := by
  constructor <;> intro hG p x hpx hdom
  · obtain ⟨q, hqG, y, hqy, hacc⟩ := hG p x hpx ((h.dom_iff).mpr hdom)
    exact ⟨q, hqG, y, hqy, (h x y).mp hacc⟩
  · obtain ⟨q, hqG, y, hqy, hacc⟩ := hG p x hpx ((h.dom_iff).mp hdom)
    exact ⟨q, hqG, y, hqy, (h x y).mpr hacc⟩

end Problem

/-! ### Explicit problems -/

/-- The identity problem on `X`: the unique accepted answer is the input itself. -/
def idProblem (X : RepSpace.{u}) : Problem X X := ⟨fun x y => y = x⟩

/-- The empty-domain problem (calibration: it accepts nothing, so anything realizes it). -/
def zeroProblem : Problem baireSpace natSpace := ⟨fun _ _ => False⟩

/-- The total problem whose unique answer is the natural number `0`. -/
def constNatZeroProblem : Problem baireSpace natSpace := ⟨fun _ (n : ℕ) => n = 0⟩

/-- The total problem whose unique answer is the zero stream — the target of the
`≤W`/`≤sW` separation. -/
def constZeroProblem : Problem baireSpace baireSpace := ⟨fun _ (q : Baire) => q = fun _ => 0⟩

/-- A problem is **computable** when a single oracle code realizes it. Deliberately *not*
the existence of a computable total extensional selection `X → Y`, which is strictly
stronger for multivalued problems. -/
def ComputableProblem (f : Problem X Y) : Prop := ∃ c : OracleCode, f.Realizes c.evalStream

end ComputableAnalysis
