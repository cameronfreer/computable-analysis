/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.Realizer

/-!
# Computable maps between representations

`ComputableMap X Y f` says some oracle code realizes `f` on names. Identity is realized by
`query`; composition by oracle substitution (`OracleCode.evalStream_subst`), which needs
the inner realizer to converge only on the valid name at hand; and computable points are
preserved via the foundation bridge `OracleCode.computable_of_mem_evalStream`.

Units 8–9 stay on bare `Representation` (comparing representations of one fixed carrier);
the bundled `RepSpace` enters with problems and reductions (units 10–11).
-/

namespace ComputableAnalysis

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable {X : Representation α} {Y : Representation β} {Z : Representation γ}

/-- `f` is a **computable map** from `X` to `Y`: some oracle code realizes it on names. -/
def ComputableMap (X : Representation α) (Y : Representation β) (f : α → β) : Prop :=
  ∃ c : OracleCode, Realizes X Y c f

namespace ComputableMap

/-- The identity map is computable, realized by `query`. -/
protected theorem id : ComputableMap X X id :=
  ⟨.query, fun p _ hpa => ⟨p, by simp, hpa⟩⟩

/-- **Composition.** Computable maps compose, realized by oracle substitution: the outer
code runs against the stream produced by the inner code on the given valid name
(`OracleCode.evalStream_subst`). -/
protected theorem comp {g : β → γ} {f : α → β} (hg : ComputableMap Y Z g)
    (hf : ComputableMap X Y f) : ComputableMap X Z (g ∘ f) := by
  obtain ⟨cg, hcg⟩ := hg
  obtain ⟨cf, hcf⟩ := hf
  refine ⟨cg.subst cf, fun p a hpa => ?_⟩
  obtain ⟨q, hq, hqf⟩ := hcf p a hpa
  obtain ⟨r, hr, hrg⟩ := hcg q (f a) hqf
  exact ⟨r, (OracleCode.evalStream_subst hq).symm ▸ hr, hrg⟩

/-- **Preservation of computable points.** The image of a computable point under a
computable map is computable: the realizer's total stream value on a computable name is
itself computable (`OracleCode.computable_of_mem_evalStream`). -/
protected theorem computablePoint {f : α → β} {a : α} (hf : ComputableMap X Y f)
    (ha : X.ComputablePoint a) : Y.ComputablePoint (f a) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨p, hp, hpa⟩ := ha
  obtain ⟨q, hq, hqf⟩ := hc p a hpa
  exact ⟨q, OracleCode.computable_of_mem_evalStream hp hq, hqf⟩

end ComputableMap

end ComputableAnalysis
