/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.Constructions
import ComputableAnalysis.Weihrauch.Problem

/-!
# The machine-independent problem algebra

Constructions on problems and their extensional laws, stated purely at the level of the
`accepts` relations — no oracle codes, no names, no Baire-space plumbing in the basic laws.
The semantic intermediate layer between the bare `Problem` relation and the Weihrauch
reduction theory:

* `Problem.Tightens f g`: on every input `g` must handle, `f` is defined and permits no
  answers `g` forbids — so every solver of `f` solves `g` (`Problem.Tightens.realizes`). A
  preorder whose induced equivalence is exactly `Problem.Equivalent`
  (`Problem.equivalent_iff_mutual_tightens`).
* `Problem.restrict` / `Problem.corestrict`: shrink the domain by a predicate on inputs,
  respectively the permitted answers by a predicate on outputs.
* `Problem.relThen` / `Problem.«then»`: plain relational composition versus spec-safe
  sequential composition, which adds the domain-safety clause that makes composed
  realizers correct (`Problem.Realizes.then`). Spec-safe composition is associative up to
  `Problem.Equivalent` (`Problem.then_assoc`), unconditionally.
* `Problem.prod` / `Problem.coprod`: coordinatewise semantics on the product represented
  space `RepSpace.prod`, tag-wise semantics on the sum `RepSpace.sum`.

The only realizer-level facts are the two at the end — contravariant monotonicity of
realizers under tightening, and safe composition of realizers — both direct from the
definitions, with no reduction theory.
-/

namespace ComputableAnalysis

universe u v w w' u' v'

variable {X : RepSpace.{u}} {Y : RepSpace.{v}} {Z : RepSpace.{w}} {W : RepSpace.{w'}}
  {X' : RepSpace.{u'}} {Y' : RepSpace.{v'}}

namespace Problem

/-! ### Tightening: the refinement order of specifications -/

/-- `f.Tightens g`: on every input `g` is required to handle, `f` is defined and permits
no answers `g` does not permit. The refinement order of specifications: every solver of
`f` solves `g` (`Tightens.realizes`). Off `g.Dom` the behavior of `f` is unconstrained. -/
def Tightens (f g : Problem X Y) : Prop :=
  (∀ x, g.Dom x → f.Dom x) ∧ ∀ x, g.Dom x → ∀ y, f.accepts x y → g.accepts x y

/-- Tightening is reflexive. -/
theorem Tightens.refl (f : Problem X Y) : f.Tightens f :=
  ⟨fun _ hx => hx, fun _ _ _ hy => hy⟩

/-- Tightening is transitive. -/
theorem Tightens.trans {f g h : Problem X Y} (hfg : f.Tightens g) (hgh : g.Tightens h) :
    f.Tightens h :=
  ⟨fun x hx => hfg.1 x (hgh.1 x hx),
   fun x hx y hy => hgh.2 x hx y (hfg.2 x (hgh.1 x hx) y hy)⟩

/-- Equivalent problems tighten each other (one bridge direction). -/
theorem Equivalent.tightens {f g : Problem X Y} (h : f.Equivalent g) : f.Tightens g :=
  ⟨fun _ hx => h.dom_iff.mpr hx, fun x _ y hy => (h x y).mp hy⟩

/-- Equivalence is reflexive. -/
theorem Equivalent.refl (f : Problem X Y) : f.Equivalent f := fun _ _ => Iff.rfl

/-- Equivalence is symmetric. -/
theorem Equivalent.symm {f g : Problem X Y} (h : f.Equivalent g) : g.Equivalent f :=
  fun x y => (h x y).symm

/-- Equivalence is transitive. -/
theorem Equivalent.trans {f g h : Problem X Y} (hfg : f.Equivalent g)
    (hgh : g.Equivalent h) : f.Equivalent h :=
  fun x y => (hfg x y).trans (hgh x y)

/-- **Mutual tightening is equivalence** (antisymmetry up to `Equivalent`): the domains
coincide, on the common domain the accepted answers coincide, and off it both problems
accept nothing. -/
theorem Tightens.antisymm {f g : Problem X Y} (hfg : f.Tightens g) (hgf : g.Tightens f) :
    f.Equivalent g := by
  intro x y
  constructor
  · intro hy
    exact hfg.2 x (hgf.1 x ⟨y, hy⟩) y hy
  · intro hy
    exact hgf.2 x (hfg.1 x ⟨y, hy⟩) y hy

/-- The equivalence induced by the tightening preorder is exactly `Problem.Equivalent`. -/
theorem equivalent_iff_mutual_tightens {f g : Problem X Y} :
    f.Equivalent g ↔ f.Tightens g ∧ g.Tightens f :=
  ⟨fun h => ⟨h.tightens, h.symm.tightens⟩, fun h => h.1.antisymm h.2⟩

/-! ### Restriction and corestriction -/

/-- Restrict a problem to the inputs satisfying `P`: the same answers are accepted there,
and nothing is required — or accepted — off `P`. -/
def restrict (f : Problem X Y) (P : X → Prop) : Problem X Y :=
  ⟨fun x y => P x ∧ f.accepts x y⟩

@[simp]
theorem restrict_accepts_iff {f : Problem X Y} {P : X → Prop} {x : X} {y : Y} :
    (f.restrict P).accepts x y ↔ P x ∧ f.accepts x y := Iff.rfl

/-- The domain of a restriction: the inputs satisfying `P` that were already solvable. -/
@[simp]
theorem restrict_dom_iff {f : Problem X Y} {P : X → Prop} {x : X} :
    (f.restrict P).Dom x ↔ P x ∧ f.Dom x :=
  ⟨fun ⟨y, hPx, hy⟩ => ⟨hPx, y, hy⟩, fun ⟨hPx, y, hy⟩ => ⟨y, hPx, hy⟩⟩

/-- Corestrict a problem to the answers satisfying `Q`: only such answers remain
accepted, so the domain shrinks to the inputs with a `Q`-answer. -/
def corestrict (f : Problem X Y) (Q : Y → Prop) : Problem X Y :=
  ⟨fun x y => f.accepts x y ∧ Q y⟩

@[simp]
theorem corestrict_accepts_iff {f : Problem X Y} {Q : Y → Prop} {x : X} {y : Y} :
    (f.corestrict Q).accepts x y ↔ f.accepts x y ∧ Q y := Iff.rfl

/-- The domain of a corestriction: the inputs with at least one accepted `Q`-answer. -/
@[simp]
theorem corestrict_dom_iff {f : Problem X Y} {Q : Y → Prop} {x : X} :
    (f.corestrict Q).Dom x ↔ ∃ y, f.accepts x y ∧ Q y := Iff.rfl

/-- A problem tightens each of its restrictions: solving everywhere is a refinement of
solving on `P`. -/
theorem tightens_restrict (f : Problem X Y) (P : X → Prop) : f.Tightens (f.restrict P) :=
  ⟨fun _ hx => (restrict_dom_iff.mp hx).2,
   fun _ hx _ hy => ⟨(restrict_dom_iff.mp hx).1, hy⟩⟩

/-- A corestriction tightens the restriction of the original problem to the
corestriction's own domain: wherever a `Q`-answer exists, any solver of the corestricted
problem solves the original. -/
theorem corestrict_tightens_restrict (f : Problem X Y) (Q : Y → Prop) :
    (f.corestrict Q).Tightens (f.restrict fun x => (f.corestrict Q).Dom x) :=
  ⟨fun _ hx => (restrict_dom_iff.mp hx).1,
   fun _ hx _ hy => ⟨(restrict_dom_iff.mp hx).1, hy.1⟩⟩

/-- Congruence of restriction under equivalence. -/
theorem Equivalent.restrict {f f' : Problem X Y} (h : f.Equivalent f') (P : X → Prop) :
    (f.restrict P).Equivalent (f'.restrict P) :=
  fun x y => and_congr_right fun _ => h x y

/-- Congruence of corestriction under equivalence. -/
theorem Equivalent.corestrict {f f' : Problem X Y} (h : f.Equivalent f') (Q : Y → Prop) :
    (f.corestrict Q).Equivalent (f'.corestrict Q) :=
  fun x y => and_congr_left fun _ => h x y

/-! ### Sequential composition: relational and spec-safe -/

/-- Plain relational composition, `f` first: `(g.relThen f).accepts x z` iff some
`f`-accepted intermediate `y` has `g.accepts y z`. Purely the composite relation — no
safety requirement on the intermediates (contrast `Problem.«then»`). -/
def relThen (g : Problem Y Z) (f : Problem X Y) : Problem X Z :=
  ⟨fun x z => ∃ y, f.accepts x y ∧ g.accepts y z⟩

/-- **Spec-safe sequential composition**, `f` first: besides reaching `z` through some
accepted intermediate (as in `relThen`), the input must be *safe* — every `f`-accepted
intermediate must lie in `g.Dom` — because a solver of `f` may output any accepted
intermediate and a solver of `g` is unconstrained off `g.Dom`.

`«then»` and `relThen` differ precisely on the unsafe inputs: at any `x` where all
`f`-accepted answers lie in `g.Dom` the two accept the same pairs
(`then_accepts_iff_of_safe`), while at an unsafe `x` the spec-safe composition accepts
nothing (its domain is characterized by `then_dom_iff`) but `relThen` may still accept.
Consequently composed realizers realize `g.«then» f` (`Problem.Realizes.then`) but not
`g.relThen f` in general. -/
def «then» (g : Problem Y Z) (f : Problem X Y) : Problem X Z :=
  ⟨fun x z => (∀ y, f.accepts x y → g.Dom y) ∧ ∃ y, f.accepts x y ∧ g.accepts y z⟩

@[simp]
theorem relThen_accepts_iff {g : Problem Y Z} {f : Problem X Y} {x : X} {z : Z} :
    (g.relThen f).accepts x z ↔ ∃ y, f.accepts x y ∧ g.accepts y z := Iff.rfl

@[simp]
theorem then_accepts_iff {g : Problem Y Z} {f : Problem X Y} {x : X} {z : Z} :
    (g.«then» f).accepts x z ↔
      (∀ y, f.accepts x y → g.Dom y) ∧ ∃ y, f.accepts x y ∧ g.accepts y z := Iff.rfl

/-- The domain of the relational composition: some accepted intermediate is solvable. -/
@[simp]
theorem relThen_dom_iff {g : Problem Y Z} {f : Problem X Y} {x : X} :
    (g.relThen f).Dom x ↔ ∃ y, f.accepts x y ∧ g.Dom y :=
  ⟨fun ⟨z, y, hxy, hyz⟩ => ⟨y, hxy, z, hyz⟩, fun ⟨y, hxy, z, hyz⟩ => ⟨z, y, hxy, hyz⟩⟩

/-- The domain of the spec-safe composition: the first stage is solvable and *every* of
its accepted intermediates is solvable by the second. -/
@[simp]
theorem then_dom_iff {g : Problem Y Z} {f : Problem X Y} {x : X} :
    (g.«then» f).Dom x ↔ f.Dom x ∧ ∀ y, f.accepts x y → g.Dom y := by
  constructor
  · rintro ⟨z, hsafe, y, hxy, hyz⟩
    exact ⟨⟨y, hxy⟩, hsafe⟩
  · rintro ⟨⟨y, hxy⟩, hsafe⟩
    obtain ⟨z, hyz⟩ := hsafe y hxy
    exact ⟨z, hsafe, y, hxy, hyz⟩

/-- On a safe input — every `f`-accepted intermediate lies in `g.Dom` — the spec-safe
composition and the relational composition accept the same answers. -/
theorem then_accepts_iff_of_safe {g : Problem Y Z} {f : Problem X Y} {x : X}
    (hsafe : ∀ y, f.accepts x y → g.Dom y) {z : Z} :
    (g.«then» f).accepts x z ↔ (g.relThen f).accepts x z :=
  ⟨fun h => h.2, fun h => ⟨hsafe, h⟩⟩

/-- The relational composition tightens the spec-safe composition: on the (smaller)
spec-safe domain the two agree, so any solver of `relThen` solves `«then»`. -/
theorem relThen_tightens_then (g : Problem Y Z) (f : Problem X Y) :
    (g.relThen f).Tightens (g.«then» f) := by
  refine ⟨fun x hx => ?_, fun x hx z hz => ?_⟩
  · obtain ⟨⟨y, hxy⟩, hsafe⟩ := then_dom_iff.mp hx
    exact relThen_dom_iff.mpr ⟨y, hxy, hsafe y hxy⟩
  · exact ⟨(then_dom_iff.mp hx).2, hz⟩

/-- Congruence of relational composition under equivalence. -/
theorem Equivalent.relThen {g g' : Problem Y Z} {f f' : Problem X Y}
    (hg : g.Equivalent g') (hf : f.Equivalent f') :
    (g.relThen f).Equivalent (g'.relThen f') :=
  fun x z => exists_congr fun y => and_congr (hf x y) (hg y z)

/-- Congruence of spec-safe composition under equivalence. -/
theorem Equivalent.«then» {g g' : Problem Y Z} {f f' : Problem X Y}
    (hg : g.Equivalent g') (hf : f.Equivalent f') :
    (g.«then» f).Equivalent (g'.«then» f') :=
  fun x z =>
    and_congr (forall_congr' fun y => imp_congr (hf x y) hg.dom_iff)
      (exists_congr fun y => and_congr (hf x y) (hg y z))

/-- Relational composition is associative (up to `Equivalent`: the accepted pairs are the
same after reordering the two intermediate witnesses). -/
theorem relThen_assoc (h : Problem Z W) (g : Problem Y Z) (f : Problem X Y) :
    ((h.relThen g).relThen f).Equivalent (h.relThen (g.relThen f)) := by
  intro x w
  constructor
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩

/-- **Spec-safe composition is associative**, unconditionally, up to `Equivalent`. Both
bracketings accept `(x, w)` iff every `f`-accepted intermediate is `g`-solvable, every
`g`-accepted successor of an `f`-accepted intermediate is `h`-solvable, and some accepted
chain `x → y → z → w` exists — the two safety clauses just accumulate. -/
theorem then_assoc (h : Problem Z W) (g : Problem Y Z) (f : Problem X Y) :
    ((h.«then» g).«then» f).Equivalent (h.«then» (g.«then» f)) := by
  intro x w
  simp only [then_accepts_iff, then_dom_iff]
  constructor
  · rintro ⟨hS, y₀, hxy₀, hT₀, z₀, hy₀z₀, hz₀w⟩
    have hS₁ : ∀ y, f.accepts x y → g.Dom y := fun y hy => (hS y hy).1
    refine ⟨fun z hz => ?_, z₀, ⟨hS₁, y₀, hxy₀, hy₀z₀⟩, hz₀w⟩
    obtain ⟨-, y, hxy, hyz⟩ := hz
    exact (hS y hxy).2 z hyz
  · rintro ⟨hT, z₀, ⟨hS₁, y₀, hxy₀, hy₀z₀⟩, hz₀w⟩
    refine ⟨fun y hxy => ⟨hS₁ y hxy, fun z hyz => hT z ⟨hS₁, y, hxy, hyz⟩⟩,
      y₀, hxy₀, fun z hyz => hT z ⟨hS₁, y₀, hxy₀, hyz⟩, z₀, hy₀z₀, hz₀w⟩

/-! ### Products and coproducts -/

/-- The product problem on the product represented spaces: a pair of answers is accepted
iff each coordinate is accepted on the corresponding input coordinate. -/
def prod (f : Problem X Y) (g : Problem X' Y') : Problem (X.prod X') (Y.prod Y') :=
  ⟨fun x y => f.accepts x.1 y.1 ∧ g.accepts x.2 y.2⟩

@[simp]
theorem prod_accepts_iff {f : Problem X Y} {g : Problem X' Y'} {x : X.prod X'}
    {y : Y.prod Y'} :
    (f.prod g).accepts x y ↔ f.accepts x.1 y.1 ∧ g.accepts x.2 y.2 := Iff.rfl

/-- The domain of a product problem is the product of the domains. -/
@[simp]
theorem prod_dom_iff {f : Problem X Y} {g : Problem X' Y'} {x : X.prod X'} :
    (f.prod g).Dom x ↔ f.Dom x.1 ∧ g.Dom x.2 :=
  ⟨fun ⟨y, hy⟩ => ⟨⟨y.1, hy.1⟩, y.2, hy.2⟩,
   fun ⟨⟨y₁, hy₁⟩, y₂, hy₂⟩ => ⟨(y₁, y₂), hy₁, hy₂⟩⟩

/-- Congruence of products under equivalence. -/
theorem Equivalent.prod {f f' : Problem X Y} {g g' : Problem X' Y'}
    (hf : f.Equivalent f') (hg : g.Equivalent g') :
    (f.prod g).Equivalent (f'.prod g') :=
  fun x y => and_congr (hf x.1 y.1) (hg x.2 y.2)

/-- Tightening is preserved by products. -/
theorem Tightens.prod {f f' : Problem X Y} {g g' : Problem X' Y'}
    (hf : f.Tightens f') (hg : g.Tightens g') :
    (f.prod g).Tightens (f'.prod g') := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨h₁, h₂⟩ := prod_dom_iff.mp hx
    exact prod_dom_iff.mpr ⟨hf.1 x.1 h₁, hg.1 x.2 h₂⟩
  · obtain ⟨h₁, h₂⟩ := prod_dom_iff.mp hx
    exact ⟨hf.2 x.1 h₁ y.1 hy.1, hg.2 x.2 h₂ y.2 hy.2⟩

/-- The coproduct problem on the sum represented spaces: tag-wise semantics. A left input
accepts exactly the left answers `f` accepts, a right input the right answers `g` accepts;
mixed tags are never accepted. -/
def coprod (f : Problem X Y) (g : Problem X' Y') : Problem (X.sum X') (Y.sum Y') :=
  ⟨fun x y =>
    match x, y with
    | Sum.inl x, Sum.inl y => f.accepts x y
    | Sum.inr x, Sum.inr y => g.accepts x y
    | Sum.inl _, Sum.inr _ => False
    | Sum.inr _, Sum.inl _ => False⟩

@[simp]
theorem coprod_accepts_inl_inl_iff {f : Problem X Y} {g : Problem X' Y'} {x : X} {y : Y} :
    (f.coprod g).accepts (Sum.inl x) (Sum.inl y) ↔ f.accepts x y := Iff.rfl

@[simp]
theorem coprod_accepts_inr_inr_iff {f : Problem X Y} {g : Problem X' Y'} {x : X'}
    {y : Y'} : (f.coprod g).accepts (Sum.inr x) (Sum.inr y) ↔ g.accepts x y := Iff.rfl

@[simp]
theorem coprod_accepts_inl_inr_iff {f : Problem X Y} {g : Problem X' Y'} {x : X}
    {y : Y'} : (f.coprod g).accepts (Sum.inl x) (Sum.inr y) ↔ False := Iff.rfl

@[simp]
theorem coprod_accepts_inr_inl_iff {f : Problem X Y} {g : Problem X' Y'} {x : X'}
    {y : Y} : (f.coprod g).accepts (Sum.inr x) (Sum.inl y) ↔ False := Iff.rfl

/-- The domain of a coproduct problem at a left input is the left domain. -/
@[simp]
theorem coprod_dom_inl_iff {f : Problem X Y} {g : Problem X' Y'} {x : X} :
    (f.coprod g).Dom (Sum.inl x) ↔ f.Dom x := by
  constructor
  · rintro ⟨(y | y), hy⟩
    · exact ⟨y, hy⟩
    · exact hy.elim
  · rintro ⟨y, hy⟩
    exact ⟨Sum.inl y, hy⟩

/-- The domain of a coproduct problem at a right input is the right domain. -/
@[simp]
theorem coprod_dom_inr_iff {f : Problem X Y} {g : Problem X' Y'} {x : X'} :
    (f.coprod g).Dom (Sum.inr x) ↔ g.Dom x := by
  constructor
  · rintro ⟨(y | y), hy⟩
    · exact hy.elim
    · exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨Sum.inr y, hy⟩

/-- Congruence of coproducts under equivalence. -/
theorem Equivalent.coprod {f f' : Problem X Y} {g g' : Problem X' Y'}
    (hf : f.Equivalent f') (hg : g.Equivalent g') :
    (f.coprod g).Equivalent (f'.coprod g') := by
  rintro (x | x) (y | y)
  · exact hf x y
  · exact Iff.rfl
  · exact Iff.rfl
  · exact hg x y

/-- Tightening is preserved by coproducts. -/
theorem Tightens.coprod {f f' : Problem X Y} {g g' : Problem X' Y'}
    (hf : f.Tightens f') (hg : g.Tightens g') :
    (f.coprod g).Tightens (f'.coprod g') := by
  constructor
  · rintro (x | x) hx
    · exact coprod_dom_inl_iff.mpr (hf.1 x (coprod_dom_inl_iff.mp hx))
    · exact coprod_dom_inr_iff.mpr (hg.1 x (coprod_dom_inr_iff.mp hx))
  · rintro (x | x) hx (y | y) hy
    · exact hf.2 x (coprod_dom_inl_iff.mp hx) y hy
    · exact hy.elim
    · exact hy.elim
    · exact hg.2 x (coprod_dom_inr_iff.mp hx) y hy

/-! ### Realizer lemmas

The two facts the reduction theory will consume, proved abstractly: no oracle codes, only
the definition of `Problem.Realizes`. -/

/-- **Realizers are contravariantly monotone under tightening**: a realizer of `f`
realizes every problem `f` tightens — "every solver of `f` solves `g`", made literal at
the level of partial stream functions. -/
theorem Tightens.realizes {f g : Problem X Y} (h : f.Tightens g) {G : Baire →. Baire}
    (hG : f.Realizes G) : g.Realizes G := by
  intro p x hpx hdom
  obtain ⟨q, hqG, y, hqy, hacc⟩ := hG p x hpx (h.1 x hdom)
  exact ⟨q, hqG, y, hqy, h.2 x hdom y hacc⟩

/-- **Safe composition of realizers**: composing a realizer of `f` with a realizer of `g`
(as partial functions on Baire space) realizes the spec-safe composition `g.«then» f`. The
safety clause is exactly what makes this work: the intermediate answer produced by the
first realizer — whichever accepted one it is — is guaranteed to lie in `g.Dom`, where the
second realizer is constrained. For `g.relThen f` the composite can diverge or err on an
accepted input whose first-stage answer falls outside `g.Dom`. -/
theorem Realizes.«then» {f : Problem X Y} {g : Problem Y Z} {F G : Baire →. Baire}
    (hg : g.Realizes G) (hf : f.Realizes F) :
    (g.«then» f).Realizes fun p => (F p).bind G := by
  intro p x hpx hdom
  obtain ⟨hfdom, hsafe⟩ := then_dom_iff.mp hdom
  obtain ⟨q, hqF, y, hqy, hacc⟩ := hf p x hpx hfdom
  obtain ⟨r, hrG, z, hrz, hacc'⟩ := hg q y hqy (hsafe y hacc)
  exact ⟨r, Part.mem_bind_iff.mpr ⟨q, hqF, hrG⟩, z, hrz, hsafe, y, hacc, hacc'⟩

end Problem

end ComputableAnalysis
