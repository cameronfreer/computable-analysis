/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.Constructions

/-!
# Represented function spaces: advice-realizable maps

`AdvisedRealizes X Y c q f` says the oracle code `c` realizes `f` when its oracle carries
the advice stream `q` on the even track and a name of the argument on the odd track. The
function space `funRep X Y` represents the **advice-realizable maps** `RealizableFun X Y`:
a name head-cons-packs a code index (coordinate `0`) with an advice stream (the shifted
tail), and it names `f` exactly when the decoded pair advised-realizes `f` — invalid names
stay invalid (convention 2), and a `(code, advice)` pair realizes at most one function
(`advisedRealizes_unique`), so the representation is well-defined via choice.

Main results:

* `computableMap_funRep_eval`: evaluation is a computable map out of the product, via the
  Type-2 advised evaluator `OracleCode.exists_advisedEvalCode`.
* `RealizableFun.computablePoint_const`: the constant map at a computable point is a
  computable point of the function space.
* `computableMap_funRep_postcomp`: postcomposition by a fixed computable map is a
  computable map between function spaces.

Nothing here asserts continuity: absent an admissibility theory, the carrier is exactly
the advice-realizable maps, no more and no less.
-/

namespace ComputableAnalysis

open OracleCode

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}
variable {X : Representation α} {Y : Representation β} {Z : Representation γ}

/-! ### Advice-parameterized realization -/

/-- `c` realizes `f` with advice `q`: on every name `p` of every point `a`, running `c`
against the advice-interleaved oracle (advice on the even track, argument name on the odd
track) converges to a name of `f a`. -/
def AdvisedRealizes (X : Representation α) (Y : Representation β) (c : OracleCode)
    (q : Baire) (f : α → β) : Prop :=
  ∀ p a, X.Names p a → ∃ r ∈ c.evalStream (Baire.interleave q p), Y.Names r (f a)

/-- A `(code, advice)` pair advised-realizes at most one function: `X` is onto (every point
has a name), `evalStream` is single-valued (`Part.mem_unique`), and `Y`-names are
single-valued (`names_unique`). -/
theorem advisedRealizes_unique {c : OracleCode} {q : Baire} {f g : α → β}
    (hf : AdvisedRealizes X Y c q f) (hg : AdvisedRealizes X Y c q g) : f = g := by
  funext a
  obtain ⟨p, hp⟩ := X.onto a
  obtain ⟨r₁, hr₁, hn₁⟩ := hf p a hp
  obtain ⟨r₂, hr₂, hn₂⟩ := hg p a hp
  obtain rfl := Part.mem_unique hr₁ hr₂
  exact Representation.names_unique hn₁ hn₂

/-! ### The carrier and the function-space representation -/

/-- An **advice-realizable map** from `X` to `Y`: a function bundled with the mere
existence of an oracle code and an advice stream that advised-realize it. This is the
carrier of the represented function space `funRep`, kept deliberately opaque: nothing
identifies it with any topological class of functions. -/
structure RealizableFun (X : Representation α) (Y : Representation β) where
  /-- The underlying function. -/
  toFun : α → β
  /-- Some code and some advice stream advised-realize the underlying function. -/
  exists_advised : ∃ c q, AdvisedRealizes X Y c q toFun

/-- Apply an advice-realizable map as a function. -/
instance : CoeFun (RealizableFun X Y) fun _ => α → β :=
  ⟨RealizableFun.toFun⟩

/-- Extensionality: advice-realizable maps with the same underlying function are equal —
the realizability certificate is propositional. -/
@[ext]
theorem RealizableFun.ext {f g : RealizableFun X Y} (h : ∀ a, f a = g a) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  obtain rfl : f = g := funext h
  rfl

/-- Equality of underlying functions gives equality of advice-realizable maps. -/
private theorem RealizableFun.toFun_inj {f g : RealizableFun X Y} (h : f.toFun = g.toFun) :
    f = g :=
  RealizableFun.ext fun a => congrFun h a

/-- Pack a code and an advice stream into a function name: head `encode c`, tail `q`. -/
private def funPack (c : OracleCode) (q : Baire) : Baire :=
  fun n => n.casesOn (Encodable.encode c) q

/-- Decoding the head of a packed name recovers the code. -/
private theorem funCode_funPack (c : OracleCode) (q : Baire) :
    Denumerable.ofNat OracleCode (funPack c q 0) = c := by
  have h : funPack c q 0 = Encodable.encode c := rfl
  rw [h, Denumerable.ofNat_encode]

/-- The shifted tail of a packed name recovers the advice. -/
private theorem funAdvice_funPack (c : OracleCode) (q : Baire) :
    (fun n => funPack c q (n + 1)) = q := rfl

/-- The function-space representation of the advice-realizable maps: `F` names `f` exactly
when the head-decoded code `Denumerable.ofNat OracleCode (F 0)` together with the tail
advice `fun n => F (n + 1)` advised-realizes the underlying function. Well-defined via
choice through `advisedRealizes_unique`; convention 2: a name whose decoded pair realizes
no carrier point stays invalid — there is no default point. -/
noncomputable def funRep (X : Representation α) (Y : Representation β) :
    Representation (RealizableFun X Y) where
  rep F := ⟨∃ f : RealizableFun X Y,
      AdvisedRealizes X Y (Denumerable.ofNat OracleCode (F 0)) (fun n => F (n + 1)) f.toFun,
    fun h => h.choose⟩
  onto f := by
    obtain ⟨c, q, h⟩ := f.exists_advised
    have h' : AdvisedRealizes X Y (Denumerable.ofNat OracleCode (funPack c q 0))
        (fun n => funPack c q (n + 1)) f.toFun := by
      rwa [funCode_funPack, funAdvice_funPack]
    exact ⟨funPack c q, ⟨f, h'⟩, RealizableFun.toFun_inj (advisedRealizes_unique
      (⟨f, h'⟩ : ∃ g : RealizableFun X Y, AdvisedRealizes X Y
        (Denumerable.ofNat OracleCode (funPack c q 0)) (fun n => funPack c q (n + 1))
        g.toFun).choose_spec h')⟩

/-- Names of the function space are exactly advised realization of the underlying function
by the head-decoded code and the tail advice. -/
@[simp]
theorem funRep_names_iff {F : Baire} {f : RealizableFun X Y} :
    (funRep X Y).Names F f ↔
      AdvisedRealizes X Y (Denumerable.ofNat OracleCode (F 0)) (fun n => F (n + 1))
        f.toFun := by
  constructor
  · rintro ⟨hex, rfl⟩
    exact hex.choose_spec
  · intro h
    exact ⟨⟨f, h⟩, RealizableFun.toFun_inj (advisedRealizes_unique
      (⟨f, h⟩ : ∃ g : RealizableFun X Y, AdvisedRealizes X Y
        (Denumerable.ofNat OracleCode (F 0)) (fun n => F (n + 1)) g.toFun).choose_spec h)⟩

/-- A packed name `funPack c q` names `f` whenever `(c, q)` advised-realizes its
underlying function. -/
private theorem names_funPack {c : OracleCode} {q : Baire} {f : RealizableFun X Y}
    (h : AdvisedRealizes X Y c q f.toFun) : (funRep X Y).Names (funPack c q) f := by
  refine funRep_names_iff.mpr ?_
  rwa [funCode_funPack, funAdvice_funPack]

/-! ### Evaluation is a computable map -/

/-- **Evaluation.** The application map on the function space is computable: from the
interleaved pair (function name, argument name), decode the head code index and run it —
via `OracleCode.exists_advisedEvalCode` — against the advice-interleaved argument name. -/
theorem computableMap_funRep_eval (X : Representation α) (Y : Representation β) :
    ComputableMap ((funRep X Y).prod X) Y fun p => p.1 p.2 := by
  obtain ⟨e, he⟩ := exists_advisedEvalCode
  refine ⟨e, fun r z hz => ?_⟩
  obtain ⟨hF, hp⟩ := Representation.prod_names_iff.mp hz
  obtain ⟨out, hout, hname⟩ := funRep_names_iff.mp hF r.oddPart z.2 hp
  refine ⟨out, mem_evalStream.mpr fun n => ?_, hname⟩
  rw [he r n]
  exact mem_evalStream.mp hout n

/-! ### Constant maps are computable points -/

/-- Every constant map is advice-realizable: any name of the value serves as advice, with
the even-track projection as the code. -/
private theorem exists_advised_const (X : Representation α) (Y : Representation β)
    (y : β) : ∃ c q, AdvisedRealizes X Y c q fun _ => y := by
  obtain ⟨s, hs⟩ := Y.onto y
  obtain ⟨c, hc⟩ := type2Computable_evenPart
  refine ⟨c, s, fun p a _ => ⟨s, ?_, hs⟩⟩
  rw [computes_iff_evalStream.mp hc (Baire.interleave s p), Baire.evenPart_interleave]
  exact Part.mem_some s

/-- **Constant point.** If `y` is a computable point of `Y`, the constant map at `y` is a
computable point of the function space: pack the even-track projection code with a
computable name of `y` as advice. -/
theorem RealizableFun.computablePoint_const {y : β} (hy : Y.ComputablePoint y) :
    (funRep X Y).ComputablePoint ⟨fun _ => y, exists_advised_const X Y y⟩ := by
  obtain ⟨s, hsc, hs⟩ := hy
  obtain ⟨c, hc⟩ := type2Computable_evenPart
  refine ⟨funPack c s, ?_, names_funPack fun p a _ => ⟨s, ?_, hs⟩⟩
  · exact Computable.nat_casesOn Computable.id (Computable.const _)
      (hsc.comp Computable.snd).to₂
  · rw [computes_iff_evalStream.mp hc (Baire.interleave s p), Baire.evenPart_interleave]
    exact Part.mem_some s

/-! ### Postcomposition by a fixed computable map -/

/-- Postcomposition on the carrier: for a computable map `g`, the composite `g ∘ f` of an
advice-realizable map `f` is advice-realizable — substitute a realizer of `g` over `f`'s
code, keeping the same advice. -/
def RealizableFun.postcomp {g : β → γ} (hg : ComputableMap Y Z g) (f : RealizableFun X Y) :
    RealizableFun X Z where
  toFun := g ∘ f.toFun
  exists_advised := by
    obtain ⟨c, q, h⟩ := f.exists_advised
    obtain ⟨cg, hcg⟩ := hg
    refine ⟨cg.subst c, q, fun p a hp => ?_⟩
    obtain ⟨out, hout, hname⟩ := h p a hp
    obtain ⟨out', hout', hname'⟩ := hcg out (f.toFun a) hname
    exact ⟨out', (evalStream_subst hout).symm ▸ hout', hname'⟩

/-- Prepending a fixed head to a stream is Type-2 computable (totally, on all streams),
via the head-adaptive prefix bridge `OracleCode.exists_prefixPostCode`. -/
private theorem exists_consCode (c : OracleCode) :
    ∃ e : OracleCode, e.Computes (funPack c) := by
  have hb : Primrec₂ fun (n _ : ℕ) => n := Primrec₂.left
  have hg : Primrec fun v : ℕ =>
      if v.unpair.1 = 0 then Encodable.encode c
      else ((Denumerable.ofNat (List ℕ) v.unpair.2)[v.unpair.1 - 1]?).getD 0 := by
    have h1 : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
    have h2 : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
    exact Primrec.ite (Primrec.eq.comp h1 (Primrec.const 0))
      (Primrec.const (Encodable.encode c))
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp ((Primrec.ofNat (List ℕ)).comp h2)
          (Primrec.nat_sub.comp h1 (Primrec.const 1)))
        (Primrec.const 0))
  obtain ⟨e, he⟩ := exists_prefixPostCode hb hg
  refine ⟨e, fun F n => ?_⟩
  rw [he F n]
  congr 1
  cases n with
  | zero => simp [funPack]
  | succ m =>
    simp only [Nat.unpair_pair, Denumerable.ofNat_encode, Nat.add_sub_cancel,
      Nat.succ_ne_zero, if_false]
    rw [getElem?_streamTake_of_lt F (Nat.lt_succ_self m)]
    rfl

/-- **Postcomposition.** For a fixed computable map `g : Y → Z`, the induced map on
function spaces `f ↦ g ∘ f` is computable: the image name has a *fixed* head — the code
index of `cg.subst e`, for `cg` a realizer of `g` and `e` the advised-evaluation code —
and the entire input name as advice. -/
theorem computableMap_funRep_postcomp {g : β → γ} (hg : ComputableMap Y Z g) :
    ComputableMap (funRep X Y) (funRep X Z) (RealizableFun.postcomp hg) := by
  obtain ⟨cg, hcg⟩ := hg
  obtain ⟨e, he⟩ := exists_advisedEvalCode
  obtain ⟨cc, hcc⟩ := exists_consCode (cg.subst e)
  refine ⟨cc, .of_computes hcc fun F f hF => ?_⟩
  refine names_funPack fun p a hp => ?_
  obtain ⟨out, hout, hname⟩ := funRep_names_iff.mp hF p a hp
  have hout' : out ∈ e.evalStream (Baire.interleave F p) := by
    refine mem_evalStream.mpr fun n => ?_
    rw [he, Baire.evenPart_interleave, Baire.oddPart_interleave]
    exact mem_evalStream.mp hout n
  obtain ⟨out', hout2, hname'⟩ := hcg out (f.toFun a) hname
  refine ⟨out', ?_, hname'⟩
  rw [evalStream_subst hout']
  exact hout2

end ComputableAnalysis
