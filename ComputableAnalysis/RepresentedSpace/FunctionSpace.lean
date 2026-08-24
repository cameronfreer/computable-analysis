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
* `exists_funPackCode`: one oracle code emits the packed name `funPack c₀ a` from the
  stream `a` alone — the emitter for postprocessors whose output is a function name.

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
def funPack (c : OracleCode) (q : Baire) : Baire :=
  fun n => n.casesOn (Encodable.encode c) q

/-- Decoding the head of a packed name recovers the code. -/
theorem funCode_funPack (c : OracleCode) (q : Baire) :
    Denumerable.ofNat OracleCode (funPack c q 0) = c := by
  have h : funPack c q 0 = Encodable.encode c := rfl
  rw [h, Denumerable.ofNat_encode]

/-- The shifted tail of a packed name recovers the advice. -/
theorem funAdvice_funPack (c : OracleCode) (q : Baire) :
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
theorem names_funPack {c : OracleCode} {q : Baire} {f : RealizableFun X Y}
    (h : AdvisedRealizes X Y c q f.toFun) : (funRep X Y).Names (funPack c q) f := by
  refine funRep_names_iff.mpr ?_
  rwa [funCode_funPack, funAdvice_funPack]

/-! ### The head-cons name emitter -/

/-- **The head-cons name emitter.** A single oracle code produces the packed function name
`funPack c₀ a` from the stream `a` alone, for one fixed code `c₀`: coordinate `0` returns
the constant `Encodable.encode c₀`, and coordinate `n + 1` returns `a n`, read off the
length-`(n + 1)` prefix. Total on every stream.

This is the emitter a postprocessor uses when its output is a function name. Because the
emitted name mentions only the fixed code and the stream it is handed, a reduction whose
postprocessor is this code depends on nothing but that stream — which is what makes such a
reduction strong. -/
theorem exists_funPackCode (c₀ : OracleCode) :
    ∃ H : OracleCode, ∀ a : Baire, funPack c₀ a ∈ H.evalStream a := by
  have hidx : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hlst : Primrec fun v : ℕ => v.unpair.2 := Primrec.snd.comp Primrec.unpair
  have hg : Primrec fun v : ℕ =>
      if v.unpair.1 = 0 then Encodable.encode c₀
      else ((Denumerable.ofNat (List ℕ) v.unpair.2)[v.unpair.1 - 1]?).getD 0 :=
    Primrec.ite (Primrec.eq.comp hidx (Primrec.const 0)) (Primrec.const _)
      (Primrec.option_getD.comp
        (Primrec.list_getElem?.comp ((Primrec.ofNat (List ℕ)).comp hlst)
          (Primrec.nat_sub.comp hidx (Primrec.const 1)))
        (Primrec.const 0))
  obtain ⟨H, hH⟩ := OracleCode.exists_prefixPostCode (b := fun n _ => n) Primrec.fst hg
  refine ⟨H, fun a => OracleCode.mem_evalStream.mpr fun n => ?_⟩
  rw [hH a n]
  refine Part.mem_some_iff.mpr ?_
  cases n with
  | zero => simp [funPack]
  | succ m =>
      have hlen : m < m + 1 := Nat.lt_succ_self m
      simp only [Nat.unpair_pair, Nat.succ_ne_zero, Denumerable.ofNat_encode,
        Nat.add_sub_cancel, getElem?_streamTake_of_lt a hlen, Option.getD_some]
      rfl

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
      Nat.succ_ne_zero, ite_false]
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

/-! ### Currying -/

/-- Currying on the carrier: for a computable map `f` out of the product, each section
`f (a, ·)` is advice-realizable — a realizer of `f` is the code and any name of `a` the
advice, because the advice-interleaved oracle `Baire.interleave advice argument` *is* the
product packing of a name of `a` with a name of the argument. -/
def RealizableFun.curry {f : α × β → γ} (hf : ComputableMap (X.prod Y) Z f) (a : α) :
    RealizableFun Y Z where
  toFun b := f (a, b)
  exists_advised := by
    obtain ⟨c, hc⟩ := hf
    obtain ⟨p, hp⟩ := X.onto a
    have hp' : X.Names p a := hp
    refine ⟨c, p, fun q b hq => ?_⟩
    exact hc (Baire.interleave p q) (a, b)
      (Representation.prod_names_iff.mpr ⟨by simpa using hp', by simpa using hq⟩)

/-- **Currying.** For a computable map `f` out of the product, the curried map into the
function space is computable. The realizer is a *pure repackaging*: the image name of `a`
under a name `p` is `funPack c p` — fixed head the code index of `f`'s realizer `c`,
advice the whole of `p` — because `AdvisedRealizes` runs `c` on
`Baire.interleave advice argument`, which is exactly the product packing of `p` with a
name of the argument. -/
theorem computableMap_funRep_curry {f : α × β → γ}
    (hf : ComputableMap (X.prod Y) Z f) :
    ComputableMap X (funRep Y Z) (RealizableFun.curry hf) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨cc, hcc⟩ := exists_consCode c
  refine ⟨cc, .of_computes hcc fun p a hp => ?_⟩
  refine names_funPack fun q b hq => ?_
  exact hc (Baire.interleave p q) (a, b)
    (Representation.prod_names_iff.mpr ⟨by simpa using hp, by simpa using hq⟩)

/-- The computable-point form of currying: at a computable point `a`, the section
`f (a, ·)` is a computable point of the function space. -/
theorem RealizableFun.computablePoint_curry {f : α × β → γ}
    (hf : ComputableMap (X.prod Y) Z f) {a : α} (ha : X.ComputablePoint a) :
    (funRep Y Z).ComputablePoint (RealizableFun.curry hf a) :=
  (computableMap_funRep_curry hf).computablePoint ha

/-! ### Calibration: computable points of the function space are the computable maps -/

/-- **Calibration.** A computable point of the function space is exactly a function that
is a computable map: (→) precompose the head-decoded code with the
interleave-computable-advice operator; (←) pack `c.subst oddTrackCode` with an all-zeros
advice stream. -/
theorem funRep_computablePoint_iff {f : RealizableFun X Y} :
    (funRep X Y).ComputablePoint f ↔ ComputableMap X Y f.toFun := by
  constructor
  · rintro ⟨F, hFc, hF⟩
    have hadv := funRep_names_iff.mp hF
    have hq : Computable fun n => F (n + 1) := hFc.comp Computable.succ
    have hid : Type2Computable (id : Baire → Baire) := ⟨.query, fun p n => eval_query p n⟩
    have hint : Type2Computable fun p : Baire => Baire.interleave (fun n => F (n + 1)) p :=
      Type2Computable.interleave (type2Computable_const_stream hq) hid
    obtain ⟨m, hm⟩ := hint
    refine ⟨(Denumerable.ofNat OracleCode (F 0)).subst m, fun p a hpa => ?_⟩
    obtain ⟨r, hr, hname⟩ := hadv p a hpa
    refine ⟨r, ?_, hname⟩
    rw [evalStream_subst (Part.eq_some_iff.mp (computes_iff_evalStream.mp hm p))]
    exact hr
  · rintro ⟨c, hc⟩
    obtain ⟨od, hod⟩ := type2Computable_oddPart
    have hF : AdvisedRealizes X Y (c.subst od) (fun _ => 0) f.toFun := by
      intro p a hpa
      obtain ⟨r, hr, hname⟩ := hc p a hpa
      have hmem : p ∈ od.evalStream (Baire.interleave (fun _ => 0) p) := by
        have h := computes_iff_evalStream.mp hod (Baire.interleave (fun _ => 0) p)
        rw [Baire.oddPart_interleave] at h
        exact Part.eq_some_iff.mp h
      exact ⟨r, (evalStream_subst hmem).symm ▸ hr, hname⟩
    refine ⟨fun n => n.casesOn (Encodable.encode (c.subst od)) fun _ => 0, ?_, ?_⟩
    · exact Computable.nat_casesOn Computable.id (Computable.const _)
        ((Computable.const 0).comp Computable.snd).to₂
    · refine funRep_names_iff.mpr ?_
      change AdvisedRealizes X Y
        (Denumerable.ofNat OracleCode (Encodable.encode (c.subst od))) (fun _ : ℕ => 0)
        f.toFun
      rw [Denumerable.ofNat_encode]
      exact hF

end ComputableAnalysis
