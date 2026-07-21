/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Continuity
import ComputableAnalysis.TypeTwo.Evaln
import Mathlib.Computability.RecursiveIn

/-!
# Universal oracle evaluator, s-m-n, and the fixed-oracle `RecursiveIn` bridge

Built on the bounded simulation `evalnPrefix` (and its Baire-facing `evaln`), this
file establishes the operational core of the oracle machine model, uniformly in the
oracle (`∃ code, ∀ p, …`):

* `OracleCode.exists_universal`: a single universal code that runs an encoded code on
  the same oracle.
* `OracleCode.smn`: an explicit computable specialization function (the s-m-n theorem),
  witnessed by `curry`.
* `OracleCode.eval_comp_eq`: the explicit-witness composition equation.
* `OracleCode.exists_code_iff_recursiveIn`: at a fixed oracle `p`, a partial function
  has an oracle code iff it is recursive in the singleton oracle `{↑p}`.

The uniformity discipline is load-bearing: `∀ p, Nat.RecursiveIn {↑p} (F p)` does **not**
characterize Type-2 computability of `F` — the code witness stays outside `∀ p`. The
`exists_code_iff_recursiveIn` bridge is therefore stated at a *fixed* oracle and used
only semantically.
-/

open Encodable Denumerable

namespace ComputableAnalysis

namespace OracleCode

/-! ### s-m-n and composition -/

/-- The **s-m-n theorem**: an explicit computable function specializing an encoded code
in its first pair-argument, witnessed numerically by `curry`. -/
theorem smn :
    ∃ s : ℕ → ℕ → ℕ, Computable₂ s ∧
      ∀ (c : OracleCode) (m : ℕ) (p : Baire) (n : ℕ),
        (ofNat OracleCode (s (encode c) m)).eval p n = c.eval p (Nat.pair m n) := by
  refine ⟨fun a m => encode (curry (ofNat OracleCode a) m), ?_, ?_⟩
  · exact Primrec₂.to_comp
      (Primrec.encode.comp
        (primrec₂_curry.comp ((Primrec.ofNat OracleCode).comp Primrec.fst) Primrec.snd))
  · intro c m p n
    rw [Denumerable.ofNat_encode, Denumerable.ofNat_encode, eval_curry]

/-- The composition equation as an explicit-witness equality of oracle-relative partial
functions (the pointwise `eval_comp` of unit 2 packaged with Kleisli composition). -/
theorem eval_comp_eq (f g : OracleCode) (p : Baire) :
    (comp f g).eval p = f.eval p <=< g.eval p := by
  funext n
  exact eval_comp f g p n

/-! ### Fixed-oracle `RecursiveIn` correspondence -/

/-- The `rfind'` closure of `Nat.RecursiveIn`, ported from `Nat.Partrec.rfind'`. Oracle
codes minimize with the `rfind'` convention, but `Nat.RecursiveIn` exposes only plain
`rfind`; this bridges the two for the code → `RecursiveIn` direction. Kept private: it is
proof plumbing, not public API. -/
private theorem recursiveIn_rfind' {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ}
    (hf : Nat.RecursiveIn O f) :
    Nat.RecursiveIn O (Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun x => x = 0) <$> f (Nat.pair a (n + m))).map (· + m)) := by
  have hρ : Nat.Primrec fun q => Nat.pair (Nat.unpair (Nat.unpair q).1).1
      ((Nat.unpair q).2 + (Nat.unpair (Nat.unpair q).1).2) :=
    Primrec.nat_iff.1 <| Primrec₂.natPair.comp
      (Primrec.fst.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair)
      (Primrec.nat_add.comp (Primrec.snd.comp Primrec.unpair)
        (Primrec.snd.comp <| Primrec.unpair.comp <| Primrec.fst.comp Primrec.unpair))
  have hf' : Nat.RecursiveIn O fun q => f (Nat.pair (Nat.unpair (Nat.unpair q).1).1
      ((Nat.unpair q).2 + (Nat.unpair (Nat.unpair q).1).2)) :=
    (Nat.RecursiveIn.comp hf hρ.recursiveIn).of_eq fun q => by simp
  have hsnd : Nat.Primrec fun p => (Nat.unpair p).2 :=
    Primrec.nat_iff.1 (Primrec.snd.comp Primrec.unpair)
  have hadd : Nat.Primrec fun z => (Nat.unpair z).1 + (Nat.unpair z).2 :=
    Primrec.nat_iff.1 (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.snd.comp Primrec.unpair))
  refine (Nat.RecursiveIn.comp hadd.recursiveIn
    (Nat.RecursiveIn.pair hsnd.recursiveIn (Nat.RecursiveIn.rfind hf'))).of_eq fun p => ?_
  simp [Nat.unpaired, Nat.unpair_pair, Seq.seq, Part.bind_some_eq_map, Part.map_map,
    Function.comp_def, add_comm]

/-- Code → recursive-in: the evaluation of any oracle code at a fixed oracle `p` is
recursive in the singleton oracle `{↑p}`. The `query` constructor supplies the oracle
leaf; `rfind'` uses the ported closure `recursiveIn_rfind'`. -/
private theorem recursiveIn_of_code (p : Baire) (c : OracleCode) :
    Nat.RecursiveIn {(p : ℕ →. ℕ)} (c.eval p) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | query => exact .oracle _ rfl
  | pair cf cg ihf ihg => exact ihf.pair ihg
  | comp cf cg ihf ihg => exact ihf.comp ihg
  | prec cf cg ihf ihg => exact ihf.prec ihg
  | rfind' cf ihf => exact recursiveIn_rfind' ihf

/-- Recursive-in → code: any function recursive in `{↑p}` is the evaluation of some
oracle code at `p`. The oracle leaf becomes `query`; plain `rfind` becomes the derived
`OracleCode.rfind`. -/
private theorem code_of_recursiveIn (p : Baire) (f : ℕ →. ℕ)
    (hf : Nat.RecursiveIn {(p : ℕ →. ℕ)} f) : ∃ c : OracleCode, c.eval p = f := by
  induction hf with
  | zero => exact ⟨zero, rfl⟩
  | succ => exact ⟨succ, rfl⟩
  | left => exact ⟨left, rfl⟩
  | right => exact ⟨right, rfl⟩
  | oracle g hg =>
    rw [Set.mem_singleton_iff] at hg
    exact ⟨query, by funext n; rw [hg]; rfl⟩
  | pair _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf; obtain ⟨cg, rfl⟩ := ihg
    exact ⟨pair cf cg, rfl⟩
  | comp _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf; obtain ⟨cg, rfl⟩ := ihg
    exact ⟨comp cf cg, rfl⟩
  | prec _ _ ihf ihg =>
    obtain ⟨cf, rfl⟩ := ihf; obtain ⟨cg, rfl⟩ := ihg
    exact ⟨prec cf cg, rfl⟩
  | rfind _ ihf =>
    obtain ⟨cf, rfl⟩ := ihf
    exact ⟨OracleCode.rfind cf, funext fun a => eval_rfind cf p a⟩

/-- **Fixed-oracle correspondence.** At a fixed oracle `p`, a partial function has an
oracle code iff it is recursive in the singleton oracle `{↑p}`. Used only semantically:
the code witness stays outside any `∀ p`, per the uniformity discipline. -/
theorem exists_code_iff_recursiveIn (p : Baire) (f : ℕ →. ℕ) :
    (∃ c : OracleCode, c.eval p = f) ↔ Nat.RecursiveIn {(p : ℕ →. ℕ)} f :=
  ⟨fun ⟨_, hc⟩ => hc ▸ recursiveIn_of_code p _, code_of_recursiveIn p f⟩

/-! ### Universal evaluator -/

section Universal

open Primrec

/-- An oracle-free code appending one element at the end of an encoded list. -/
theorem exists_snocCode :
    ∃ e : OracleCode, ∀ (P : Baire) (x : ℕ) (l : List ℕ),
      e.eval P (Nat.pair x (encode l)) = Part.some (encode (l ++ [x])) := by
  have hcomp : Computable fun q : ℕ × List ℕ => q.2 ++ [q.1] :=
    (Primrec.list_append.comp Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const []))).to_comp
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1 hcomp.partrec
  refine ⟨ofPartrecCode E, fun P x l => ?_⟩
  rw [eval_ofPartrecCode, hE]
  simp

/-- An oracle code producing the encoded length-`k` prefix of the oracle stream, by
querying coordinate `k` at each `prec` step and snoc-encoding. -/
theorem exists_takeCode :
    ∃ t : OracleCode, ∀ (P : Baire) (k : ℕ),
      t.eval P k = Part.some (encode (streamTake P k)) := by
  obtain ⟨e, he⟩ := exists_snocCode
  refine ⟨comp (prec (OracleCode.const (encode ([] : List ℕ)))
      (comp e (pair (comp query (comp left right)) (comp right right))))
      (pair (OracleCode.const 0) OracleCode.id), fun P k => ?_⟩
  have hin : (pair (OracleCode.const 0) OracleCode.id).eval P k = Part.some (Nat.pair 0 k) := by
    simp [Seq.seq]
  rw [eval_comp, hin, Part.bind_eq_bind, Part.bind_some]
  clear hin
  induction k with
  | zero => simp [eval_prec_zero, eval_const, streamTake]
  | succ k ih =>
    rw [eval_prec_succ, ih, Part.bind_eq_bind, Part.bind_some]
    simp only [eval_comp, eval_pair, eval_query, eval_left, eval_right, Seq.seq, Part.bind_eq_bind,
      Part.bind_some, Part.map_some, Part.map_eq_map, Nat.unpair_pair]
    rw [he P (P k) (streamTake P k), streamTake_succ]

/-- The per-fuel simulation as an oracle code: on input `Nat.pair m k` it queries the
oracle (via `takeCode`) to build `streamTake P k`, then runs the bounded simulation of
the code `ofNat OracleCode m.1` on input `m.2`, returning the encoded `Option`. -/
private theorem exists_bodyCode :
    ∃ b : OracleCode, ∀ (P : Baire) (m k : ℕ),
      b.eval P (Nat.pair m k) = Part.some (encode (evalnPrefix k
        (ofNat OracleCode (Nat.unpair m).1) (streamTake P k) (Nat.unpair m).2)) := by
  obtain ⟨t, ht⟩ := exists_takeCode
  have hbody : Computable fun v : ℕ =>
      evalnPrefix (Nat.unpair (Nat.unpair v).2).2
        (ofNat OracleCode (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).1)
        (ofNat (List ℕ) (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).2 := by
    have hW : Primrec fun v : ℕ => (Nat.unpair v).2 := Primrec.snd.comp Primrec.unpair
    have hT : Primrec fun v : ℕ => (Nat.unpair v).1 := Primrec.fst.comp Primrec.unpair
    have hm : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair v).2).1 :=
      Primrec.fst.comp (Primrec.unpair.comp hW)
    have hk : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair v).2).2 :=
      Primrec.snd.comp (Primrec.unpair.comp hW)
    have hm1 : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).1 :=
      Primrec.fst.comp (Primrec.unpair.comp hm)
    have hm2 : Primrec fun v : ℕ => (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).2 :=
      Primrec.snd.comp (Primrec.unpair.comp hm)
    exact (primrec_evalnPrefix.comp
      ((hk.pair ((Primrec.ofNat OracleCode).comp hm1)).pair
        (((Primrec.ofNat (List ℕ)).comp hT).pair hm2))).to_comp
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1 hbody.partrec
  refine ⟨comp (ofPartrecCode E) (pair (comp t right) OracleCode.id), fun P m k => ?_⟩
  rw [eval_comp, eval_pair]
  simp only [eval_comp, eval_right, eval_id, Seq.seq, Part.bind_eq_bind, Part.bind_some,
    Nat.unpair_pair, Part.map_some, Part.map_eq_map, ht P k, eval_ofPartrecCode, hE]
  simp [Nat.unpair_pair, Denumerable.ofNat_encode]

/-- An oracle-free code for a computable unary numeric function. -/
theorem exists_ofNatFnCode {g : ℕ → ℕ} (hg : Computable g) :
    ∃ e : OracleCode, ∀ (P : Baire) (v : ℕ), e.eval P v = Part.some (g v) := by
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1 hg.partrec
  refine ⟨ofPartrecCode E, fun P v => ?_⟩
  rw [eval_ofPartrecCode, hE]
  simp

/-- **Head-adaptive finite-use bridge.** Any stream operator of the shape
`F ↦ (n ↦ g (Nat.pair n (encode (streamTake F (b n (F 0))))))` — an oracle-free
postprocessor `g` of a stream prefix whose length is computed from the coordinate `n` and
the head `F 0` — is computed by a single oracle code, **totally on all streams**. The
assembly lemma behind uniform first-order arithmetic on packed names (unit 16). -/
theorem exists_prefixPostCode {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ}
    (hb : Primrec₂ b) (hg : Primrec g) :
    ∃ c : OracleCode, ∀ (F : Baire) (n : ℕ),
      c.eval F n = Part.some (g (Nat.pair n (encode (streamTake F (b n (F 0)))))) := by
  obtain ⟨t, ht⟩ := exists_takeCode
  obtain ⟨B, hB⟩ := exists_ofNatFnCode (g := fun v => b v.unpair.1 v.unpair.2)
    (hb.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  obtain ⟨G, hG⟩ := exists_ofNatFnCode hg.to_comp
  refine ⟨.comp G (.pair OracleCode.id (.comp t (.comp B
    (.pair OracleCode.id (.comp .query .zero))))), fun F n => ?_⟩
  have h0 : (OracleCode.comp .query .zero).eval F n = Part.some (F 0) :=
    (eval_comp_some rfl).trans (eval_query F 0)
  have hbc : (OracleCode.comp B (.pair OracleCode.id (.comp .query .zero))).eval F n
      = Part.some (b n (F 0)) := by
    rw [eval_comp_some (eval_pair_some (eval_id F n) h0), hB]
    simp
  rw [eval_comp_some (eval_pair_some (eval_id F n)
    (eval_comp_some hbc ▸ ht F (b n (F 0)))), hG]

theorem exists_universal :
    ∃ u : OracleCode, ∀ (c : OracleCode) (p : Baire) (n : ℕ),
      u.eval p (Nat.pair (encode c) n) = c.eval p n := by
  obtain ⟨b, hb⟩ := exists_bodyCode
  obtain ⟨flag, hflag⟩ := exists_ofNatFnCode (g := fun v => 1 - v)
    (Primrec.nat_sub.comp (Primrec.const 1) Primrec.id).to_comp
  obtain ⟨sub, hsub⟩ := exists_ofNatFnCode (g := fun v => v - 1)
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp
  refine ⟨comp sub (comp b (pair OracleCode.id (rfind (comp flag b)))), fun c P n => ?_⟩
  set m := Nat.pair (encode c) n with hm
  set f : ℕ → Option ℕ := fun k => evalnPrefix k c (streamTake P k) n with hfdef
  have hbmk : ∀ k, b.eval P (Nat.pair m k) = Part.some (encode (f k)) := fun k => by
    rw [hb P m k, hm]; simp only [Nat.unpair_pair, Denumerable.ofNat_encode, hfdef]
  -- an isSome option is recovered from its (shifted) encoding
  have hopt : ∀ {o : Option ℕ}, o.isSome → o = some (encode o - 1) := by
    rintro (_ | x) h
    · simp at h
    · simp
  -- the fuel search finds the least converging fuel
  have hsearch : (rfind (comp flag b)).eval P m =
      Nat.rfind fun k => (↑(f k).isSome : Part Bool) := by
    rw [eval_rfind]; congr 1; funext k
    rw [eval_comp, hbmk k, Part.bind_eq_bind, Part.bind_some, hflag P (encode (f k))]
    cases f k <;> simp
  -- evaluation as an `rfindOpt` over the bounded simulation
  have heval : c.eval P n = Nat.rfindOpt f := by
    refine Part.ext fun x => evalnPrefix_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m₁ m₂ hle ha
    exact evalnPrefix_mono hle (streamTake_prefix P hle) ha
  -- reduce the universal code to the fuel search followed by decoding
  have hlhs : (comp sub (comp b (pair OracleCode.id (rfind (comp flag b))))).eval P m
      = (rfind (comp flag b)).eval P m >>= fun k => Part.some (encode (f k) - 1) := by
    rw [eval_comp, eval_comp, eval_pair, eval_id]
    simp only [Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_eq_bind, Part.bind_assoc,
      Part.bind_map, Part.bind_some, hbmk, hsub]
  rw [hlhs, hsearch, heval, Nat.rfindOpt]
  refine Part.ext fun x => ?_
  simp only [Part.bind_eq_bind, Part.mem_bind_iff]
  refine exists_congr fun k => and_congr_right fun hk => ?_
  have hks : (f k).isSome := by simpa using Nat.rfind_spec hk
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hks
  simp [hy]

end Universal

/-! ### The advised-evaluation code -/

/-- **The advised-evaluation code.** A single code that, on every oracle `r`, decodes a
code index from the head of the even track and runs the decoded code — via the universal
machine — against the remaining even track (the *advice*) interleaved with the odd track
(the argument). Total plumbing: the identity holds at every `r` and `n`. This is the
Type-2 engine of the represented function space: a function name head-cons-packs a code
index and an advice stream, and evaluation reads that pack off the even track of a
product name. -/
theorem exists_advisedEvalCode :
    ∃ e : OracleCode, ∀ (r : Baire) (n : ℕ),
      e.eval r n = (Denumerable.ofNat OracleCode (r.evenPart 0)).eval
        (Baire.interleave (fun k => r.evenPart (k + 1)) r.oddPart) n := by
  obtain ⟨u, hu⟩ := exists_universal
  -- the advised oracle is `r` read through a fixed computable reindexing: even
  -- coordinates shift past the head, odd coordinates are untouched
  obtain ⟨cG, hcG⟩ := type2Computable_query_comp (g := fun m => if m % 2 = 0 then m + 2 else m)
    (Primrec.ite
      (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 0))
      (Primrec.nat_add.comp Primrec.id (Primrec.const 2)) Primrec.id).to_comp
  refine ⟨.comp (u.subst cG) (.pair (.comp .query (.const 0)) .id), fun r n => ?_⟩
  have h0 : (OracleCode.comp .query (.const 0)).eval r n = Part.some (r 0) :=
    (eval_comp_some (eval_const r 0 n)).trans (eval_query r 0)
  have hinp : (OracleCode.pair (.comp .query (.const 0)) OracleCode.id).eval r n
      = Part.some (Nat.pair (r 0) n) := eval_pair_some h0 (eval_id r n)
  have hsub : (u.subst cG).eval r = u.eval fun m => r (if m % 2 = 0 then m + 2 else m) :=
    eval_subst hcG u r
  have hhead : r 0 = encode (Denumerable.ofNat OracleCode (r.evenPart 0)) := by simp
  have hadv : Baire.interleave (fun k => r.evenPart (k + 1)) r.oddPart
      = fun m => r (if m % 2 = 0 then m + 2 else m) := by
    funext m
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · rw [Baire.interleave_even, if_pos (Nat.mul_mod_right 2 k)]
      rfl
    · rw [Baire.interleave_odd, if_neg (by omega)]
      rfl
  rw [eval_comp_some hinp, hsub, hhead, hu, hadv]

/-! ### The three-stage adaptive prefix chain -/

/-- **Three-stage adaptive prefix-chain bridge.** Any stream operator that reads a
prefix of primitively computed length `b₀ n`, recomputes a longer prefix length `b₁`
from the coordinate and that encoded prefix, recomputes once more through `b₂`, and
postprocesses with an oracle-free `g`, is computed by a single oracle code, **totally
on all streams**. This strictly generalizes `exists_prefixPostCode` (whose adaptation
sees only the head `F 0`): here each stage's bound is recomputed from the previous
stage's entire encoded prefix. Built from the same primitives — `exists_takeCode`,
`exists_ofNatFnCode`, and the `eval_comp_some`/`eval_pair_some` assembly steps. -/
theorem exists_prefixChainCode {b₀ : ℕ → ℕ} {b₁ b₂ : ℕ → ℕ → ℕ} {g : ℕ → ℕ}
    (hb₀ : Primrec b₀) (hb₁ : Primrec₂ b₁) (hb₂ : Primrec₂ b₂) (hg : Primrec g) :
    ∃ c : OracleCode, ∀ (F : Baire) (n : ℕ),
      c.eval F n = Part.some (g (Nat.pair n (encode (streamTake F
        (b₂ n (encode (streamTake F
          (b₁ n (encode (streamTake F (b₀ n))))))))))) := by
  obtain ⟨t, ht⟩ := exists_takeCode
  obtain ⟨B₀, hB₀⟩ := exists_ofNatFnCode hb₀.to_comp
  obtain ⟨B₁, hB₁⟩ := exists_ofNatFnCode
    (g := fun v => b₁ v.unpair.1 v.unpair.2)
    (hb₁.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  obtain ⟨B₂, hB₂⟩ := exists_ofNatFnCode
    (g := fun v => b₂ v.unpair.1 v.unpair.2)
    (hb₂.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp
  obtain ⟨G, hG⟩ := exists_ofNatFnCode hg.to_comp
  refine ⟨.comp G (.pair OracleCode.id (.comp t (.comp B₂ (.pair OracleCode.id
    (.comp t (.comp B₁ (.pair OracleCode.id (.comp t B₀)))))))), fun F n => ?_⟩
  have e₀ : (OracleCode.comp t B₀).eval F n
      = Part.some (encode (streamTake F (b₀ n))) :=
    (eval_comp_some (hB₀ F n)).trans (ht F (b₀ n))
  have p₁ : (OracleCode.pair OracleCode.id (.comp t B₀)).eval F n
      = Part.some (Nat.pair n (encode (streamTake F (b₀ n)))) :=
    eval_pair_some (eval_id F n) e₀
  have q₁ : (OracleCode.comp B₁ (.pair OracleCode.id (.comp t B₀))).eval F n
      = Part.some (b₁ n (encode (streamTake F (b₀ n)))) := by
    rw [eval_comp_some p₁, hB₁]
    simp
  have e₁ : (OracleCode.comp t (.comp B₁ (.pair OracleCode.id (.comp t B₀)))).eval F n
      = Part.some (encode (streamTake F (b₁ n (encode (streamTake F (b₀ n)))))) :=
    (eval_comp_some q₁).trans (ht F _)
  have p₂ : (OracleCode.pair OracleCode.id
        (.comp t (.comp B₁ (.pair OracleCode.id (.comp t B₀))))).eval F n
      = Part.some (Nat.pair n
          (encode (streamTake F (b₁ n (encode (streamTake F (b₀ n))))))) :=
    eval_pair_some (eval_id F n) e₁
  have q₂ : (OracleCode.comp B₂ (.pair OracleCode.id
        (.comp t (.comp B₁ (.pair OracleCode.id (.comp t B₀)))))).eval F n
      = Part.some (b₂ n (encode (streamTake F (b₁ n (encode (streamTake F (b₀ n))))))) := by
    rw [eval_comp_some p₂, hB₂]
    simp
  have e₂ : (OracleCode.comp t (.comp B₂ (.pair OracleCode.id
        (.comp t (.comp B₁ (.pair OracleCode.id (.comp t B₀))))))).eval F n
      = Part.some (encode (streamTake F
          (b₂ n (encode (streamTake F (b₁ n (encode (streamTake F (b₀ n))))))))) :=
    (eval_comp_some q₂).trans (ht F _)
  have p₃ : (OracleCode.pair OracleCode.id (.comp t (.comp B₂ (.pair OracleCode.id
        (.comp t (.comp B₁ (.pair OracleCode.id (.comp t B₀)))))))).eval F n
      = Part.some (Nat.pair n (encode (streamTake F
          (b₂ n (encode (streamTake F (b₁ n (encode (streamTake F (b₀ n)))))))))) :=
    eval_pair_some (eval_id F n) e₂
  rw [eval_comp_some p₃, hG]

end OracleCode

end ComputableAnalysis
