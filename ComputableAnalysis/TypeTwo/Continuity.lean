/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Evaln

/-!
# Finite use, the stream layer, and continuity

A converging evaluation `y ∈ c.eval p n` reaches its value at some fuel `k`, and a
run at fuel `k` reads only oracle coordinates below `k`. This gives the **finite use**
theorem `eval_eq_of_agree_on_use`: the value depends on only finitely many oracle
coordinates.

The **stream layer** lifts the coordinatewise primitive to stream operators:
`OracleCode.Computes c F` says `c` computes the total stream map `F` on every stream,
`OracleCode.evalStream` is the partial stream value on valid names, and
`Type2Computable F` is the uniform existence of a single computing code.

Finite use yields **continuity**: every `Type2Computable` operator is continuous for the
product topology on Baire space (each factor `ℕ` discrete). This is the *default* topology
(`ℕ` is discrete in mathlib), so it needs no scoped instances; only the later *metric*
structure is scoped per convention 11's non-global metric discipline.

The stream layer is closed under **composition** via oracle substitution. The primitive is
the *pointwise* substitution law `evalStream_subst`, which needs the inner code to converge
only on the given valid name; the globally total `eval_subst` and `Type2Computable.comp`
are corollaries. `mem_evalStream` characterizes stream membership coordinatewise, and the
`Computes`/`evalStream` equivalence packages the total and partial views.
-/

namespace ComputableAnalysis

namespace OracleCode

/-! ### Finite use -/

/-- **Finite use.** A converging evaluation depends on only finitely many oracle
coordinates: there is a finite set `u` of coordinates such that every stream `q`
agreeing with `p` on `u` yields the same value. Derived from `evalnPrefix`: a run at
fuel `k` reads only coordinates `< k`, so `u = Finset.range k` works. -/
theorem eval_eq_of_agree_on_use {c : OracleCode} {p : Baire} {n y : ℕ}
    (h : y ∈ c.eval p n) :
    ∃ u : Finset ℕ, ∀ q : Baire, (∀ i ∈ u, q i = p i) → y ∈ c.eval q n := by
  obtain ⟨k, hk⟩ := evalnPrefix_complete.mp h
  refine ⟨Finset.range k, fun q hq => evalnPrefix_complete.mpr ⟨k, ?_⟩⟩
  have hst : streamTake q k = streamTake p k := by
    refine List.ext_getElem (by simp [length_streamTake]) fun i h1 _ => ?_
    rw [getElem_streamTake, getElem_streamTake,
      hq i (Finset.mem_range.mpr (by simpa [length_streamTake] using h1))]
  rwa [hst]

/-! ### Stream layer -/

/-- `c` computes the total stream operator `F`: on every stream `p`, coordinate `n` of
the output is `F p n`. -/
def Computes (c : OracleCode) (F : Baire → Baire) : Prop :=
  ∀ p n, c.eval p n = Part.some (F p n)

/-- The partial stream value of `c` on `p`: defined exactly when every output coordinate
converges, with value the coordinatewise `get`. -/
def evalStream (c : OracleCode) (p : Baire) : Part Baire :=
  ⟨∀ n, (c.eval p n).Dom, fun h n => (c.eval p n).get (h n)⟩

/-- The total-stream view and the partial-stream view agree: `c` computes `F` iff its
stream value on every `p` is exactly `F p`. -/
theorem computes_iff_evalStream {c : OracleCode} {F : Baire → Baire} :
    c.Computes F ↔ ∀ p, c.evalStream p = Part.some (F p) := by
  constructor
  · intro h p
    refine Part.eq_some_iff.mpr ⟨fun n => by rw [h p n]; exact trivial, funext fun n => ?_⟩
    change (c.eval p n).get _ = F p n
    rw [Part.get_eq_iff_mem, h p n]; exact Part.mem_some _
  · intro h p n
    have hmem : F p ∈ c.evalStream p := (h p).symm ▸ Part.mem_some _
    obtain ⟨hdom, hval⟩ := hmem
    exact Part.eq_some_iff.mpr (congrFun hval n ▸ Part.get_mem (hdom n))

/-- **Pointwise membership in the stream value.** `q` is the stream value of `c` on `p`
exactly when every output coordinate of `q` is the coordinatewise evaluation value. This is
the partial-realizer primitive: it characterizes `evalStream` on *valid* names without any
global totality assumption. -/
theorem mem_evalStream {c : OracleCode} {p q : Baire} :
    q ∈ c.evalStream p ↔ ∀ n, q n ∈ c.eval p n := by
  constructor
  · rintro ⟨hdom, hval⟩ n
    exact congrFun hval n ▸ Part.get_mem (hdom n)
  · intro h
    exact ⟨fun n => Part.dom_iff_mem.mpr ⟨q n, h n⟩,
      funext fun n => Part.get_eq_of_mem (h n) _⟩

/-- Substitute `cg` for every `query` in `cf`, inlining a code that computes the oracle. -/
def subst : OracleCode → OracleCode → OracleCode
  | zero, _ => zero
  | succ, _ => succ
  | left, _ => left
  | right, _ => right
  | query, cg => cg
  | pair a b, cg => pair (a.subst cg) (b.subst cg)
  | comp a b, cg => comp (a.subst cg) (b.subst cg)
  | prec a b, cg => prec (a.subst cg) (b.subst cg)
  | rfind' a, cg => rfind' (a.subst cg)

/-- **Pointwise oracle substitution.** On a *single* input `p`, if `cg` produces the stream
`q` there (`cg.eval p = ↑q`), then substituting `cg` for the oracle in `cf` runs `cf`
against `q`. This is the valid-name substitution law: it needs `cg` to converge only on `p`
(to `q`), not to be a globally total operator. Substitution therefore ignores divergent
coordinates of the inner computation outside `p`. -/
theorem eval_subst_of_eval {cg : OracleCode} {p q : Baire}
    (h : cg.eval p = fun n => Part.some (q n)) (cf : OracleCode) :
    (cf.subst cg).eval p = cf.eval q := by
  induction cf with
  | zero => rfl
  | succ => rfl
  | left => rfl
  | right => rfl
  | query =>
      change cg.eval p = query.eval q
      rw [h]; funext n; exact (eval_query q n).symm
  | pair a b iha ihb => funext n; simp only [subst, eval_pair, iha, ihb]
  | comp a b iha ihb => funext n; simp only [subst, eval_comp, iha, ihb]
  | prec a b iha ihb => funext n; simp only [subst, OracleCode.eval, iha, ihb]
  | rfind' a iha => funext n; simp only [subst, OracleCode.eval, iha]

/-- **Oracle substitution law** (globally total form). If `cg` computes the total stream map
`G`, then substituting `cg` for the oracle in `cf` evaluates `cf` against the stream `G p`.
A corollary of the pointwise `eval_subst_of_eval` with `q := G p`. -/
theorem eval_subst {cg : OracleCode} {G : Baire → Baire} (hg : cg.Computes G)
    (cf : OracleCode) (p : Baire) : (cf.subst cg).eval p = cf.eval (G p) :=
  eval_subst_of_eval (q := G p) (funext fun n => hg p n) cf

/-- **Pointwise substitution on stream values.** If `cg` produces the stream `q` on `p`
(i.e. `q` is a valid stream value of `cg` at `p`), then the stream value of `cf.subst cg`
at `p` is exactly the stream value of `cf` at `q`. This is the composition law the
represented-map layer uses: an inner realizer converges on a valid name to `q`, and the
outer code then runs on `q`. -/
theorem evalStream_subst {cf cg : OracleCode} {p q : Baire} (hq : q ∈ cg.evalStream p) :
    (cf.subst cg).evalStream p = cf.evalStream q := by
  have hpe : cg.eval p = fun n => Part.some (q n) :=
    funext fun n => Part.eq_some_iff.mpr (mem_evalStream.mp hq n)
  have hsub : (cf.subst cg).eval p = cf.eval q := eval_subst_of_eval hpe cf
  ext r
  simp only [mem_evalStream, hsub]

/-- **Pointwise output pairing.** There is a code-level pairing operator `pairCode` such that
whenever `cf` produces the stream `q` on `p` and `cg` produces `r` on `p` (both as valid
stream values), the paired code `pairCode cf cg` produces `Baire.interleave q r` on `p`. The
witness interleaves the two outputs coordinatewise; it needs convergence only at the shared
input `p`, so the represented-space product layer can reuse it without reconstructing the
oracle plumbing. -/
theorem exists_pairStreams :
    ∃ pairCode : OracleCode → OracleCode → OracleCode,
      ∀ (cf cg : OracleCode) (p q r : Baire),
        q ∈ cf.evalStream p → r ∈ cg.evalStream p →
        Baire.interleave q r ∈ (pairCode cf cg).evalStream p := by
  obtain ⟨half, hhalf⟩ :
      ∃ e : OracleCode, ∀ (p : Baire) (n : ℕ), e.eval p n = Part.some (n / 2) := by
    obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1
      ((Primrec.nat_div.comp Primrec.id (Primrec.const 2)).to_comp).partrec
    exact ⟨ofPartrecCode E, fun p n => by rw [eval_ofPartrecCode, hE]; simp⟩
  obtain ⟨sel, hsel⟩ : ∃ e : OracleCode, ∀ (p : Baire) (w : ℕ),
      e.eval p w = Part.some (((Nat.unpair w).1 % 2).casesOn
        (Nat.unpair (Nat.unpair w).2).1 (fun _ => (Nat.unpair (Nat.unpair w).2).2)) := by
    have hpar := Primrec.nat_mod.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2)
    have hab := Primrec.snd.comp Primrec.unpair
    have ha := Primrec.fst.comp (Primrec.unpair.comp hab)
    have hb := Primrec.snd.comp (Primrec.unpair.comp hab)
    obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1
      ((Primrec.nat_casesOn hpar ha (hb.comp Primrec.fst).to₂).to_comp).partrec
    exact ⟨ofPartrecCode E, fun p w => by rw [eval_ofPartrecCode, hE]; simp⟩
  refine ⟨fun cf cg => OracleCode.comp sel (pair OracleCode.id
    (pair (OracleCode.comp cf half) (OracleCode.comp cg half))), ?_⟩
  intro cf cg p q r hq hr
  have hqe : ∀ m, cf.eval p m = Part.some (q m) :=
    fun m => Part.eq_some_iff.mpr (mem_evalStream.mp hq m)
  have hre : ∀ m, cg.eval p m = Part.some (r m) :=
    fun m => Part.eq_some_iff.mpr (mem_evalStream.mp hr m)
  refine mem_evalStream.mpr fun n => ?_
  have h1 : (OracleCode.comp cf half).eval p n = Part.some (q (n / 2)) := by
    rw [eval_comp, hhalf, Part.bind_eq_bind, Part.bind_some]; exact hqe (n / 2)
  have h2 : (OracleCode.comp cg half).eval p n = Part.some (r (n / 2)) := by
    rw [eval_comp, hhalf, Part.bind_eq_bind, Part.bind_some]; exact hre (n / 2)
  have h3 : (pair OracleCode.id
      (pair (OracleCode.comp cf half) (OracleCode.comp cg half))).eval p n
      = Part.some (Nat.pair n (Nat.pair (q (n / 2)) (r (n / 2)))) := by
    rw [eval_pair, eval_id, eval_pair, h1, h2]; simp [Seq.seq, Part.map_some, Part.bind_some]
  have h4 : (OracleCode.comp sel (pair OracleCode.id
      (pair (OracleCode.comp cf half) (OracleCode.comp cg half)))).eval p n
      = Part.some (Baire.interleave q r n) := by
    rw [eval_comp, h3, Part.bind_eq_bind, Part.bind_some, hsel]
    simp only [Nat.unpair_pair, Baire.interleave]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
  rw [h4]; exact Part.mem_some _

/-- The output-pairing code combinator, extracted once from `exists_pairStreams` so every
consumer shares a single combinator. Specified, not constructed: the helper codes inside
`exists_pairStreams` come from `Nat.Partrec.Code.exists_code` (Prop-level), so the
combinator is choice-extracted and opaque — only properties following from
`pairCode_spec` can be proved about it. If a later unit needs more (say a converse
convergence law), strengthen `exists_pairStreams` and re-extract. -/
noncomputable def pairCode : OracleCode → OracleCode → OracleCode :=
  Classical.choose exists_pairStreams

/-- Specification of `pairCode`: whenever `cf` produces the stream `q` on `p` and `cg`
produces `r` on `p`, the paired code produces their interleaving on `p`. -/
theorem pairCode_spec {cf cg : OracleCode} {p q r : Baire} (hq : q ∈ cf.evalStream p)
    (hr : r ∈ cg.evalStream p) :
    Baire.interleave q r ∈ (pairCode cf cg).evalStream p :=
  Classical.choose_spec exists_pairStreams cf cg p q r hq hr

end OracleCode

/-- A stream operator is **Type-2 computable** when a single finite code computes it on
every stream (uniformity: `∃ code, ∀ p`). -/
def Type2Computable (F : Baire → Baire) : Prop :=
  ∃ c : OracleCode, c.Computes F

/-- **Composition closure.** Type-2 computable operators compose, realized by oracle
substitution: the code for `F` is run against the code for `G` supplying the oracle. This
is foundational API for represented maps and Weihrauch reductions. -/
theorem Type2Computable.comp {F G : Baire → Baire} (hF : Type2Computable F)
    (hG : Type2Computable G) : Type2Computable (F ∘ G) := by
  obtain ⟨cf, hcf⟩ := hF
  obtain ⟨cg, hcg⟩ := hG
  exact ⟨cf.subst cg, fun p n => by rw [OracleCode.eval_subst hcg cf p]; exact hcf (G p) n⟩

/-- **Output-pairing closure.** If `F` and `G` are Type-2 computable, so is the map that
interleaves their outputs. A corollary of the code-level `OracleCode.exists_pairStreams`;
foundational for products in the represented-space layer. -/
theorem Type2Computable.interleave {F G : Baire → Baire} (hF : Type2Computable F)
    (hG : Type2Computable G) : Type2Computable (fun p => Baire.interleave (F p) (G p)) := by
  obtain ⟨cf, hcf⟩ := hF
  obtain ⟨cg, hcg⟩ := hG
  refine ⟨OracleCode.pairCode cf cg, fun p n => ?_⟩
  have hqF : F p ∈ cf.evalStream p :=
    Part.eq_some_iff.mp (OracleCode.computes_iff_evalStream.mp hcf p)
  have hrG : G p ∈ cg.evalStream p :=
    Part.eq_some_iff.mp (OracleCode.computes_iff_evalStream.mp hcg p)
  exact Part.eq_some_iff.mpr
    (OracleCode.mem_evalStream.mp (OracleCode.pairCode_spec hqF hrG) n)

/-! ### Computable stream operators consumed by the represented-space layer -/

open OracleCode in
/-- **Constant to a computable stream.** For any computable output stream `s`, the constant
map `_ ↦ s` is Type-2 computable. Generalizes the constant-value case to an arbitrary
computable point. -/
theorem type2Computable_const_stream {s : Baire} (hs : Computable s) :
    Type2Computable (fun _ : Baire => s) := by
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1 hs.partrec
  exact ⟨ofPartrecCode E, fun p n => by rw [eval_ofPartrecCode, hE]; simp⟩

open OracleCode in
/-- A query composed with a computable index map is Type-2 computable. -/
theorem type2Computable_query_comp {g : ℕ → ℕ} (hg : Computable g) :
    Type2Computable (fun p : Baire => fun n => p (g n)) := by
  obtain ⟨E, hE⟩ := Nat.Partrec.Code.exists_code.1 hg.partrec
  refine ⟨comp query (ofPartrecCode E), fun p n => ?_⟩
  have hEn : (ofPartrecCode E).eval p n = Part.some (g n) := by rw [eval_ofPartrecCode, hE]; simp
  rw [eval_comp, hEn, Part.bind_eq_bind, Part.bind_some, eval_query]

/-- The even-track deinterleaving projection is Type-2 computable. -/
theorem type2Computable_evenPart : Type2Computable Baire.evenPart :=
  type2Computable_query_comp ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).to_comp)

/-- The odd-track deinterleaving projection is Type-2 computable. -/
theorem type2Computable_oddPart : Type2Computable Baire.oddPart :=
  type2Computable_query_comp
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
      (Primrec.const 1)).to_comp)

/-! ### Fixed deinterleaving codes

The two projections above are extracted once into shared constants, the same pattern as
`OracleCode.pairCode`: specified, not constructed, so only properties following from the
`evalStream` specifications can be proved about them. They give the reduction-witness
calculus fixed named codes in place of per-proof `obtain`s from the existentials. -/

/-- The fixed even-track deinterleaving code, extracted once from
`type2Computable_evenPart`. -/
noncomputable def OracleCode.evenCode : OracleCode :=
  Classical.choose type2Computable_evenPart

/-- Specification of `OracleCode.evenCode`: its stream value at `p` is `p.evenPart`. -/
theorem OracleCode.evalStream_evenCode (p : Baire) :
    OracleCode.evenCode.evalStream p = Part.some p.evenPart :=
  OracleCode.computes_iff_evalStream.mp (Classical.choose_spec type2Computable_evenPart) p

/-- The fixed odd-track deinterleaving code, extracted once from
`type2Computable_oddPart`. -/
noncomputable def OracleCode.oddCode : OracleCode :=
  Classical.choose type2Computable_oddPart

/-- Specification of `OracleCode.oddCode`: its stream value at `p` is `p.oddPart`. -/
theorem OracleCode.evalStream_oddCode (p : Baire) :
    OracleCode.oddCode.evalStream p = Part.some p.oddPart :=
  OracleCode.computes_iff_evalStream.mp (Classical.choose_spec type2Computable_oddPart) p

/-- On an interleaved stream, `OracleCode.evenCode` recovers the first component. -/
theorem OracleCode.evalStream_evenCode_interleave (p q : Baire) :
    OracleCode.evenCode.evalStream (Baire.interleave p q) = Part.some p := by
  rw [evalStream_evenCode, Baire.evenPart_interleave]

/-- On an interleaved stream, `OracleCode.oddCode` recovers the second component. -/
theorem OracleCode.evalStream_oddCode_interleave (p q : Baire) :
    OracleCode.oddCode.evalStream (Baire.interleave p q) = Part.some q := by
  rw [evalStream_oddCode, Baire.oddPart_interleave]

/-! ### Continuity

Baire space carries the default product topology (each factor `ℕ` discrete); the scoped
`PiNat` *metric* discipline of convention 11 is not needed here, only the topology.
-/

open Topology in
/-- **Continuity.** Every Type-2 computable operator is continuous for the product
topology on Baire space (each factor discrete). Each output coordinate is locally
constant by finite use, hence continuous. -/
theorem type2Computable_continuous {F : Baire → Baire} (h : Type2Computable F) :
    Continuous F := by
  obtain ⟨c, hc⟩ := h
  refine continuous_pi fun i => continuous_iff_continuousAt.mpr fun p₀ => ?_
  have hy : F p₀ i ∈ c.eval p₀ i := hc p₀ i ▸ Part.mem_some _
  obtain ⟨u, hu⟩ := OracleCode.eval_eq_of_agree_on_use hy
  have hnhds : {q : Baire | ∀ j ∈ u, q j = p₀ j} ∈ 𝓝 p₀ := by
    refine IsOpen.mem_nhds ?_ (fun _ _ => rfl)
    have hset : {q : Baire | ∀ j ∈ u, q j = p₀ j}
        = ⋂ j ∈ u, (fun q : Baire => q j) ⁻¹' {p₀ j} := by
      ext q; simp
    rw [hset]
    exact isOpen_biInter_finset fun j _ =>
      (continuous_apply j).isOpen_preimage _ (isOpen_discrete _)
  have heq : (fun _ : Baire => F p₀ i) =ᶠ[𝓝 p₀] fun q => F q i :=
    Filter.eventually_of_mem hnhds fun q hq => Part.mem_some_iff.mp (hc q i ▸ hu q hq)
  exact continuousAt_const.congr heq

end ComputableAnalysis
