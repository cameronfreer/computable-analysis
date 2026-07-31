/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecContainers
import ComputableAnalysis.Weihrauch.Reduction
import ComputableAnalysis.Weihrauch.Principles.LPO

/-!
# The limit problem and the reduction `LPO ≤W Lim`

`Lim` receives a table `p` of columns — `p (Nat.pair n t)` is the stage-`t` entry of
column `n` — with every column eventually constant, and must output the stream of column
limits. The limit stream is unique (`Lim.accepts_unique`), so `Lim` is single-valued on
its domain.

`lpo_le_lim` reduces `LPO` to `Lim`: the preprocessor sends a stream `p` to the table
whose column `n` at stage `t` records whether a nonzero entry appears among
`p 0, …, p t` — computed uniformly by the head-adaptive prefix bridge
`OracleCode.exists_prefixPostCode`, testing the prefix via its list sum — and the
postprocessor reads coordinate `0` of the limit stream, which stabilizes to the `LPO`
answer bit.

`limTable` is the generic table for reductions that need the input together with its jump:
even columns echo the input and odd columns carry the bounded-simulation halting bit at the
stage. `limTable_dom` places it in the domain of `Lim`, and `exists_limTableCode` produces
it by a single oracle code, so any `_ ≤sW Lim` whose oracle need is the jump can take its
preprocessor from here. Routing the input through the answer is what leaves the
postprocessor free of it, hence what makes such a reduction strong.
-/

open Encodable Denumerable

namespace ComputableAnalysis

/-- **The limit problem** on Baire space: the input is a table of columns
(`p (Nat.pair n t)` is the stage-`t` entry of column `n`), each eventually constant, and
the accepted answer is the stream of column limits. -/
def Lim : Problem baireSpace baireSpace :=
  ⟨fun p (q : Baire) => ∀ n, ∃ s, ∀ t, s ≤ t → p (Nat.pair n t) = q n⟩

/-- **Definitional unfolding of `Lim.accepts`.** An explicit rewrite lemma, deliberately
not a global `simp` rule. -/
theorem Lim.accepts_iff {p q : Baire} :
    Lim.accepts p q ↔ ∀ n, ∃ s, ∀ t, s ≤ t → p (Nat.pair n t) = q n :=
  Iff.rfl

/-- The limit stream is unique: `Lim` is single-valued on its domain. Evaluate both
stabilization stages of column `n` at their maximum and chain the equalities. -/
theorem Lim.accepts_unique {p q q' : Baire} (h : Lim.accepts p q) (h' : Lim.accepts p q') :
    q = q' := by
  funext n
  obtain ⟨s, hs⟩ := Lim.accepts_iff.mp h n
  obtain ⟨s', hs'⟩ := Lim.accepts_iff.mp h' n
  exact (hs (max s s') (le_max_left _ _)).symm.trans (hs' (max s s') (le_max_right _ _))

/-- A list of naturals sums to zero iff every entry vanishes. -/
private theorem list_sum_eq_zero {l : List ℕ} : l.sum = 0 ↔ ∀ x ∈ l, x = 0 := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The length-`(t + 1)` prefix of a stream sums to zero iff the stream vanishes up to
time `t`: the entries of `streamTake p (t + 1)` are exactly `p 0, …, p t`. -/
private theorem streamTake_sum_eq_zero {p : Baire} {t : ℕ} :
    (streamTake p (t + 1)).sum = 0 ↔ ∀ k ≤ t, p k = 0 := by
  rw [list_sum_eq_zero]
  constructor
  · intro h k hk
    exact h (p k) (List.mem_ofFn.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, rfl⟩)
  · intro h x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact h i (Nat.lt_succ_iff.mp i.isLt)

/-- The preprocessed table for `lpo_le_lim`: column `n` at stage `t` — coordinate
`Nat.pair n t` — is `1` if a nonzero entry appears among `p 0, …, p t`, else `0`. Every
column is eventually constant with limit the `LPO` answer bit. -/
private def limInput (p : Baire) : Baire := fun m =>
  if (streamTake p (m.unpair.2 + 1)).sum = 0 then 0 else 1

/-- The table entry is `0` when the input vanishes up to the stage. -/
private theorem limInput_eq_zero {p : Baire} {m : ℕ} (h : ∀ k ≤ m.unpair.2, p k = 0) :
    limInput p m = 0 :=
  if_pos (streamTake_sum_eq_zero.mpr h)

/-- The table entry is `1` once a nonzero input entry has appeared by the stage. -/
private theorem limInput_eq_one {p : Baire} {m k : ℕ} (hk : k ≤ m.unpair.2)
    (hpk : p k ≠ 0) : limInput p m = 1 :=
  if_neg fun hsum => hpk (streamTake_sum_eq_zero.mp hsum k hk)

/-- The postprocessor `comp query (const 1)`: on any oracle `r` its stream value is the
constant stream at `r 1` — coordinate `1` of the interleaved input is the oracle answer's
coordinate `0`. (Restated here because the copy in `LLPO.lean` is private to that file.) -/
private theorem const_query_one_mem_evalStream (r : Baire) :
    (fun _ => r 1 : Baire) ∈ (OracleCode.comp .query (.const 1)).evalStream r := by
  refine OracleCode.mem_evalStream.mpr fun n => ?_
  rw [OracleCode.eval_comp_some (OracleCode.eval_const r 1 n), OracleCode.eval_query]
  exact Part.mem_some _

/-- **`LPO ≤W Lim`.** Preprocess a stream `p` into the table whose column `n` at stage
`t` flags whether a nonzero entry appears among `p 0, …, p t` (uniformly, by the
head-adaptive prefix bridge with the list-sum test); every column stabilizes to the `LPO`
answer bit, so postprocessing reads coordinate `0` of the limit stream. -/
theorem lpo_le_lim : LPO ≤W Lim := by
  -- The preprocessor: a total code computing `limInput`, via the prefix bridge.
  have hb : Primrec₂ fun (n : ℕ) (_ : ℕ) => n.unpair.2 + 1 :=
    (Primrec.succ.comp ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)).to₂
  have hl : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)
  have hsum : Primrec fun v : ℕ => (ofNat (List ℕ) v.unpair.2).sum := primrec_list_sum hl
  have hg : Primrec fun v : ℕ => if (ofNat (List ℕ) v.unpair.2).sum = 0 then 0 else 1 :=
    Primrec.ite (Primrec.eq.comp hsum (Primrec.const 0)) (Primrec.const 0) (Primrec.const 1)
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hb hg
  refine reduction_iff_exists_reductionPair.mpr
    ⟨K, .comp .query (.const 1), fun p x hpx hdom => ?_⟩
  obtain rfl := (baireRep_names_iff.mp hpx).symm
  have hKp : limInput p ∈ K.evalStream p := by
    refine OracleCode.mem_evalStream.mpr fun m => ?_
    rw [hK p m]
    simp only [Nat.unpair_pair, Denumerable.ofNat_encode, Part.mem_some_iff, limInput]
  -- The table is in the domain of `Lim`: every column stabilizes.
  have hdomL : Lim.Dom (limInput p) := by
    by_cases hz : ∀ k, p k = 0
    · exact ⟨(fun _ => 0 : Baire), Lim.accepts_iff.mpr fun n =>
        ⟨0, fun t _ => limInput_eq_zero fun k _ => hz k⟩⟩
    · obtain ⟨k₀, hk₀⟩ := not_forall.mp hz
      exact ⟨(fun _ => 1 : Baire), Lim.accepts_iff.mpr fun n =>
        ⟨k₀, fun t ht => limInput_eq_one (by rw [Nat.unpair_pair]; exact ht) hk₀⟩⟩
  refine ⟨limInput p, hKp, limInput p, baireRep_names_iff.mpr rfl, hdomL,
    fun a y' hay' hacc => ?_⟩
  have heq : y' = a := baireRep_names_iff.mp hay'
  subst y'
  have h1 : Baire.interleave p a 1 = a 0 := by simpa using Baire.interleave_odd p a 0
  refine ⟨fun _ => Baire.interleave p a 1, const_query_one_mem_evalStream _, a 0,
    natRep_names_iff.mpr h1.symm, ?_⟩
  -- Column `0` of the table stabilizes to `a 0`; case on whether `p` vanishes.
  obtain ⟨s, hs⟩ := Lim.accepts_iff.mp hacc 0
  by_cases hz : ∀ k, p k = 0
  · have ha0 : a 0 = 0 :=
      (hs s le_rfl).symm.trans (limInput_eq_zero fun k _ => hz k)
    exact LPO.accepts_iff.mpr (Or.inl ⟨ha0, hz⟩)
  · obtain ⟨k₀, hk₀⟩ := not_forall.mp hz
    have ha1 : a 0 = 1 :=
      (hs (max s k₀) (le_max_left _ _)).symm.trans
        (limInput_eq_one (by rw [Nat.unpair_pair]; exact le_max_right _ _) hk₀)
    exact LPO.accepts_iff.mpr (Or.inr ⟨ha1, k₀, hk₀⟩)

/-! ### The reduce-to-`Lim` input/jump table

The table a reduction hands to `Lim` when what it needs from the oracle is its own input
together with the input's jump. Even columns echo the input, so the answer carries it and
the postprocessor never has to revisit it — the move that makes such a reduction strong.
Odd columns run the bounded simulation for one more stage, so they are monotone and
`{0,1}`-valued, hence eventually constant with limit the halting bit.
-/

/-- The jump bit: `1` when the `e`-th oracle code, run against the length-`t` prefix of `p`
with fuel `t` on input `e`, has halted, and `0` otherwise. -/
def jumpBit (p : Baire) (e t : ℕ) : ℕ :=
  (OracleCode.evalnPrefix t (ofNat OracleCode e) (streamTake p t) e).isSome.toNat

/-- The jump bit is a bit. -/
theorem jumpBit_cases (p : Baire) (e t : ℕ) : jumpBit p e t = 0 ∨ jumpBit p e t = 1 := by
  unfold jumpBit
  cases (OracleCode.evalnPrefix t (ofNat OracleCode e) (streamTake p t) e).isSome <;> simp

/-- The jump column is monotone in the stage: once halted, always halted, since the bounded
simulation is monotone in the fuel and under prefix extension simultaneously. -/
theorem jumpBit_mono (p : Baire) (e : ℕ) {t t' : ℕ} (htt : t ≤ t')
    (h1 : jumpBit p e t = 1) : jumpBit p e t' = 1 := by
  simp only [jumpBit, Bool.toNat_eq_one, Option.isSome_iff_exists] at h1 ⊢
  obtain ⟨y, hy⟩ := h1
  exact ⟨y, OracleCode.evalnPrefix_mono htt (streamTake_prefix p htt) hy⟩

/-- **The input/jump table.** Coordinate `Nat.pair col t` is the stage-`t` entry of column
`col`: even columns echo the input entry `p (col / 2)`, constant in the stage; odd columns
carry `jumpBit p (col / 2) t`. -/
def limTable (p : Baire) : Baire := fun m =>
  if m.unpair.1 % 2 = 0 then p (m.unpair.1 / 2) else jumpBit p (m.unpair.1 / 2) m.unpair.2

/-- **The table lies in the domain of `Lim`.** Echo columns are constant in the stage; jump
columns are monotone and `{0,1}`-valued, so they stabilize either at the first halting stage
or at `0` forever. -/
theorem limTable_dom (p : Baire) : Lim.Dom (limTable p) := by
  have hcol : ∀ n : ℕ, ∃ ln : ℕ, ∃ s : ℕ, ∀ t, s ≤ t → limTable p (Nat.pair n t) = ln := by
    intro n
    by_cases hpar : n % 2 = 0
    · exact ⟨p (n / 2), 0, fun t _ => by simp only [limTable, Nat.unpair_pair, if_pos hpar]⟩
    · by_cases hhalt : ∃ t, jumpBit p (n / 2) t = 1
      · obtain ⟨t₀, ht₀⟩ := hhalt
        refine ⟨1, t₀, fun t ht => ?_⟩
        simp only [limTable, Nat.unpair_pair, if_neg hpar]
        exact jumpBit_mono p (n / 2) ht ht₀
      · have hnone := not_exists.mp hhalt
        refine ⟨0, 0, fun t _ => ?_⟩
        simp only [limTable, Nat.unpair_pair, if_neg hpar]
        rcases jumpBit_cases p (n / 2) t with h0 | h1
        · exact h0
        · exact absurd h1 (hnone t)
  exact ⟨fun n => (hcol n).choose, fun n => (hcol n).choose_spec⟩

/-- The oracle-free postprocessor behind `exists_limTableCode`: from the coordinate paired
with an encoded prefix of the input, read the echoed entry off the prefix on even columns,
and run the bounded simulation against the prefix truncated to the stage on odd ones. -/
private def limTableStep (v : ℕ) : ℕ :=
  if v.unpair.1.unpair.1 % 2 = 0 then
    ((ofNat (List ℕ) v.unpair.2)[v.unpair.1.unpair.1 / 2]?).getD 0
  else
    (OracleCode.evalnPrefix v.unpair.1.unpair.2
      (ofNat OracleCode (v.unpair.1.unpair.1 / 2))
      ((ofNat (List ℕ) v.unpair.2).take v.unpair.1.unpair.2)
      (v.unpair.1.unpair.1 / 2)).isSome.toNat

private theorem primrec_limTableStep : Primrec limTableStep := by
  have hcoord : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hcol : Primrec fun v : ℕ => v.unpair.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp hcoord)
  have hstage : Primrec fun v : ℕ => v.unpair.1.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp hcoord)
  have hidx : Primrec fun v : ℕ => v.unpair.1.unpair.1 / 2 :=
    Primrec.nat_div.comp hcol (Primrec.const 2)
  have hlist : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)
  have hecho : Primrec fun v : ℕ =>
      ((ofNat (List ℕ) v.unpair.2)[v.unpair.1.unpair.1 / 2]?).getD 0 :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp hlist hidx) (Primrec.const 0)
  have hsim : Primrec fun v : ℕ =>
      OracleCode.evalnPrefix v.unpair.1.unpair.2 (ofNat OracleCode (v.unpair.1.unpair.1 / 2))
        ((ofNat (List ℕ) v.unpair.2).take v.unpair.1.unpair.2) (v.unpair.1.unpair.1 / 2) :=
    OracleCode.primrec_evalnPrefix.comp
      ((hstage.pair ((Primrec.ofNat OracleCode).comp hidx)).pair
        ((Primrec.list_take.comp hstage hlist).pair hidx))
  have hjump : Primrec fun v : ℕ =>
      (OracleCode.evalnPrefix v.unpair.1.unpair.2 (ofNat OracleCode (v.unpair.1.unpair.1 / 2))
        ((ofNat (List ℕ) v.unpair.2).take v.unpair.1.unpair.2)
        (v.unpair.1.unpair.1 / 2)).isSome.toNat := by
    refine (Primrec.ite (Primrec.eq.comp (Primrec.option_isSome.comp hsim) (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)).of_eq fun v => ?_
    cases h : (OracleCode.evalnPrefix v.unpair.1.unpair.2
      (ofNat OracleCode (v.unpair.1.unpair.1 / 2))
      ((ofNat (List ℕ) v.unpair.2).take v.unpair.1.unpair.2)
      (v.unpair.1.unpair.1 / 2)).isSome <;> simp
  exact Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp hcol (Primrec.const 2)) (Primrec.const 0))
    hecho hjump

/-- **The table is produced by a single oracle code**, on every input stream. Both tracks
read a finite prefix of the input — the echo track needs the entry itself, the jump track
the length-`t` prefix the bounded simulation may query — so one prefix long enough for both
suffices, and the head-adaptive prefix bridge assembles the code. -/
theorem exists_limTableCode : ∃ K : OracleCode, ∀ p : Baire, limTable p ∈ K.evalStream p := by
  have hb : Primrec₂ fun (m : ℕ) (_ : ℕ) => max (m.unpair.1 / 2 + 1) m.unpair.2 :=
    (Primrec.nat_max.comp
      (Primrec.succ.comp (Primrec.nat_div.comp
        ((Primrec.fst.comp Primrec.unpair).comp Primrec.fst) (Primrec.const 2)))
      ((Primrec.snd.comp Primrec.unpair).comp Primrec.fst)).to₂
  obtain ⟨K, hK⟩ := OracleCode.exists_prefixPostCode hb primrec_limTableStep
  refine ⟨K, fun p => OracleCode.mem_evalStream.mpr fun m => ?_⟩
  rw [hK p m]
  refine Part.mem_some_iff.mpr ?_
  have hlt : m.unpair.1 / 2 < max (m.unpair.1 / 2 + 1) m.unpair.2 :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hle : m.unpair.2 ≤ max (m.unpair.1 / 2 + 1) m.unpair.2 := le_max_right _ _
  by_cases hpar : m.unpair.1 % 2 = 0
  · simp only [limTable, limTableStep, Nat.unpair_pair, Denumerable.ofNat_encode, if_pos hpar,
      getElem?_streamTake_of_lt p hlt, Option.getD_some]
  · simp only [limTable, limTableStep, Nat.unpair_pair, Denumerable.ofNat_encode, if_neg hpar,
      take_streamTake p hle, jumpBit]

end ComputableAnalysis
