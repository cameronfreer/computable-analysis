/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.Eval

/-!
# Bounded simulation of oracle codes

`OracleCode.evalnPrefix fuel c oraclePrefix input` is a bounded approximation of
evaluation: it fails when the current computation encounters a value outside its
active bound or queries outside `oraclePrefix`. The bound controls encountered
inputs and intermediates and decreases through `prec`/`rfind'` (parallel
subcomputations can each receive the same bound) — the semantics inherited from
`Nat.Partrec.Code.evaln`, not a literal step count. It is a genuinely
executable, `Option`-valued function of `Primcodable` arguments.

Main results:

* `evalnPrefix_mono`: monotonicity in the fuel and under compatible prefix
  extension, in one statement.
* `evalnPrefix_sound`: a bounded run under a prefix of `p` is sound for
  `eval · p`.
* `evalnPrefix_complete`: every converging evaluation is reached at some fuel,
  with the length-`fuel` prefix as the oracle word.
* `primrec_evalnPrefix` / `computable_evalnPrefix`: the simulation is primitive
  recursive (hence computable) as a unary function of the packed product.

`OracleCode.evaln k c p n := evalnPrefix k c (streamTake p k) n` is the
Baire-facing convenience version: `evaln_sound` and `evaln_complete` connect it
to `eval`. This is the operational layer that later makes finite use effective
and justifies computable pushforward.
-/

open Encodable Denumerable

namespace ComputableAnalysis

namespace OracleCode

/-- Bounded simulation: a bounded approximation of evaluating `c` that fails
when the computation encounters a value outside its active bound (which
decreases through `prec`/`rfind'`) or queries outside the finite oracle word
`oraclePrefix`. Adapted from `Nat.Partrec.Code.evaln`. -/
def evalnPrefix : ℕ → OracleCode → List ℕ → ℕ → Option ℕ
  | 0, _, _ => fun _ => Option.none
  | k + 1, zero, _ => fun n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ, _ => fun n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left, _ => fun n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right, _ => fun n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, query, s => fun n => do
    guard (n ≤ k)
    s[n]?
  | k + 1, pair cf cg, s => fun n => do
    guard (n ≤ k)
    Nat.pair <$> evalnPrefix (k + 1) cf s n <*> evalnPrefix (k + 1) cg s n
  | k + 1, comp cf cg, s => fun n => do
    guard (n ≤ k)
    let x ← evalnPrefix (k + 1) cg s n
    evalnPrefix (k + 1) cf s x
  | k + 1, prec cf cg, s => fun n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evalnPrefix (k + 1) cf s a) fun y => do
        let i ← evalnPrefix k (prec cf cg) s (Nat.pair a y)
        evalnPrefix (k + 1) cg s (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf, s => fun n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evalnPrefix (k + 1) cf s (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evalnPrefix k (rfind' cf) s (Nat.pair a (m + 1))

/-- The Baire-facing bounded simulation: queries are answered from the
length-`k` prefix of the oracle stream. -/
def evaln (k : ℕ) (c : OracleCode) (p : Baire) (n : ℕ) : Option ℕ :=
  evalnPrefix k c (streamTake p k) n

theorem evalnPrefix_bound : ∀ {k c s n x}, x ∈ evalnPrefix k c s n → n < k
  | 0, c, _, n, x, h => by simp [evalnPrefix] at h
  | k + 1, c, s, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evalnPrefix] at h <;> exact this h
    intro o h'
    simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
      exists_and_left, exists_const] at h'
    exact Nat.lt_succ_of_le h'.1

private theorem mem_getElem?_mono {s t : List ℕ} (hst : s <+: t) {n x : ℕ}
    (h : x ∈ s[n]?) : x ∈ t[n]? := by
  obtain ⟨u, rfl⟩ := hst
  rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp h).1)]
  exact h

set_option linter.flexible false in
/-- Monotonicity of the bounded simulation, in the fuel and under compatible
prefix extension simultaneously. Adapted from `Nat.Partrec.Code.evaln_mono`. -/
theorem evalnPrefix_mono :
    ∀ {k₁ k₂ c s t n x}, k₁ ≤ k₂ → s <+: t →
      x ∈ evalnPrefix k₁ c s n → x ∈ evalnPrefix k₂ c t n
  | 0, k₂, c, _, _, n, x, _, _, h => by simp [evalnPrefix] at h
  | k + 1, k₂ + 1, c, s, t, n, x, hl, hst, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    induction c generalizing x n <;> rw [evalnPrefix] at h ⊢ <;>
      refine this hl' (fun h => ?_) h
    iterate 4 exact h
    case query => exact mem_getElem?_mono hst h
    case pair cf cg hf hg _ =>
      simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
        Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [Nat.unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evalnPrefix_mono hl' hst h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp only [Nat.unpaired, bind, Nat.pair_unpair, Option.pure_def, Option.mem_def,
        Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evalnPrefix_mono hl' hst

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
/-- Soundness: a bounded run whose oracle word is a prefix of the stream `p`
computes a value of `eval · p`. Adapted from `Nat.Partrec.Code.evaln_sound`. -/
theorem evalnPrefix_sound :
    ∀ {k c s n x} {p : Baire}, p ∈ cylinder s →
      x ∈ evalnPrefix k c s n → x ∈ c.eval p n
  | 0, _, _, n, x, _, _, h => by simp [evalnPrefix] at h
  | k + 1, c, s, n, x, p, hp, h => by
    induction c generalizing x n <;>
        simp [eval, evalnPrefix, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    case query =>
      obtain ⟨hn, rfl⟩ := List.getElem?_eq_some_iff.mp h
      exact (hp n hn).symm
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evalnPrefix_mono k.le_succ List.prefix_rfl h₁
          simp [evalnPrefix, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
      · have := evalnPrefix_sound hp h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

theorem evaln_sound {k c n x} {p : Baire} (h : x ∈ evaln k c p n) : x ∈ c.eval p n :=
  evalnPrefix_sound (mem_cylinder_streamTake p k) h

set_option backward.isDefEq.respectTransparency false in
set_option linter.flexible false in
/-- Completeness: every converging evaluation is reached by the bounded
simulation at some fuel, with the length-`fuel` prefix of the oracle stream as
the oracle word. Adapted from `Nat.Partrec.Code.evaln_complete`. -/
theorem evalnPrefix_complete {c n x} {p : Baire} :
    x ∈ c.eval p n ↔ ∃ k, x ∈ evalnPrefix k c (streamTake p k) n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evalnPrefix_sound (mem_cylinder_streamTake p k) h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evalnPrefix (k + 1) c (streamTake p (k + 1)) n
  · exact ⟨k + 1, h⟩
  have mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ →
      x ∈ evalnPrefix k₁ c (streamTake p k₁) n →
        x ∈ evalnPrefix k₂ c (streamTake p k₂) n :=
    fun hk => evalnPrefix_mono hk (streamTake_prefix p hk)
  induction c generalizing n x with
      simp [eval, evalnPrefix, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | query =>
    refine ⟨n, ⟨le_rfl, ?_⟩⟩
    rw [getElem?_streamTake_of_lt p n.lt_succ_self]
    exact congrArg some h.symm
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evalnPrefix_bound hk₁, _,
        mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evalnPrefix_bound hk₁, _,
        mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      intro y hy hx
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
          Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
          evalnPrefix_mono (Nat.succ_le_succ <| le_max_left _ _)
            (streamTake_prefix p (show k₁ + 1 ≤ (max k₁ k₂).succ + 1 by omega)) ?_,
          mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evalnPrefix.eq_9, bind, Nat.unpaired, Nat.unpair_pair, Option.mem_def,
        Option.bind_eq_some_iff, Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈
        evalnPrefix (k + 1) (rfind' cf) (streamTake p (k + 1))
          (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evalnPrefix, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evalnPrefix, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| evalnPrefix_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evalnPrefix_bound hk₁
      use a
      use mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evalnPrefix_mono (Nat.succ_le_succ <| le_max_right _ _)
          (streamTake_prefix p (show k₂ + 1 ≤ max k₁ k₂ + 2 by omega)) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

/-- Convergence of the Baire-facing bounded simulation. -/
theorem evaln_complete {c n x} {p : Baire} :
    x ∈ c.eval p n ↔ ∃ k, x ∈ evaln k c p n :=
  evalnPrefix_complete

/-! ### Computability of the bounded simulation

Adapted from the `Nat.Partrec.Code.primrec_evaln` construction: a course-of-values
table over encoded `(fuel, code)` pairs, with the oracle word riding along as the
parameter of `Primrec.nat_strong_rec`.
-/

section

open Primrec

/-- The evaluation table: entry `encode (k, c)` lists `evalnPrefix k c s n` for
`n < k`. -/
private def lup (L : List (List (Option ℕ))) (p : ℕ × OracleCode) (n : ℕ) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o

private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

private def G (s : List ℕ) (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × OracleCode) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        OracleCode.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (s[n]?) -- query
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (Nat.pair z y)
              lup L (k, cg) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c) (Nat.pair z (m + 1)))

set_option maxHeartbeats 1000000 in
-- the oracle-word parameter enlarges every product type in the adapted
-- `Nat.Partrec.Code` construction, so unification exceeds the default limit
private theorem hG : Primrec₂ G := by
  refine Primrec₂.mk ?_
  have a := (Primrec.ofNat (ℕ × OracleCode)).comp
    ((Primrec.list_length (α := List (Option ℕ))).comp (Primrec.snd (α := List ℕ)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp
    (Primrec.list_map (β := ℕ) (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := ℕ))
  have n := Primrec.snd (α := List ℕ × List (List (Option ℕ))) (β := ℕ)
  refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) (?_ : Primrec _)
  have k := k.comp (Primrec.fst (β := ℕ))
  have n := n.comp (Primrec.fst (β := ℕ))
  have k' := Primrec.snd (α := (List ℕ × List (List (Option ℕ))) × ℕ) (β := ℕ)
  have c := Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  apply OracleCode.primrec_recOn c
    (_root_.Primrec.const (some 0))
    (Primrec.option_some.comp (_root_.Primrec.succ.comp n))
    (Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n))
    (Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n))
    (Primrec.list_getElem?.comp
      (Primrec.fst.comp <| Primrec.fst.comp <|
        Primrec.fst (α := (List ℕ × List (List (Option ℕ))) × ℕ) (β := ℕ)) n)
  · have L := ((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp
      (Primrec.fst (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cf).pair n) ?_
    unfold Primrec₂
    conv =>
      congr
      · ext p
        dsimp only []
        erw [Option.bind_eq_bind, ← Option.map_eq_bind]
    refine Primrec.option_map ((hlup.comp <| L.pair <| (k.pair cg).pair n).comp Primrec.fst) ?_
    unfold Primrec₂
    exact Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  · have L := ((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp
      (Primrec.fst (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cg).pair n) ?_
    unfold Primrec₂
    have h :=
      hlup.comp ((L.comp Primrec.fst).pair <| ((k.pair cf).comp Primrec.fst).pair Primrec.snd)
    exact h
  · have L := ((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp
      (Primrec.fst (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × OracleCode × Option ℕ × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    refine
      Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp n))
        (hlup.comp <| L.pair <| (k.pair cf).pair z)
        (?_ : Primrec _)
    have L := L.comp (Primrec.fst (β := ℕ))
    have z := z.comp (Primrec.fst (β := ℕ))
    have y := Primrec.snd
      (α := (((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        OracleCode × OracleCode × Option ℕ × Option ℕ) (β := ℕ)
    have h₁ := hlup.comp <| L.pair <| (((k'.pair c).comp Primrec.fst).comp Primrec.fst).pair
      (Primrec₂.natPair.comp z y)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have z := z.comp (Primrec.fst (β := ℕ))
    have y := y.comp (Primrec.fst (β := ℕ))
    have i := Primrec.snd
      (α := ((((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ) ×
        OracleCode × OracleCode × Option ℕ × Option ℕ) × ℕ)
      (β := ℕ)
    have h₂ := hlup.comp ((L.comp Primrec.fst).pair <|
      ((k.pair cg).comp <| Primrec.fst.comp Primrec.fst).pair <|
        Primrec₂.natPair.comp z <| Primrec₂.natPair.comp y i)
    exact h₂
  · have L := ((Primrec.snd.comp Primrec.fst).comp Primrec.fst).comp
      (Primrec.fst (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × Option ℕ))
    have k := k.comp (Primrec.fst (β := OracleCode × Option ℕ))
    have n := n.comp (Primrec.fst (β := OracleCode × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := ((List ℕ × List (List (Option ℕ))) × ℕ) × ℕ)
        (β := OracleCode × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    have m := Primrec.snd.comp (Primrec.unpair.comp n)
    have h₁ := hlup.comp <| L.pair <| (k.pair cf).pair (Primrec₂.natPair.comp z m)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have m := m.comp (Primrec.fst (β := ℕ))
    refine Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) ?_
    unfold Primrec₂
    exact (hlup.comp ((L.comp Primrec.fst).pair <|
      ((k'.pair c).comp <| Primrec.fst.comp Primrec.fst).pair
        (Primrec₂.natPair.comp (z.comp Primrec.fst) (_root_.Primrec.succ.comp m)))).comp
      Primrec.fst

private theorem evalnPrefix_map (k c s n) :
    ((List.range k)[n]?.bind fun a => evalnPrefix k c s a) = evalnPrefix k c s n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evalnPrefix k c s n
      · rfl
      exact kn.elim (evalnPrefix_bound e)
    simpa using kn

set_option linter.flexible false in
/-- The bounded simulation is primitive recursive as a unary function of the
packed product. Adapted from `Nat.Partrec.Code.primrec_evaln`. -/
theorem primrec_evalnPrefix :
    Primrec fun a : (ℕ × OracleCode) × List ℕ × ℕ =>
      evalnPrefix a.1.1 a.1.2 a.2.1 a.2.2 :=
  have :
    Primrec₂ fun (s : List ℕ) (n : ℕ) =>
      let a := ofNat (ℕ × OracleCode) n
      (List.range a.1).map (fun m => evalnPrefix a.1 a.2 s m) :=
    Primrec.nat_strong_rec _ hG.to₂ fun s p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_unpair, Option.some_inj]
      refine List.map_congr_left fun n => ?_
      have : List.range p =
          List.range (Nat.pair p.unpair.1 (encode (ofNat OracleCode p.unpair.2))) := by
        simp
      rw [this]
      generalize p.unpair.1 = k
      generalize ofNat OracleCode p.unpair.2 = c
      intro nk
      rcases k with - | k'
      · simp [evalnPrefix]
      let k := k' + 1
      simp only
      simp only [List.mem_range, Nat.lt_succ_iff] at nk
      have hg :
        ∀ {k' c' n},
          Nat.pair k' (encode c') < Nat.pair k (encode c) →
            lup ((List.range (Nat.pair k (encode c))).map fun n =>
              (List.range n.unpair.1).map
                (fun m => evalnPrefix n.unpair.1 (ofNat OracleCode n.unpair.2) s m))
              (k', c') n =
            evalnPrefix k' c' s n := by
        intro k₁ c₁ n₁ hl
        simp [lup, List.getElem?_range hl, evalnPrefix_map, Bind.bind, Option.bind_map]
      obtain - | - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
        simp [evalnPrefix, nk, Bind.bind, Functor.map, Seq.seq, pure]
      · obtain ⟨lf, lg⟩ := encode_lt_pair cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
        cases evalnPrefix k cf s n
        · rfl
        cases evalnPrefix k cg s n <;> rfl
      · obtain ⟨lf, lg⟩ := encode_lt_comp cf cg
        rw [hg (Nat.pair_lt_pair_right _ lg)]
        cases evalnPrefix k cg s n
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lf)]
      · obtain ⟨lf, lg⟩ := encode_lt_prec cf cg
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        cases n.unpair.2
        · rfl
        simp only
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evalnPrefix k' _ s _
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lg)]
      · have lf := encode_lt_rfind' cf
        rw [hg (Nat.pair_lt_pair_right _ lf)]
        rcases evalnPrefix k cf s n with - | x
        · rfl
        simp only [Option.bind_some]
        cases x <;> simp
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
  (Primrec.option_bind
    (Primrec.list_getElem?.comp
      (this.comp (Primrec.fst.comp Primrec.snd) (Primrec.encode_iff.2 Primrec.fst))
      (Primrec.snd.comp Primrec.snd))
    Primrec.snd.to₂).of_eq
    fun ⟨⟨k, c⟩, s, n⟩ => by
      simpa [Option.bind_map, Function.comp_def] using evalnPrefix_map k c s n

/-- The bounded simulation is computable as a unary function of the packed
product. -/
theorem computable_evalnPrefix :
    Computable fun a : (ℕ × OracleCode) × List ℕ × ℕ =>
      evalnPrefix a.1.1 a.1.2 a.2.1 a.2.2 :=
  primrec_evalnPrefix.to_comp

end

end OracleCode

end ComputableAnalysis
