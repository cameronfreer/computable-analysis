/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Computability.Halting

/-!
# `REPred` closure lemmas

Mathlib's `Computability/RE.lean` provides only `REPred.of_eq`, `Partrec.dom_re`,
`ComputablePred.to_re` and Post's theorem — no closure of `REPred` under `∧`, `∨`,
precomposition, or (bounded or unbounded) quantification over `ℕ`. This file supplies
the missing closure lemmas (upstream candidates; pure computability content, no
dependence on the rest of this library):

* `repred_comp`: precomposition with a computable function.
* `repred_of_primrecPred`: primitively recursive decidable predicates are r.e.
* `repred_and` / `repred_or`: conjunction (via `Part.bind`) and disjunction (via
  `Partrec.merge'`).
* `repred_exists_nat`: ℕ-projection, by `Code.evaln` dovetailing (stage `k` checks
  witness `k.unpair.1` with fuel `k.unpair.2`) through `Nat.rfindOpt`.
* `repred_forall_lt` / `repred_exists_lt`: quantification bounded by a `Primrec`
  function of the input — the uniformly input-dependent finite conjunction and
  disjunction.

## Upstream status

**Not yet proposed.** mathlib's `Computability/RE.lean` has no `REPred` closure lemmas at the
current pin. Tracked in #14 and #21.
-/

namespace ComputableAnalysis

open Nat.Partrec (Code)

/-- `REPred` is closed under precomposition with a computable function (missing from
mathlib). -/
theorem repred_comp {α β : Type*} [Primcodable α] [Primcodable β] {p : β → Prop}
    (hp : REPred p) {g : α → β} (hg : Computable g) : REPred fun a => p (g a) :=
  Partrec.comp hp hg

/-- Decidable primitively recursive predicates are r.e. (missing from mathlib as a
one-step lemma). -/
theorem repred_of_primrecPred {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : PrimrecPred p) : REPred p := hp.computablePred.to_re

/-- `REPred` is closed under conjunction (missing from mathlib): sequential composition
of the two semidecision procedures via `Part.bind`. -/
theorem repred_and {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) : REPred fun a => p a ∧ q a := by
  have hp' : Partrec fun a => Part.assert (p a) fun _ => Part.some () := hp
  have hq' : Partrec fun a => Part.assert (q a) fun _ => Part.some () := hq
  have h : Partrec fun a => (Part.assert (p a) fun _ => Part.some ()).bind
      fun _ => Part.assert (q a) fun _ => Part.some () :=
    hp'.bind ((hq'.comp Computable.fst).to₂)
  refine h.dom_re.of_eq fun a => ?_
  rw [Part.bind_dom]
  constructor
  · rintro ⟨⟨hpa, -⟩, hqa, -⟩
    exact ⟨hpa, hqa⟩
  · rintro ⟨hpa, hqa⟩
    exact ⟨⟨hpa, trivial⟩, hqa, trivial⟩

/-- `REPred` is closed under disjunction (missing from mathlib): parallel composition of
the two semidecision procedures via `Partrec.merge'`. -/
theorem repred_or {α : Type*} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) : REPred fun a => p a ∨ q a := by
  have hp' : Partrec fun a => Part.assert (p a) fun _ => Part.some () := hp
  have hq' : Partrec fun a => Part.assert (q a) fun _ => Part.some () := hq
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp' hq'
  refine hk.dom_re.of_eq fun a => ?_
  rw [(H a).2]
  constructor
  · rintro (⟨hpa, -⟩ | ⟨hqa, -⟩)
    · exact Or.inl hpa
    · exact Or.inr hqa
  · rintro (hpa | hqa)
    · exact Or.inl ⟨hpa, trivial⟩
    · exact Or.inr ⟨hqa, trivial⟩

/-- `REPred` is closed under ℕ-projection (missing from mathlib): the Σ₁ closure under
an unbounded `∃ n : ℕ`. Proof: `Code.evaln` dovetailing — stage `k` checks witness
`k.unpair.1` with fuel `k.unpair.2` — through `Nat.rfindOpt`. -/
theorem repred_exists_nat {α : Type*} [Primcodable α] {p : α × ℕ → Prop}
    (hp : REPred p) : REPred fun a => ∃ n, p (a, n) := by
  have hp' : Partrec fun x : α × ℕ => Part.assert (p x) fun _ => Part.some () := hp
  have hnat : Nat.Partrec fun n =>
      Part.bind (Encodable.decode₂ (α × ℕ) n) fun x =>
        (Part.assert (p x) fun _ => Part.some ()).map Encodable.encode :=
    Partrec.bind_decode₂_iff.mp hp'
  obtain ⟨c, hc⟩ := Code.exists_code.mp hnat
  have hg : Computable₂ fun (a : α) (k : ℕ) =>
      (Code.evaln k.unpair.2 c (Encodable.encode (a, k.unpair.1))).map fun _ => () := by
    have h1 : Primrec fun w : α × ℕ =>
        Code.evaln w.2.unpair.2 c (Encodable.encode (w.1, w.2.unpair.1)) := by
      have hup1 : Primrec fun w : α × ℕ => w.2.unpair.1 :=
        Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)
      have hup2 : Primrec fun w : α × ℕ => w.2.unpair.2 :=
        Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)
      exact Code.primrec_evaln.comp
        ((hup2.pair (Primrec.const c)).pair
          (Primrec.encode.comp (Primrec.fst.pair hup1)))
    exact (Primrec.option_map h1 (Primrec.const ()).to₂).to_comp
  have hdove : Partrec fun a => Nat.rfindOpt fun k =>
      (Code.evaln k.unpair.2 c (Encodable.encode (a, k.unpair.1))).map fun _ => () :=
    Partrec.rfindOpt hg
  refine hdove.dom_re.of_eq fun a => ?_
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨k, u, hu⟩
    rw [Option.mem_def, Option.map_eq_some_iff] at hu
    obtain ⟨v, hv, -⟩ := hu
    have hev : v ∈ Code.eval c (Encodable.encode (a, k.unpair.1)) :=
      Code.evaln_sound hv
    rw [hc] at hev
    simp only [Encodable.encodek₂, Part.coe_some, Part.bind_some, Part.mem_map_iff,
      Part.mem_assert_iff, Part.mem_some_iff, exists_prop, and_true] at hev
    obtain ⟨-, hpa, -⟩ := hev
    exact ⟨k.unpair.1, hpa⟩
  · rintro ⟨n, hn⟩
    have hev : Encodable.encode () ∈ Code.eval c (Encodable.encode (a, n)) := by
      rw [hc]
      simp only [Encodable.encodek₂, Part.coe_some, Part.bind_some, Part.mem_map_iff,
        Part.mem_assert_iff, Part.mem_some_iff]
      refine ⟨(), ⟨hn, ?_⟩, ?_⟩ <;> trivial
    obtain ⟨s, hs⟩ := Code.evaln_complete.mp hev
    refine ⟨Nat.pair n s, (), ?_⟩
    rw [Option.mem_def, Nat.unpair_pair, Option.map_eq_some_iff]
    exact ⟨Encodable.encode (), hs, rfl⟩

/-- `REPred` is closed under `Primrec`-bounded universal quantification (missing from
mathlib): the uniformly input-dependent finite conjunction. Proof: `Code.evaln`
dovetailing — a single stage `k` must certify ALL `i < f a` simultaneously, via a
decidable `Bool`-fold over `List.range (f a)` — through `Nat.rfindOpt`. -/
theorem repred_forall_lt {α : Type*} [Primcodable α] {p : α × ℕ → Prop}
    (hp : REPred p) {f : α → ℕ} (hf : Primrec f) :
    REPred fun a => ∀ i < f a, p (a, i) := by
  have hp' : Partrec fun x : α × ℕ => Part.assert (p x) fun _ => Part.some () := hp
  have hnat : Nat.Partrec fun n =>
      Part.bind (Encodable.decode₂ (α × ℕ) n) fun x =>
        (Part.assert (p x) fun _ => Part.some ()).map Encodable.encode :=
    Partrec.bind_decode₂_iff.mp hp'
  obtain ⟨c, hc⟩ := Code.exists_code.mp hnat
  -- the stage-`k` simultaneous certificate for all `i < f a`
  have hb : Primrec fun w : α × ℕ =>
      (List.range (f w.1)).foldr
        (fun i b => (Code.evaln w.2 c (Encodable.encode (w.1, i))).isSome && b) true := by
    have hh : Primrec₂ fun (w : α × ℕ) (q : ℕ × Bool) =>
        (Code.evaln w.2 c (Encodable.encode (w.1, q.1))).isSome && q.2 :=
      Primrec.and.comp
        (Primrec.option_isSome.comp (Code.primrec_evaln.comp
          (((Primrec.snd.comp Primrec.fst).pair (Primrec.const c)).pair
            (Primrec.encode.comp ((Primrec.fst.comp Primrec.fst).pair
              (Primrec.fst.comp Primrec.snd))))))
        (Primrec.snd.comp Primrec.snd)
    exact (Primrec.list_foldr (Primrec.list_range.comp (hf.comp Primrec.fst))
      (Primrec.const true) hh).of_eq fun w => rfl
  have hg : Computable₂ fun (a : α) (k : ℕ) =>
      (bif (List.range (f a)).foldr
          (fun i b => (Code.evaln k c (Encodable.encode (a, i))).isSome && b) true
        then some () else none : Option Unit) :=
    (Primrec.cond hb (Primrec.const (some ())) (Primrec.const none)).to_comp
  have hdove : Partrec fun a => Nat.rfindOpt fun k =>
      (bif (List.range (f a)).foldr
          (fun i b => (Code.evaln k c (Encodable.encode (a, i))).isSome && b) true
        then some () else none : Option Unit) := Partrec.rfindOpt hg
  -- semantics of the Bool fold
  have hfold : ∀ (g : ℕ → Bool) (l : List ℕ) (init : Bool),
      (l.foldr (fun i b => g i && b) init = true) ↔ (∀ i ∈ l, g i = true) ∧ init = true := by
    intro g l init
    induction l with
    | nil => simp
    | cons a l ih =>
      rw [List.foldr_cons, Bool.and_eq_true, ih, List.forall_mem_cons]
      tauto
  have hmono : ∀ {k K : ℕ}, k ≤ K → ∀ {n : ℕ},
      (Code.evaln k c n).isSome = true → (Code.evaln K c n).isSome = true := by
    intro k K hkK n hs
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
    exact Option.isSome_iff_exists.mpr ⟨v, Code.evaln_mono hkK hv⟩
  refine hdove.dom_re.of_eq fun a => ?_
  rw [Nat.rfindOpt_dom]
  constructor
  · rintro ⟨k, u, hu⟩
    intro i hi
    cases hB : (List.range (f a)).foldr
        (fun i b => (Code.evaln k c (Encodable.encode (a, i))).isSome && b) true with
    | false =>
      rw [hB, Bool.cond_false] at hu
      exact absurd hu (Option.not_mem_none u)
    | true =>
      have hall := ((hfold _ _ _).mp hB).1 i (List.mem_range.mpr hi)
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hall
      have hev : v ∈ Code.eval c (Encodable.encode (a, i)) := Code.evaln_sound hv
      rw [hc] at hev
      simp only [Encodable.encodek₂, Part.coe_some, Part.bind_some, Part.mem_map_iff,
        Part.mem_assert_iff, Part.mem_some_iff, exists_prop, and_true] at hev
      obtain ⟨-, hpa, -⟩ := hev
      exact hpa
  · intro h
    have hex : ∀ i < f a, ∃ k, (Code.evaln k c (Encodable.encode (a, i))).isSome = true := by
      intro i hi
      have hev : Encodable.encode () ∈ Code.eval c (Encodable.encode (a, i)) := by
        rw [hc]
        simp only [Encodable.encodek₂, Part.coe_some, Part.bind_some, Part.mem_map_iff,
          Part.mem_assert_iff, Part.mem_some_iff]
        refine ⟨(), ⟨h i hi, ?_⟩, ?_⟩ <;> trivial
      obtain ⟨s, hs⟩ := Code.evaln_complete.mp hev
      exact ⟨s, Option.isSome_iff_exists.mpr ⟨_, hs⟩⟩
    have huniform : ∀ N : ℕ,
        (∀ i < N, ∃ k, (Code.evaln k c (Encodable.encode (a, i))).isSome = true) →
        ∃ K, ∀ i < N, (Code.evaln K c (Encodable.encode (a, i))).isSome = true := by
      intro N
      induction N with
      | zero => exact fun _ => ⟨0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
      | succ N ih =>
        intro hN
        obtain ⟨K₀, hK₀⟩ := ih fun i hi => hN i (Nat.lt_succ_of_lt hi)
        obtain ⟨k₁, hk₁⟩ := hN N (Nat.lt_succ_self N)
        refine ⟨max K₀ k₁, fun i hi => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact hmono (le_max_left _ _) (hK₀ i hlt)
        · exact hmono (le_max_right _ _) hk₁
    obtain ⟨K, hK⟩ := huniform (f a) hex
    refine ⟨K, (), ?_⟩
    have hB : (List.range (f a)).foldr
        (fun i b => (Code.evaln K c (Encodable.encode (a, i))).isSome && b) true = true :=
      (hfold _ _ _).mpr ⟨fun i hi => hK i (List.mem_range.mp hi), rfl⟩
    rw [hB, Bool.cond_true]
    rfl

/-- `REPred` is closed under `Primrec`-bounded existential quantification (missing from
mathlib): an easy corollary of `repred_exists_nat` + `repred_and` with the decidable
bound guard. -/
theorem repred_exists_lt {α : Type*} [Primcodable α] {p : α × ℕ → Prop}
    (hp : REPred p) {f : α → ℕ} (hf : Primrec f) :
    REPred fun a => ∃ i < f a, p (a, i) := by
  have hguard : REPred fun x : α × ℕ => x.2 < f x.1 :=
    repred_of_primrecPred (Primrec.nat_lt.comp Primrec.snd (hf.comp Primrec.fst))
  exact (repred_exists_nat (repred_and hguard hp)).of_eq fun a => Iff.rfl

end ComputableAnalysis
