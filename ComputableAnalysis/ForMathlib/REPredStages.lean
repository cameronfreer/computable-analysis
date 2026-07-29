/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecContainers
import Mathlib.Computability.Halting

/-!
# Staged approximation of r.e. predicates

Mathlib's `Computability/RE.lean` supplies `REPred.of_eq`, `Partrec.dom_re`,
`ComputablePred.to_re` and Post's theorem, but no characterization of `REPred` as the limit of
a decidable test with a fuel parameter — the form every effective consumer actually wants.

* `repred_exists_primrec_stages`: `p a ↔ ∃ t, f a t = true` for some `Primrec₂ f`.
* `repred_exists_primrec_cumulative`: the same with *persistence*, obtained by taking the
  bounded disjunction over `s ≤ t`.
* `exists_common_stage_of_persistent`: persistence turns pointwise confirmation into one stage
  certifying a whole finite family.

Names follow the `repred_*` convention of `ForMathlib/REPredClosure.lean`. The intended
**upstream** name of the first is `REPred.exists_primrec_stages`, in mathlib's root namespace
where dot notation on a `REPred` hypothesis fires; using that name here would only produce
pseudo-dot notation, since `REPred` is reducible and resolution lands on `Nat.Partrec`.

## Upstream status

**`repred_exists_primrec_stages` only** is the upstream candidate, to be proposed as
`REPred.exists_primrec_stages`; tracked in #14 and #21. The
`Primrec₂` conjunct is the entire content: without it the statement is vacuous, since
`fun a _ => decide (p a)` satisfies the biconditional classically.

The other two are deliberately **not** proposed. Persistence is established where it is
consumed rather than bolted onto the public theorem as a monotonicity conjunct that nothing
upstream would need, which keeps the proposed API minimal.
-/

open Nat.Partrec Nat.Partrec.Code Encodable

namespace ComputableAnalysis

/-- **Every r.e. predicate is the existential projection of a primitive recursive test.**
The fuel parameter `t` ranges over stages of `evaln`; the machine code is deliberately hidden,
since no consumer needs the numbering. -/
theorem repred_exists_primrec_stages {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : REPred p) :
    ∃ f : α → ℕ → Bool, Primrec₂ f ∧ ∀ a, p a ↔ ∃ t, f a t = true := by
  obtain ⟨c, hc⟩ := exists_code.mp hp
  have hdom : ∀ a : α, (eval c (encode a)).Dom ↔ p a := by
    intro a
    rw [hc]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom]
    exact ⟨fun h => h.fst, fun h => ⟨h, trivial⟩⟩
  refine ⟨fun a t => (evaln t c (encode a)).isSome, ?_, fun a => ⟨fun ha => ?_, fun ⟨t, ht⟩ => ?_⟩⟩
  · exact Primrec.option_isSome.comp (Code.primrec_evaln.comp
      ((Primrec.snd.pair (Primrec.const c)).pair (Primrec.encode.comp Primrec.fst)))
  · obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp ((hdom a).mpr ha)
    obtain ⟨k, hk⟩ := evaln_complete.mp hx
    exact ⟨k, Option.isSome_iff_exists.mpr ⟨x, hk⟩⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ht
    exact (hdom a).mp (evaln_sound hx).fst

/-- **The cumulative certificate.** `exists_primrec_stages` gives eventual confirmation but not
persistence, so a certificate must never be read off `f a t` alone: distinct instances may be
confirmed at different stages with no common exact stage. The bounded disjunction over `s ≤ t`
restores persistence and stays primitive recursive. -/
theorem repred_exists_primrec_cumulative {α : Type*} [Primcodable α] {p : α → Prop}
    (hp : REPred p) :
    ∃ g : α → ℕ → Bool, Primrec₂ g ∧
      (∀ a t, g a t = true → p a) ∧
      (∀ a t t', t ≤ t' → g a t = true → g a t' = true) ∧
      (∀ a, p a → ∃ t, g a t = true) := by
  obtain ⟨f, hfprim, hfiff⟩ := repred_exists_primrec_stages hp
  refine ⟨fun a t => (List.range (t + 1)).any (fun s => f a s), ?_, ?_, ?_, ?_⟩
  · exact primrec_list_any
      (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
      (hfprim.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  · intro a t ht
    obtain ⟨s, -, hs⟩ := List.any_eq_true.mp ht
    exact (hfiff a).mpr ⟨s, hs⟩
  · intro a t t' htt' ht
    obtain ⟨s, hs, hfs⟩ := List.any_eq_true.mp ht
    exact List.any_eq_true.mpr ⟨s, List.range_subset.mpr (Nat.succ_le_succ htt') hs, hfs⟩
  · intro a ha
    obtain ⟨t, ht⟩ := (hfiff a).mp ha
    exact ⟨t, List.any_eq_true.mpr ⟨t, List.mem_range.mpr (Nat.lt_succ_self t), ht⟩⟩

/-- **One stage certifies a whole finite family.** Persistence is exactly what turns pointwise
eventual confirmation into a single common stage — the fact a packed search needs, after its
other coordinates are fixed. -/
theorem exists_common_stage_of_persistent {α : Type*} {p : α → Prop} {g : α → ℕ → Bool}
    (hpers : ∀ a t t', t ≤ t' → g a t = true → g a t' = true)
    (hev : ∀ a, p a → ∃ t, g a t = true) :
    ∀ l : List α, (∀ a ∈ l, p a) → ∃ t, ∀ a ∈ l, g a t = true := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨0, by simp⟩
  | cons b l ih =>
    intro hl
    obtain ⟨t₁, ht₁⟩ := hev b (hl b (List.mem_cons_self ..))
    obtain ⟨t₂, ht₂⟩ := ih fun a ha => hl a (List.mem_cons_of_mem _ ha)
    refine ⟨max t₁ t₂, fun a ha => ?_⟩
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact hpers _ _ _ (le_max_left _ _) ht₁
    · exact hpers _ _ _ (le_max_right _ _) (ht₂ a ha')

end ComputableAnalysis
