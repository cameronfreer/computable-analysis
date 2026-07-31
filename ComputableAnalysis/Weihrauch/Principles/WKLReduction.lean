/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Compilers
import ComputableAnalysis.Weihrauch.Principles.WKL

/-!
# The strict death race: reducing `WKL` to parallelized `LLPO`

The semantic layer of `WKL ≤sW LLPO.parallelize`. One `LLPO` instance per node `w` of the
presented tree, built by `firstOccurrenceFlags` from the **strict death race**: at level
`n` the `false` event says child `w0` is dead while `w1` is still alive, and the `true`
event says the reverse.

Two independent facts make the instance legitimate at *every* node, dead nodes included:

* within a side, `firstOccurrenceFlags` flags at most one level;
* across sides the events are outright incompatible (`not_raceEvent_both`), because
  aliveness is antitone in the level, so an even event at `n` and an odd event at `m`
  force both `m < n` and `n < m`.

Equal death times are simply unflagged, which is harmless: by `infAbove_select`, at a node
whose subtree is infinite the child selected by the answer (`0` selects child `0`) is again
infinite, and equal finite death can only occur off the constructed path.
-/

namespace ComputableAnalysis

/-! ### Aliveness and the death race -/

/-- The subtree above `w` reaches level `n`. -/
def AliveAt (p : Baire) (w : List Bool) (n : ℕ) : Prop :=
  ∃ v : List Bool, v.length = n ∧ TreeMem p (w ++ v)

/-- The subtree above `w` is infinite. -/
def InfAbove (p : Baire) (w : List Bool) : Prop := ∀ n, AliveAt p w n

/-- Aliveness is antitone in the level: prefix closure truncates a witness. -/
theorem AliveAt.mono {p : Baire} (hpc : IsPrefixClosed p) {w : List Bool} {m n : ℕ}
    (hmn : m ≤ n) (h : AliveAt p w n) : AliveAt p w m := by
  obtain ⟨v, hv, hmem⟩ := h
  refine ⟨v.take m, by rw [List.length_take, hv, Nat.min_eq_left hmn], ?_⟩
  refine hpc (w ++ v) _ hmem ?_
  rw [List.prefix_append_right_inj]
  exact List.take_prefix m v

/-- The strict death race at level `n`: child `b` is dead there while its sibling is
alive. -/
def RaceEvent (p : Baire) (w : List Bool) (b : Bool) (n : ℕ) : Prop :=
  ¬ AliveAt p (w ++ [b]) n ∧ AliveAt p (w ++ [!b]) n

/-- **The two sides are incompatible**, at any pair of levels — the fact that makes the
`LLPO` promise unconditional. -/
theorem not_raceEvent_both {p : Baire} (hpc : IsPrefixClosed p) {w : List Bool} {n m : ℕ}
    (h0 : RaceEvent p w false n) (h1 : RaceEvent p w true m) : False := by
  obtain ⟨hd0, ha1⟩ := h0
  obtain ⟨hd1, ha0⟩ := h1
  simp only [Bool.not_false, Bool.not_true] at ha1 ha0
  have hmn : m < n := by
    by_contra hc
    exact hd0 (AliveAt.mono hpc (by omega) ha0)
  have hnm : n < m := by
    by_contra hc
    exact hd1 (AliveAt.mono hpc (by omega) ha1)
  omega

/-- The `LLPO` instance attached to node `w`. -/
noncomputable def raceFlags (p : Baire) (w : List Bool) : Baire :=
  firstOccurrenceFlags (RaceEvent p w)

/-- Every node's instance satisfies the promise, unconditionally. -/
theorem raceFlags_atMostOne {p : Baire} (hpc : IsPrefixClosed p) (w : List Bool) :
    ∀ a b : ℕ, raceFlags p w a ≠ 0 → raceFlags p w b ≠ 0 → a = b :=
  firstOccurrenceFlags_atMostOne fun _ _ h0 h1 => not_raceEvent_both hpc h0 h1

/-- Every node's instance lies in `LLPO`'s domain. -/
theorem raceFlags_llpo_dom {p : Baire} (hpc : IsPrefixClosed p) (w : List Bool) :
    LLPO.Dom (raceFlags p w) :=
  llpo_dom_of_atMostOne (raceFlags_atMostOne hpc w)

/-! ### Selecting a child -/

/-- **The selection lemma**: at a node with an infinite subtree, an accepted answer selects
a child whose subtree is again infinite. Answer `0` selects child `0`. Prefix closure is
not needed here — only at the domain step (`raceFlags_llpo_dom`). -/
theorem infAbove_select {p : Baire} {w : List Bool}
    (hinf : InfAbove p w) {i : ℕ} (hacc : LLPO.accepts (raceFlags p w) i) :
    InfAbove p (w ++ [decide (i = 1)]) := by
  obtain ⟨-, hdisj⟩ := LLPO.accepts_iff.mp hacc
  -- if the selected child died at some level, its sibling would be alive there
  have hsib : ∀ (c : Bool) (n : ℕ), ¬ AliveAt p (w ++ [c]) n → RaceEvent p w c n := by
    intro c n hdead
    refine ⟨hdead, ?_⟩
    obtain ⟨v, hv, hmem⟩ := hinf (n + 1)
    obtain ⟨d, v', rfl⟩ : ∃ d v', v = d :: v' := by
      cases v with
      | nil => simp at hv
      | cons d v' => exact ⟨d, v', rfl⟩
    have hlen : v'.length = n := by simpa using hv
    have hmem' : TreeMem p ((w ++ [d]) ++ v') := by simpa using hmem
    cases c <;> cases d
    · exact absurd ⟨v', hlen, hmem'⟩ hdead
    · exact ⟨v', hlen, by simpa using hmem'⟩
    · exact ⟨v', hlen, by simpa using hmem'⟩
    · exact absurd ⟨v', hlen, hmem'⟩ hdead
  intro n
  by_contra hdead
  rcases hdisj with ⟨hi0, hall⟩ | ⟨hi1, hall⟩
  · rw [show decide (i = 1) = false by simp [hi0]] at hdead
    exact not_event_of_track_zero (b := false)
      (fun m => by simpa [raceFlags] using hall m) n (hsib false n hdead)
  · rw [show decide (i = 1) = true by simp [hi1]] at hdead
    exact not_event_of_track_zero (b := true)
      (fun m => by simpa [raceFlags] using hall m) n (hsib true n hdead)

/-! ### The path read off the answers -/

/-- The path prefix built from a stream of answer bits: at each node, follow its bit. -/
def pathWord (a : Baire) : ℕ → List Bool
  | 0 => []
  | n + 1 => pathWord a n ++ [decide (a (Nat.pair (treeWordCode (pathWord a n)) 0) = 1)]

@[simp]
private theorem length_pathWord (a : Baire) (n : ℕ) : (pathWord a n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathWord, ih]

/-- The Cantor **name** of the constructed path. -/
def pathName (a : Baire) : Baire :=
  fun k => if (pathWord a (k + 1)).getD k false then 1 else 0

private theorem bool_eq_beq_ite (b : Bool) : b = ((if b then (1 : ℕ) else 0) == 1) := by
  cases b <;> rfl

/-- The path stream's prefixes are exactly the path words. -/
theorem streamTake_pathStream (a : Baire) (n : ℕ) :
    streamTake (fun k => (pathWord a (k + 1)).getD k false) n = pathWord a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [streamTake_succ, ih]
      have hstep : pathWord a (n + 1)
          = pathWord a n ++ [decide (a (Nat.pair (treeWordCode (pathWord a n)) 0) = 1)] := rfl
      rw [hstep]
      congr 1
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp

/-- The path name denotes the path stream. -/
theorem cantorRep_names_pathName (a : Baire) :
    cantorRep.Names (pathName a) (fun k => (pathWord a (k + 1)).getD k false) :=
  cantorRep_names_iff.mpr
    ⟨fun n => by simp only [pathName]; split <;> omega, funext fun n => bool_eq_beq_ite _⟩

/-- An infinite subtree above `[]` is what infinitude of the tree says. -/
private theorem infAbove_nil {p : Baire} (hinf : IsInfiniteTree p) : InfAbove p [] := by
  intro n
  obtain ⟨w, hw, hmem⟩ := hinf n
  exact ⟨w, hw, by simpa using hmem⟩

/-- A node with an infinite subtree is itself a node. -/
private theorem treeMem_of_infAbove {p : Baire} {w : List Bool} (h : InfAbove p w) :
    TreeMem p w := by
  obtain ⟨v, hv, hmem⟩ := h 0
  rwa [List.length_eq_zero_iff.mp hv, List.append_nil] at hmem

/-- Following the answer bits stays inside the tree, at every level. -/
theorem infAbove_pathWord {p : Baire} (hinf : IsInfiniteTree p) {a : Baire}
    (hans : ∀ j, LLPO.accepts (raceFlags p (treeWordDecode j)) (a (Nat.pair j 0)))
    (n : ℕ) : InfAbove p (pathWord a n) := by
  induction n with
  | zero => exact infAbove_nil hinf
  | succ n ih =>
      have h := infAbove_select ih
        (i := a (Nat.pair (treeWordCode (pathWord a n)) 0))
        (by simpa [treeWordDecode_treeWordCode] using hans (treeWordCode (pathWord a n)))
      exact h

end ComputableAnalysis
