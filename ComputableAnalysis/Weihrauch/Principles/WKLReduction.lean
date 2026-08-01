/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.TypeTwo.PrefixTable
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

open OracleCode (binaryWords mem_binaryWords length_of_mem_binaryWords)

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

/-! ### Deciding the flags from a prefix

`TreeMem` reads the name at `treeWordCode w`, so a long-enough **prefix** of the name
decides every question the flags ask — the queries are indexed by the very codes being
looked up, and no scatter/gather is needed. These definitions are the decision procedure;
`raceFlagB_eq` is its agreement with the semantic `raceFlags`. -/

/-- Membership decided from a prefix of the tree name. -/
def treeMemB (L : List ℕ) (w : List Bool) : Bool := decide (L.getD (treeWordCode w) 0 ≠ 0)

/-- Aliveness decided from a prefix: some word of the right length extends `u`. -/
def aliveB (L : List ℕ) (u : List Bool) (l : ℕ) : Bool :=
  (binaryWords l).any fun v => treeMemB L (u ++ v)

/-- The strict death race decided from a prefix. -/
def raceEventB (L : List ℕ) (w : List Bool) (b : Bool) (l : ℕ) : Bool :=
  !aliveB L (w ++ [b]) l && aliveB L (w ++ [!b]) l

/-- The flag at coordinate `k` of node `w`, decided from a prefix. -/
def raceFlagB (L : List ℕ) (w : List Bool) (k : ℕ) : ℕ :=
  if raceEventB L w (decide (k % 2 = 1)) (k / 2) &&
      (List.range (k / 2)).all (fun l => !raceEventB L w (decide (k % 2 = 1)) l) then 1 else 0

/-- The words the flags at node `j`, coordinate `k`, inspect. -/
def raceWords (j k : ℕ) : List (List Bool) :=
  (List.range (k / 2 + 1)).flatMap fun l =>
    (binaryWords l).flatMap fun v =>
      [treeWordDecode j ++ [false] ++ v, treeWordDecode j ++ [true] ++ v]

/-- A strict bound on the codes of the inspected words. -/
def raceBound (m : ℕ) : ℕ :=
  ((raceWords m.unpair.1 m.unpair.2).map treeWordCode).foldr (fun i b => max (i + 1) b) 0

private theorem lt_foldr_max {l : List ℕ} {i : ℕ} (h : i ∈ l) :
    i < l.foldr (fun i b => max (i + 1) b) 0 := by
  induction l with
  | nil => exact absurd h List.not_mem_nil
  | cons a l ih =>
      rcases List.mem_cons.mp h with rfl | hl
      · exact lt_of_lt_of_le (Nat.lt_succ_self i) (le_max_left _ _)
      · exact lt_of_lt_of_le (ih hl) (le_max_right _ _)

/-- Every inspected word's code lies below the bound. -/
theorem treeWordCode_lt_raceBound {j k : ℕ} {w : List Bool} (h : w ∈ raceWords j k) :
    treeWordCode w < raceBound (Nat.pair j k) := by
  refine lt_foldr_max ?_
  simp only [Nat.unpair_pair]
  exact List.mem_map_of_mem h

/-- The words below a child, at a level within range, are inspected. -/
theorem mem_raceWords {j k l : ℕ} (hl : l ≤ k / 2) (c : Bool) {v : List Bool}
    (hv : v ∈ binaryWords l) : treeWordDecode j ++ [c] ++ v ∈ raceWords j k := by
  refine List.mem_flatMap.mpr ⟨l, List.mem_range.mpr (by omega), ?_⟩
  refine List.mem_flatMap.mpr ⟨v, hv, ?_⟩
  cases c <;> simp

/-- Aliveness is decided correctly once the prefix covers the inspected words. -/
theorem aliveB_iff {p : Baire} {N : ℕ} {u : List Bool} {l : ℕ}
    (h : ∀ v ∈ binaryWords l, treeWordCode (u ++ v) < N) :
    aliveB (streamTake p N) u l = true ↔ AliveAt p u l := by
  rw [aliveB, List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hb⟩
    have hval : (streamTake p N).getD (treeWordCode (u ++ v)) 0 = p (treeWordCode (u ++ v)) :=
      streamTake_getD p (h v hv)
    rw [treeMemB, decide_eq_true_eq, hval] at hb
    exact ⟨v, length_of_mem_binaryWords hv, hb⟩
  · rintro ⟨v, hv, hmem⟩
    have hvm : v ∈ binaryWords l := mem_binaryWords.mpr hv
    have hval : (streamTake p N).getD (treeWordCode (u ++ v)) 0 = p (treeWordCode (u ++ v)) :=
      streamTake_getD p (h v hvm)
    refine ⟨v, hvm, ?_⟩
    rw [treeMemB, decide_eq_true_eq, hval]
    exact hmem

/-- The race event is decided correctly once the prefix covers the inspected words. -/
theorem raceEventB_iff {p : Baire} {j k l : ℕ} (hl : l ≤ k / 2) (b : Bool) :
    raceEventB (streamTake p (raceBound (Nat.pair j k))) (treeWordDecode j) b l = true ↔
      RaceEvent p (treeWordDecode j) b l := by
  have hcov : ∀ (c : Bool) (v : List Bool), v ∈ binaryWords l →
      treeWordCode (treeWordDecode j ++ [c] ++ v) < raceBound (Nat.pair j k) := fun c v hv =>
    treeWordCode_lt_raceBound (mem_raceWords hl c hv)
  have h0 := aliveB_iff (p := p) (u := treeWordDecode j ++ [b]) (l := l) (hcov b)
  have h1 := aliveB_iff (p := p) (u := treeWordDecode j ++ [!b]) (l := l) (hcov !b)
  simp only [raceEventB, RaceEvent, Bool.and_eq_true, Bool.not_eq_true']
  rw [← h0, ← h1]
  simp

/-! ### Primitive recursiveness of the decision procedure

Elaboration machinery, deliberately private: the public contract is the named codes and
their evaluation specifications, not the plumbing needed to build them. -/

private theorem primrec_decide_ne {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => decide (f a ≠ g a) := by
  obtain ⟨_, h⟩ := PrimrecRel.comp (PrimrecRel.not Primrec.eq) hf hg
  exact Primrec.of_eq h fun a => decide_eq_decide.mpr Iff.rfl

private theorem primrec_decide_eq {α : Type*} [Primcodable α] {f g : α → ℕ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => decide (f a = g a) := by
  obtain ⟨_, h⟩ := PrimrecRel.comp Primrec.eq hf hg
  exact Primrec.of_eq h fun a => decide_eq_decide.mpr Iff.rfl

private theorem primrec_treeMemB {α : Type*} [Primcodable α] {L : α → List ℕ}
    {w : α → List Bool} (hL : Primrec L) (hw : Primrec w) :
    Primrec fun a => treeMemB (L a) (w a) :=
  primrec_decide_ne
    ((Primrec.list_getD 0).comp hL (primrec_treeWordCode.comp hw)) (Primrec.const 0)

private theorem primrec_aliveB {α : Type*} [Primcodable α] {L : α → List ℕ}
    {u : α → List Bool} {l : α → ℕ} (hL : Primrec L) (hu : Primrec u) (hl : Primrec l) :
    Primrec fun a => aliveB (L a) (u a) (l a) :=
  primrec_list_any (OracleCode.primrec_binaryWords.comp hl)
    ((primrec_treeMemB (hL.comp Primrec.fst)
      (Primrec.list_append.comp (hu.comp Primrec.fst) Primrec.snd)).to₂)

private theorem primrec_raceEventB {α : Type*} [Primcodable α] {L : α → List ℕ}
    {w : α → List Bool} {b : α → Bool} {l : α → ℕ}
    (hL : Primrec L) (hw : Primrec w) (hb : Primrec b) (hl : Primrec l) :
    Primrec fun a => raceEventB (L a) (w a) (b a) (l a) := by
  have hchild : ∀ (c : α → Bool), Primrec c → Primrec fun a => w a ++ [c a] := fun c hc =>
    Primrec.list_append.comp hw (Primrec.list_cons.comp hc (Primrec.const []))
  exact Primrec.and.comp
    (Primrec.not.comp (primrec_aliveB hL (hchild b hb) hl))
    (primrec_aliveB hL (hchild _ (Primrec.not.comp hb)) hl)

private theorem primrec_raceFlagB {α : Type*} [Primcodable α] {L : α → List ℕ}
    {w : α → List Bool} {k : α → ℕ} (hL : Primrec L) (hw : Primrec w) (hk : Primrec k) :
    Primrec fun a => raceFlagB (L a) (w a) (k a) := by
  have hpar : Primrec fun a => decide (k a % 2 = 1) :=
    primrec_decide_eq (Primrec.nat_mod.comp hk (Primrec.const 2)) (Primrec.const 1)
  have hhalf : Primrec fun a => k a / 2 := Primrec.nat_div.comp hk (Primrec.const 2)
  have hnow : Primrec fun a => raceEventB (L a) (w a) (decide (k a % 2 = 1)) (k a / 2) :=
    primrec_raceEventB hL hw hpar hhalf
  have hpast : Primrec fun a =>
      (List.range (k a / 2)).all fun l => !raceEventB (L a) (w a) (decide (k a % 2 = 1)) l :=
    primrec_list_all (Primrec.list_range.comp hhalf)
      ((Primrec.not.comp (primrec_raceEventB (hL.comp Primrec.fst) (hw.comp Primrec.fst)
        (hpar.comp Primrec.fst) Primrec.snd)).to₂)
  have hcond : Primrec fun a =>
      raceEventB (L a) (w a) (decide (k a % 2 = 1)) (k a / 2) &&
        (List.range (k a / 2)).all fun l =>
          !raceEventB (L a) (w a) (decide (k a % 2 = 1)) l := Primrec.and.comp hnow hpast
  refine Primrec.of_eq (Primrec.cond hcond (Primrec.const 1) (Primrec.const 0)) fun a => ?_
  simp only [raceFlagB]
  cases raceEventB (L a) (w a) (decide (k a % 2 = 1)) (k a / 2) &&
    (List.range (k a / 2)).all fun l =>
      !raceEventB (L a) (w a) (decide (k a % 2 = 1)) l <;> rfl

end ComputableAnalysis
