/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.WeakEquivalence
import Mathlib.MeasureTheory.Measure.DiracProba

/-!
# Recovering a Cantor point from a weak name of its Dirac measure

A weak name of a probability measure on Cantor space approximates it in Lévy–Prokhorov
distance. When the measure happens to be the Dirac measure at a point, the point itself is
recoverable from the name, uniformly and by a single oracle code: `exists_diracDecodeCode`.

The decision is exact rather than approximate. Cylinder masses of `diracProba z` are `0` or
`1`, never anything between, so an approximation to within `1/4` of the mass of a word
cylinder already decides whether the point lies in it: among the `2^(t+1)` words of length
`t + 1`, exactly one cylinder contains `z`, and the search for the word whose approximate
mass exceeds `1/2` finds it and reads bit `t` off it. Cylinder masses come from the unit 28
equivalence `cantorMeasureRep_equiv_weak`, and the comparison against the threshold is
primitive recursive by `primrecPred_ratLt`.

The contract is stated at the level of representations — a weak name in, a `cantorRep` name
out — and mentions nothing about where such a name came from.
-/

open Encodable Denumerable MeasureTheory

namespace ComputableAnalysis

open scoped PiNatInstances

/-! ### Cylinder masses of a Dirac measure are `0` or `1` -/

/-- A Dirac measure gives mass `1` to every cylinder containing its point. -/
private theorem cylMass_diracProba_of_mem {z : Cantor} {s : List Bool}
    (hz : z ∈ (cylinder s : Set Cantor)) : cylMass (diracProba z) s = 1 := by
  rw [cylMass, show (diracProba z).toMeasure = Measure.dirac z from rfl,
    Measure.dirac_apply' z (measurableSet_cylinder s), Set.indicator_of_mem hz]
  simp

/-- A Dirac measure gives mass `0` to every cylinder missing its point. -/
private theorem cylMass_diracProba_of_not_mem {z : Cantor} {s : List Bool}
    (hz : z ∉ (cylinder s : Set Cantor)) : cylMass (diracProba z) s = 0 := by
  rw [cylMass, show (diracProba z).toMeasure = Measure.dirac z from rfl,
    Measure.dirac_apply' z (measurableSet_cylinder s), Set.indicator_of_notMem hz]
  simp

/-! ### The words of a given length -/

/-- All Boolean words of a given length. -/
private def wordsOfLen : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (wordsOfLen n).map (fun s => false :: s) ++ (wordsOfLen n).map (fun s => true :: s)

/-- Every entry of `wordsOfLen n` has length `n`. -/
private theorem length_of_mem_wordsOfLen : ∀ {n : ℕ} {s : List Bool},
    s ∈ wordsOfLen n → s.length = n
  | 0, s, hs => by
      rw [wordsOfLen, List.mem_singleton] at hs
      simp [hs]
  | n + 1, s, hs => by
      rw [wordsOfLen, List.mem_append] at hs
      rcases hs with hs | hs <;>
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
          simp [length_of_mem_wordsOfLen hu]

/-- Every word occurs in the list for its own length. -/
private theorem mem_wordsOfLen : ∀ s : List Bool, s ∈ wordsOfLen s.length
  | [] => by simp [wordsOfLen]
  | b :: s => by
      have hs := mem_wordsOfLen s
      rw [List.length_cons, wordsOfLen, List.mem_append]
      cases b
      · exact Or.inl (List.mem_map.mpr ⟨s, hs, rfl⟩)
      · exact Or.inr (List.mem_map.mpr ⟨s, hs, rfl⟩)

private theorem primrec_wordsOfLen : Primrec wordsOfLen := by
  have h : Primrec fun n : ℕ => Nat.rec (motive := fun _ => List (List Bool)) [[]]
      (fun _ ih => ih.map (fun s => false :: s) ++ ih.map (fun s => true :: s)) n :=
    Primrec.nat_rec' Primrec.id (Primrec.const [[]])
      ((Primrec.list_append.comp
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          ((Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂))
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          ((Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂))).to₂)
  refine h.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [wordsOfLen, ← ih]

/-! ### The threshold and the selection fold -/

/-- The code of the threshold `1/2`. -/
private def halfCode : RatCode := Nat.pair (Nat.pair 1 0) 1

private theorem ratOfCode_halfCode : ratOfCode halfCode = 1 / 2 := by
  rw [ratOfCode, halfCode]
  norm_num

/-- Folds agree when their steps agree on the entries of the list. -/
private theorem foldr_congr_mem {α β : Type*} {f g : α → β → β} {l : List α} {b : β}
    (h : ∀ a ∈ l, ∀ x, f a x = g a x) : l.foldr f b = l.foldr g b := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, ih fun c hc => h c (List.mem_cons_of_mem _ hc),
        h a List.mem_cons_self]

/-- A fold that selects the value at the unique satisfying entry. -/
private theorem foldr_select {α : Type*} (P : α → Prop) [DecidablePred P] (f : α → ℕ)
    (l : List α) (a : α) (ha : a ∈ l) (hP : P a) (huniq : ∀ b ∈ l, P b → b = a) :
    l.foldr (fun x acc => if P x then f x else acc) 0 = f a := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rcases List.mem_cons.mp ha with rfl | ha'
      · simp [hP]
      · by_cases hPb : P b
        · rw [huniq b List.mem_cons_self hPb]
          simp [hP]
        · rw [List.foldr_cons, ite_eq_right hPb]
          exact ih ha' fun c hc => huniq c (List.mem_cons_of_mem _ hc)

/-! ### The decoding postprocessor -/

/-- The prefix of a cylinder-mass name that decoding bit `t` reads: long enough to contain
the precision-`2` component of every word of length `t + 1`. -/
private def bitBound (t : ℕ) : ℕ :=
  ((wordsOfLen (t + 1)).map fun s => Nat.pair (encode s) 2 + 1).foldr max 0

private theorem lt_bitBound {t : ℕ} {s : List Bool} (hs : s ∈ wordsOfLen (t + 1)) :
    Nat.pair (encode s) 2 < bitBound t := by
  rw [bitBound]
  have hmem : Nat.pair (encode s) 2 + 1 ∈
      (wordsOfLen (t + 1)).map fun s => Nat.pair (encode s) 2 + 1 :=
    List.mem_map.mpr ⟨s, hs, rfl⟩
  revert hmem
  generalize ((wordsOfLen (t + 1)).map fun s => Nat.pair (encode s) 2 + 1) = l
  intro hmem
  induction l with
  | nil => simp at hmem
  | cons a l ih =>
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
      · exact lt_of_lt_of_le (ih hmem') (le_max_right _ _)

private theorem primrec_bitBound : Primrec bitBound := by
  have hmap : Primrec fun t : ℕ =>
      (wordsOfLen (t + 1)).map fun s => Nat.pair (encode s) 2 + 1 :=
    Primrec.list_map (primrec_wordsOfLen.comp Primrec.succ)
      ((Primrec.succ.comp (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.const 2))).to₂)
  exact Primrec.list_foldr hmap (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)

/-- The oracle-free postprocessor: from the coordinate `t` paired with an encoded prefix of
a cylinder-mass name, select the unique word of length `t + 1` whose approximate mass beats
the threshold, and return its last bit. -/
private def bitStep (v : ℕ) : ℕ :=
  (wordsOfLen (v.unpair.1 + 1)).foldr
    (fun s acc =>
      if ratOfCode halfCode
          < ratOfCode (((ofNat (List ℕ) v.unpair.2)[Nat.pair (encode s) 2]?).getD 0) then
        (if (s[v.unpair.1]?).getD false then 1 else 0)
      else acc) 0

private theorem primrec_bitStep : Primrec bitStep := by
  have hcoord : Primrec fun v : ℕ => v.unpair.1 := Primrec.fst.comp Primrec.unpair
  have hlist : Primrec fun v : ℕ => ofNat (List ℕ) v.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair)
  have hwords : Primrec fun v : ℕ => wordsOfLen (v.unpair.1 + 1) :=
    primrec_wordsOfLen.comp (Primrec.succ.comp hcoord)
  have hval : Primrec fun w : ℕ × List Bool × ℕ =>
      (((ofNat (List ℕ) w.1.unpair.2)[Nat.pair (encode w.2.1) 2]?).getD 0) :=
    Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (hlist.comp Primrec.fst)
        (Primrec₂.natPair.comp (Primrec.encode.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.const 2)))
      (Primrec.const 0)
  have hbit : Primrec fun w : ℕ × List Bool × ℕ =>
      if ((w.2.1)[w.1.unpair.1]?).getD false then 1 else 0 :=
    Primrec.ite
      (Primrec.eq.comp
        (Primrec.option_getD.comp
          (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
            (hcoord.comp Primrec.fst))
          (Primrec.const false))
        (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)
  exact Primrec.list_foldr hwords (Primrec.const 0)
    ((Primrec.ite (primrecPred_ratLt (Primrec.const halfCode) hval) hbit
      (Primrec.snd.comp Primrec.snd)).to₂)

/-! ### The decoder -/

/-- **The Cantor Dirac decoder.** One oracle code recovers the point from any weak name of
the Dirac measure at it: a `cantorRep` name of `z` from a `weakMeasureRep` name of
`diracProba z`, uniformly in both.

The code translates the weak name into cylinder masses through the unit 28 equivalence, then
decides bit `t` by locating, among the words of length `t + 1`, the one whose mass
approximation at precision `2` exceeds `1/2`. Exactly one qualifies: the masses of
`diracProba z` are `0` or `1`, so a value beating `1/2` forces mass `1`, hence membership of
`z` in that cylinder, hence that the word is `z`'s own length-`(t + 1)` prefix — while that
prefix does qualify, its mass being exactly `1`. -/
theorem exists_diracDecodeCode :
    ∃ D : OracleCode, ∀ (r : Baire) (z : Cantor),
      (weakMeasureRep cantorPresentation).Names r (diracProba z) →
        ∃ w ∈ D.evalStream r, cantorRep.Names w z := by
  obtain ⟨c₁, hc₁⟩ := cantorMeasureRep_equiv_weak.2
  obtain ⟨E, hE⟩ := OracleCode.exists_prefixPostCode
    (b := fun t _ => bitBound t) (primrec_bitBound.comp Primrec.fst).to₂ primrec_bitStep
  refine ⟨E.subst c₁, fun r z hr => ?_⟩
  obtain ⟨F, hF, hFname⟩ := hc₁ r (diracProba z) hr
  have hM : MeasureNames F (diracProba z) := cantorMeasureRep_names_iff.mp hFname
  -- the precision-`2` component of the mass of a word, as read off the name
  have happrox : ∀ s : List Bool,
      |((ratOfCode (F (Nat.pair (encode s) 2)) : ℚ) : ℝ) - cylMass (diracProba z) s| ≤ 4⁻¹ := by
    intro s
    have hnames := (Representation.subtype_names_iff.mp (hM s))
    have h2 := (realPresentation.cauchyRep_names_iff.mp hnames) 2
    rw [Real.dist_eq] at h2
    calc |((ratOfCode (F (Nat.pair (encode s) 2)) : ℚ) : ℝ) - cylMass (diracProba z) s|
        = |realPresentation.dense ((fun n => F (Nat.pair (encode s) n)) 2)
            - (cylMass01 (diracProba z) s : ℝ)| := rfl
      _ ≤ (2 : ℝ)⁻¹ ^ 2 := h2
      _ = 4⁻¹ := by norm_num
  -- the qualifying words are exactly the prefixes of `z`
  have hsel : ∀ (t : ℕ) (s : List Bool), s ∈ wordsOfLen (t + 1) →
      (ratOfCode halfCode < ratOfCode (F (Nat.pair (encode s) 2)) ↔ s = streamTake z (t + 1)) := by
    intro t s hs
    have hlen : s.length = t + 1 := length_of_mem_wordsOfLen hs
    have happ := happrox s
    constructor
    · intro hgt
      have hgtR : (1 / 2 : ℝ) < ((ratOfCode (F (Nat.pair (encode s) 2)) : ℚ) : ℝ) := by
        have := (Rat.cast_lt (K := ℝ)).mpr hgt
        rwa [ratOfCode_halfCode, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at this
      have hpos : (0 : ℝ) < cylMass (diracProba z) s := by
        cases abs_le.mp happ with
        | intro _ hub => linarith
      have hmem : z ∈ (cylinder s : Set Cantor) := by
        by_contra hnot
        rw [cylMass_diracProba_of_not_mem hnot] at hpos
        exact absurd hpos (lt_irrefl 0)
      have := mem_cylinder_iff.mp hmem
      rw [hlen] at this
      exact this.symm
    · rintro rfl
      have hmem : z ∈ (cylinder (streamTake z (t + 1)) : Set Cantor) := mem_cylinder_streamTake z _
      have hone : cylMass (diracProba z) (streamTake z (t + 1)) = 1 :=
        cylMass_diracProba_of_mem hmem
      set q : ℚ := ratOfCode (F (Nat.pair (encode (streamTake z (t + 1))) 2)) with hq
      have hlb : (3 / 4 : ℝ) ≤ (q : ℝ) := by
        have := abs_le.mp (happrox (streamTake z (t + 1)))
        rw [hone] at this
        linarith [this.1]
      have : ((1 / 2 : ℚ) : ℝ) < (q : ℝ) := by
        push_cast
        linarith
      rw [ratOfCode_halfCode]
      exact_mod_cast this
  -- the emitted stream is the bit stream of `z`
  set w : Baire := fun t => bitStep (Nat.pair t (encode (streamTake F (bitBound t)))) with hw
  have hwval : ∀ t, w t = if z t then 1 else 0 := by
    intro t
    have hprefix : ∀ s ∈ wordsOfLen (t + 1),
        ((ofNat (List ℕ) (encode (streamTake F (bitBound t))))[Nat.pair (encode s) 2]?).getD 0
          = F (Nat.pair (encode s) 2) := by
      intro s hs
      rw [Denumerable.ofNat_encode, getElem?_streamTake_of_lt F (lt_bitBound hs), Option.getD_some]
    rw [hw]
    simp only [bitStep, Nat.unpair_pair]
    rw [foldr_congr_mem (g := fun s acc =>
      if ratOfCode halfCode < ratOfCode (F (Nat.pair (encode s) 2)) then
        (if (s[t]?).getD false then 1 else 0) else acc)
      (fun s hs _ => by rw [hprefix s hs])]
    have hmemw : streamTake z (t + 1) ∈ wordsOfLen (t + 1) := by
      simpa [length_streamTake] using mem_wordsOfLen (streamTake z (t + 1))
    rw [foldr_select _ _ _ (streamTake z (t + 1)) hmemw ((hsel t _ hmemw).mpr rfl)
      (fun b hb hPb => (hsel t b hb).mp hPb)]
    rw [getElem?_streamTake_of_lt z (Nat.lt_succ_self t), Option.getD_some]
  refine ⟨w, ?_, ?_⟩
  · rw [OracleCode.evalStream_subst hF]
    refine OracleCode.mem_evalStream.mpr fun t => ?_
    rw [hE F t]
    exact Part.mem_some _
  · have hg : (fun t => w t == 1) = z := by
      funext t
      rw [hwval t]
      cases hz : z t <;> simp
    exact Part.mem_assert (fun t => by rw [hwval t]; split <;> omega)
      (by rw [hg]; exact Part.mem_some z)

end ComputableAnalysis
