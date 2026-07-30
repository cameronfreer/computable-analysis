/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.CantorRepresentation
import ComputableAnalysis.Measure.WeakRepresentation
import ComputableAnalysis.Metric.CantorPresentation
import ComputableAnalysis.Metric.RatCodeArith
import Mathlib.Data.List.GetD
import Mathlib.Computability.Halting

/-!
# Equivalence of the two Cantor measure representations

The unit 28 interface theorem: the Cantor computable-measure representation
`cantorMeasureRep` (exact cylinder-mass component names, unit 25) is computably
equivalent to the generic weak measure representation `weakMeasureRep` (unit 27)
instantiated at the Cantor presentation (unit 24), under convention 11's scoped
`PiNat` instances:

* `cantorMeasureRep_equiv_weak : cantorMeasureRep ≡c weakMeasureRep cantorPresentation`

Both directions are explicit realizers from `OracleCode.exists_prefixPostCode`.

**Weak to cylinder masses.** The separation fact: an `ε`-thickening of a word cylinder
with `0 < ε ≤ 2 · ((2:ℝ)⁻¹) ^ s.length` is the cylinder itself (two Cantor points at
distance `< (1/2)^m` agree at all coordinates `≤ m`), so past the separation threshold
the Lévy–Prokhorov defining inequalities collapse on the clopen cylinder and LP distance
controls cylinder masses exactly (`abs_cylMass_sub_le`).  The cylinder mass of a decoded
atomic measure is an *exact rational*, computed by the total code `cylWtCode` (decidable
membership `inCylB` of `false`-padded words in cylinders, plus a positive-division rider
`divPosCode` on the unnormalized coded fractions).  Component `(s, n)` of the output is
read off coordinate `s.length + n` of the weak name.

**Cylinder masses to weak.** Output coordinate `n` is the encoded level-`(n + 2)`
discretization list: all words of length `n + 2` paired with the weight codes read off
the name at packed precision `2n + 5`.  The discretization estimate costs
`(2⁻¹) ^ (n + 2)` (cylinders have diameter `(1/2) ^ (n + 2)`), and renormalizing the
`2 ^ (n + 2)` approximate weights costs `2 · 2 ^ (n + 2) · (2⁻¹) ^ (2n + 5)
= (2⁻¹) ^ (n + 2)` more — total `(2⁻¹) ^ (n + 1) ≤ (2⁻¹) ^ n`.

Implementation note: unit 27 keeps its evaluation lemmas for `atomicOfList` private, so
this file re-proves the two branch evaluations against private *definitionally equal*
copies of the clamped-weight helpers (`wRaw`, `wSumL`); the branch proofs go through
`rw [atomicOfList]` plus `split`, with `exact`/`rfl` crossing the definitional equality.
-/

namespace ComputableAnalysis

open MeasureTheory Metric Encodable Denumerable OracleCode

open scoped PiNatInstances

/-! ### Clamped weights: definitionally equal copies of unit 27's private helpers -/

/-- The clamped rational weight of a weight code (definitionally equal to the private
helper inside `atomicOfList`). -/
private def wRaw (c : ℕ) : ℚ := max 0 (min 1 (ratOfCode c))

private theorem wRaw_nonneg (c : ℕ) : 0 ≤ wRaw c := le_max_left _ _

/-- The (rational) total clamped weight of a decoded atom list (definitionally equal to
the private helper inside `atomicOfList`). -/
private def wSumL (l : List (ℕ × ℕ)) : ℚ := (l.map fun pr => wRaw pr.2).sum

private theorem wSumL_nonneg (l : List (ℕ × ℕ)) : 0 ≤ wSumL l :=
  List.sum_nonneg fun x hx => by
    obtain ⟨pr, -, rfl⟩ := List.mem_map.mp hx
    exact wRaw_nonneg _

/-- A mapped list sum as a `Fin` sum over positions. -/
private theorem listSum_map_eq_finSum {β M : Type*} [AddCommMonoid M] (l : List β)
    (g : β → M) : (l.map g).sum = ∑ i : Fin l.length, g l[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

/-! ### Evaluation of the decoded atomics

The two branch evaluations of unit 27's `atomicOfList`, restated over the private
copies above; the proofs cross the definitional equality. -/

/-- Nonzero total weight: the decoded atomic is the renormalized weighted Dirac sum. -/
private theorem toMeasure_atomicOfList_of_ne {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) :
    (atomicOfList cantorPresentation l).toMeasure
      = ∑ i : Fin l.length,
          ENNReal.ofReal ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            • Measure.dirac (cantorPresentation.dense l[i].1) := by
  rw [atomicOfList]
  split
  · next h => exact absurd h h0
  · next h => rfl

/-- Zero total weight: the decoded atomic is the default Dirac at dense point `0`. -/
private theorem toMeasure_atomicOfList_of_eq {l : List (ℕ × ℕ)} (h0 : wSumL l = 0) :
    (atomicOfList cantorPresentation l).toMeasure
      = Measure.dirac (cantorPresentation.dense 0) := by
  rw [atomicOfList]
  split
  · next h => rfl
  · next h => exact absurd h0 h

private theorem atomic_eq (m : ℕ) :
    atomic cantorPresentation m = atomicOfList cantorPresentation (ofNat (List (ℕ × ℕ)) m) :=
  rfl

private theorem atomic_encode (l : List (ℕ × ℕ)) :
    atomic cantorPresentation (Encodable.encode l) = atomicOfList cantorPresentation l := by
  rw [atomic_eq, Denumerable.ofNat_encode]

/-! ### Finite atomic measures on Cantor space -/

/-- A finite weighted sum of Diracs with nonnegative weights summing to `1` is a
probability measure. -/
private theorem isProbabilityMeasure_sum_smul_dirac {k : ℕ} {a : Fin k → ℝ}
    (x : Fin k → Cantor) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) := by
  constructor
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => ha i, hsum, ENNReal.ofReal_one]

/-- Evaluating a finite atomic measure on a measurable set: indicator sums. -/
private theorem sum_smul_dirac_apply {k : ℕ} (a : Fin k → ℝ) (x : Fin k → Cantor)
    {A : Set Cantor} (hA : MeasurableSet A) :
    (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) A
      = ∑ i, A.indicator (fun _ => ENNReal.ofReal (a i)) (x i) := by
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  by_cases hi : x i ∈ A
  · simp [Set.indicator_of_mem hi]
  · simp [Set.indicator_of_notMem hi]

/-! ### Word machinery -/

/-- The repo's `cantorPresentation` has exactly the dense sequence `densePoint`. -/
private theorem cantorPresentation_dense : cantorPresentation.dense = densePoint := rfl

private theorem half_pow_le_half_pow {k n : ℕ} (h : k ≤ n) :
    ((2 : ℝ)⁻¹) ^ n ≤ ((2 : ℝ)⁻¹) ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 : ((2 : ℝ)⁻¹) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ k := by positivity
  nlinarith

/-! #### The level-`n` words -/

/-- All binary words of length `n` (in order), via iteration (primrec-friendly). -/
private def wordsOf (n : ℕ) : List (List Bool) :=
  (fun L => L.flatMap fun s => [s ++ [false], s ++ [true]])^[n] [[]]

private theorem wordsOf_zero : wordsOf 0 = [[]] := rfl

private theorem wordsOf_succ (n : ℕ) :
    wordsOf (n + 1) = (wordsOf n).flatMap fun s => [s ++ [false], s ++ [true]] := by
  rw [wordsOf, Function.iterate_succ_apply']
  rfl

private theorem streamTake_mem_wordsOf (x : Cantor) : ∀ n, streamTake x n ∈ wordsOf n
  | 0 => by simp [streamTake, wordsOf_zero]
  | n + 1 => by
    rw [streamTake_succ, wordsOf_succ]
    refine List.mem_flatMap.mpr ⟨streamTake x n, streamTake_mem_wordsOf x n, ?_⟩
    cases x n <;> simp

private theorem length_of_mem_wordsOf :
    ∀ {n : ℕ} {s : List Bool}, s ∈ wordsOf n → s.length = n
  | 0, s, hs => by
    simp only [wordsOf_zero, List.mem_singleton] at hs
    simp [hs]
  | n + 1, s, hs => by
    rw [wordsOf_succ] at hs
    obtain ⟨t, ht, hst⟩ := List.mem_flatMap.mp hs
    have hlt : t.length = n := length_of_mem_wordsOf ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl <;> simp [hlt]

private theorem sum_map_flatMap_pair (g : List Bool → ℝ) :
    ∀ l : List (List Bool),
      ((l.flatMap fun s => [s ++ [false], s ++ [true]]).map g).sum
        = (l.map fun s => g (s ++ [false]) + g (s ++ [true])).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil]
    rw [sum_map_flatMap_pair g l]
    ring

/-- The level-`n` cylinder masses of a probability measure sum to `1`. -/
private theorem sum_map_wordsOf (μ : ProbabilityMeasure Cantor) :
    ∀ n, ((wordsOf n).map (cylMass μ)).sum = 1
  | 0 => by simp [wordsOf_zero]
  | n + 1 => by
    rw [wordsOf_succ, sum_map_flatMap_pair]
    rw [show ((wordsOf n).map fun s => cylMass μ (s ++ [false]) + cylMass μ (s ++ [true]))
        = (wordsOf n).map (cylMass μ) from
      List.map_congr_left fun s _ => (cylMass_split μ s).symm]
    exact sum_map_wordsOf μ n

private theorem length_wordsOf (n : ℕ) : (wordsOf n).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [wordsOf_succ, List.length_flatMap]
    have hconst : ((wordsOf n).map fun s =>
        ([s ++ [false], s ++ [true]] : List (List Bool)).length)
        = (wordsOf n).map fun _ => 2 := List.map_congr_left fun s _ => rfl
    rw [hconst, List.map_const', List.sum_replicate, smul_eq_mul, ih, pow_succ]

/-! #### The cylinder discretization and its LP bound -/

/-- Every word cylinder has diameter `≤ (1/2)^|s|`. -/
private theorem dist_le_of_mem_cylinder {s : List Bool} {y z : Cantor}
    (hy : y ∈ (cylinder s : Set Cantor)) (hz : z ∈ (cylinder s : Set Cantor)) :
    dist y z ≤ (1 / 2 : ℝ) ^ s.length := by
  have h := cylinder_eq_of_mem hz
  rw [h] at hy
  exact PiNat.mem_cylinder_iff_dist_le.mp hy

/-- The level-`n` cylinder discretization `D_n μ`: mass `cylMass μ s` at the
representative point `wordPoint s`, over all length-`n` words `s`, as a direct Dirac
sum. -/
private noncomputable def discretize (μ : ProbabilityMeasure Cantor) (n : ℕ) :
    ProbabilityMeasure Cantor :=
  ⟨∑ i : Fin (wordsOf n).length,
      ENNReal.ofReal (cylMass μ (wordsOf n)[i]) • Measure.dirac (wordPoint (wordsOf n)[i]),
    isProbabilityMeasure_sum_smul_dirac _ (fun i => cylMass_nonneg μ _)
      (by rw [← listSum_map_eq_finSum (wordsOf n) (cylMass μ)]; exact sum_map_wordsOf μ n)⟩

private theorem toMeasure_discretize (μ : ProbabilityMeasure Cantor) (n : ℕ) :
    (discretize μ n).toMeasure
      = ∑ i : Fin (wordsOf n).length,
          ENNReal.ofReal (cylMass μ (wordsOf n)[i])
            • Measure.dirac (wordPoint (wordsOf n)[i]) := rfl

/-- **The discretization estimate**: `levyProkhorovDist μ (D_n μ) ≤ (1/2)^n`. -/
private theorem levyProkhorovDist_discretize_le (μ : ProbabilityMeasure Cantor) (n : ℕ) :
    levyProkhorovDist μ.toMeasure (discretize μ n).toMeasure ≤ (1 / 2 : ℝ) ^ n := by
  refine levyProkhorovDist_le_of_forall_le _ _ (by positivity) fun ε B hε hB => ?_
  have key : μ.toMeasure B ≤ (discretize μ n).toMeasure (thickening ε B) := by
    have hcover : B ⊆ ⋃ i : Fin (wordsOf n).length, B ∩ cylinder (wordsOf n)[i] := by
      intro x hx
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp (streamTake_mem_wordsOf x n)
      refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx, ?_⟩
      change x ∈ cylinder (wordsOf n)[i]
      rw [hix]
      exact mem_cylinder_streamTake x n
    calc μ.toMeasure B
        ≤ μ.toMeasure (⋃ i : Fin (wordsOf n).length, B ∩ cylinder (wordsOf n)[i]) :=
          measure_mono hcover
      _ ≤ ∑' i : Fin (wordsOf n).length, μ.toMeasure (B ∩ cylinder (wordsOf n)[i]) :=
          measure_iUnion_le _
      _ = ∑ i : Fin (wordsOf n).length, μ.toMeasure (B ∩ cylinder (wordsOf n)[i]) :=
          tsum_fintype _
      _ ≤ ∑ i : Fin (wordsOf n).length,
            (ENNReal.ofReal (cylMass μ (wordsOf n)[i])
              • Measure.dirac (wordPoint (wordsOf n)[i])) (thickening ε B) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rcases Set.eq_empty_or_nonempty (B ∩ cylinder (wordsOf n)[i]) with hemp | hne
          · rw [hemp]
            simp
          · obtain ⟨b, hbB, hbc⟩ := hne
            have hlen : ((wordsOf n)[i] : List Bool).length = n :=
              length_of_mem_wordsOf (List.getElem_mem _)
            have hpt : wordPoint (wordsOf n)[i] ∈ thickening ε B := by
              refine Metric.mem_thickening_iff.mpr ⟨b, hbB, lt_of_le_of_lt ?_ hε⟩
              have hd := dist_le_of_mem_cylinder
                (streamExtend_mem_cylinder ((wordsOf n)[i] : List Bool) fun _ => false) hbc
              rwa [hlen] at hd
            rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem hpt, mul_one]
            calc μ.toMeasure (B ∩ cylinder (wordsOf n)[i])
                ≤ μ.toMeasure (cylinder (wordsOf n)[i]) :=
                  measure_mono Set.inter_subset_right
              _ = ENNReal.ofReal (cylMass μ (wordsOf n)[i]) := by
                  rw [cylMass, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = (discretize μ n).toMeasure (thickening ε B) := by
          rw [toMeasure_discretize, Measure.finsetSum_apply]
  exact key.trans le_self_add

/-! #### Separation: small thickenings of cylinders are the cylinders themselves

The exact separation constant: any `ε ≤ 2 · (2⁻¹)^|s|` (equivalently
`ε ≤ (1/2)^(|s|−1)`) works, since two Cantor points at distance `< (1/2)^m` agree at
all coordinates `≤ m`. -/

private theorem thickening_cylinder_subset {s : List Bool} {ε : ℝ}
    (hε : ε ≤ 2 * ((2 : ℝ)⁻¹) ^ s.length) :
    Metric.thickening ε (cylinder s : Set Cantor) ⊆ cylinder s := by
  rintro y hy i hi
  obtain ⟨x, hxB, hd⟩ := Metric.mem_thickening_iff.mp hy
  obtain ⟨m, hm⟩ : ∃ m, s.length = m + 1 := ⟨s.length - 1, by omega⟩
  have hbound : 2 * ((2 : ℝ)⁻¹) ^ s.length = (1 / 2 : ℝ) ^ m := by
    rw [hm, pow_succ]
    norm_num
    ring
  have hdm : dist y x < (1 / 2 : ℝ) ^ m := lt_of_lt_of_le hd (by rw [← hbound]; exact hε)
  have hagree : y i = x i := PiNat.apply_eq_of_dist_lt hdm (by omega)
  rw [hagree]
  exact hxB i hi

/-- **The LP-to-cylinder-mass estimate**: past the separation threshold `|s| ≤ k`, the
LP defining inequalities collapse on the clopen cylinder, giving
`|μ(cyl s) − ν(cyl s)| ≤ (2⁻¹)^k`. -/
private theorem abs_cylMass_sub_le {μ ν : ProbabilityMeasure Cantor} {s : List Bool}
    {k : ℕ} (hs : s.length ≤ k)
    (h : levyProkhorovDist μ.toMeasure ν.toMeasure ≤ ((2 : ℝ)⁻¹) ^ k) :
    |cylMass μ s - (ν.toMeasure (cylinder s)).toReal| ≤ ((2 : ℝ)⁻¹) ^ k := by
  have hk0 : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ k := by positivity
  have hkey : ∀ t : ℝ, 0 < t →
      |cylMass μ s - (ν.toMeasure (cylinder s)).toReal| ≤ ((2 : ℝ)⁻¹) ^ k + t := by
    intro t ht
    set ε : ℝ := min (((2 : ℝ)⁻¹) ^ k + t) (2 * ((2 : ℝ)⁻¹) ^ s.length) with hε_def
    have hε0 : 0 < ε := lt_min (by linarith) (by positivity)
    have hLPε : levyProkhorovDist μ.toMeasure ν.toMeasure < ε := by
      refine lt_min (by linarith) (lt_of_le_of_lt h ?_)
      have h1 : ((2 : ℝ)⁻¹) ^ k ≤ ((2 : ℝ)⁻¹) ^ s.length := half_pow_le_half_pow hs
      have h2 : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ s.length := by positivity
      linarith
    have hedist : levyProkhorovEDist μ.toMeasure ν.toMeasure < ENNReal.ofReal ε :=
      (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr hLPε
    have hedist' : levyProkhorovEDist ν.toMeasure μ.toMeasure < ENNReal.ofReal ε := by
      rw [levyProkhorovEDist_comm]
      exact hedist
    have hthick : Metric.thickening ((ENNReal.ofReal ε).toReal)
        (cylinder s : Set Cantor) ⊆ cylinder s := by
      rw [ENNReal.toReal_ofReal hε0.le]
      exact thickening_cylinder_subset (min_le_right _ _)
    have h1 : μ.toMeasure (cylinder s)
        ≤ ν.toMeasure (cylinder s) + ENNReal.ofReal ε :=
      (left_measure_le_of_levyProkhorovEDist_lt hedist
        (measurableSet_cylinder s)).trans
        (add_le_add (measure_mono hthick) le_rfl)
    have h2 : ν.toMeasure (cylinder s)
        ≤ μ.toMeasure (cylinder s) + ENNReal.ofReal ε :=
      (left_measure_le_of_levyProkhorovEDist_lt hedist'
        (measurableSet_cylinder s)).trans
        (add_le_add (measure_mono hthick) le_rfl)
    have hr1 : cylMass μ s ≤ (ν.toMeasure (cylinder s)).toReal + ε := by
      have hne : ν.toMeasure (cylinder s) + ENNReal.ofReal ε ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
      have := ENNReal.toReal_mono hne h1
      rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε0.le] at this
    have hr2 : (ν.toMeasure (cylinder s)).toReal ≤ cylMass μ s + ε := by
      have hne : μ.toMeasure (cylinder s) + ENNReal.ofReal ε ≠ ⊤ :=
        ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩
      have := ENNReal.toReal_mono hne h2
      rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hε0.le] at this
    have habs : |cylMass μ s - (ν.toMeasure (cylinder s)).toReal| ≤ ε :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact habs.trans (min_le_left _ _)
  by_contra hcon
  push Not at hcon
  have := hkey ((|cylMass μ s - (ν.toMeasure (cylinder s)).toReal| - ((2 : ℝ)⁻¹) ^ k) / 2)
    (by linarith)
  linarith

/-! ### Coded rational arithmetic

The shared combinators come from `Metric/RatCodeArith.lean`; local here are only the
positive-division rider `divPosCode` and the `wRaw` restatement of the clamp spec. -/

/-- The clamp spec of `Metric/RatCodeArith.lean` restated through the local
abbreviation `wRaw`. -/
private theorem ratOfCode_clampCode_wRaw (m : ℕ) : ratOfCode (clampCode m) = wRaw m :=
  ratOfCode_clampCode m

/-- A rational code decodes to `0` exactly when its two numerator slots agree. -/
private theorem ratOfCode_eq_zero_iff (m : ℕ) :
    ratOfCode m = 0 ↔ m.unpair.1.unpair.1 = m.unpair.1.unpair.2 := by
  have hden : ((m.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  rw [ratOfCode, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact_mod_cast sub_eq_zero.mp h
    · exact absurd h hden
  · intro h
    exact Or.inl (sub_eq_zero.mpr (by exact_mod_cast h))

/-- Division of a rational code by one with positive decoded value (numerator slots
`b < a`); unnormalized fraction arithmetic. -/
private def divPosCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair (m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1))
      (m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1)))
    ((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1)

private theorem ratOfCode_divPosCode (m₁ m₂ : ℕ)
    (h : m₂.unpair.1.unpair.2 < m₂.unpair.1.unpair.1) :
    ratOfCode (divPosCode m₁ m₂) = ratOfCode m₁ / ratOfCode m₂ := by
  have hsub : ((m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2 : ℕ) : ℚ)
      = (m₂.unpair.1.unpair.1 : ℚ) - (m₂.unpair.1.unpair.2 : ℚ) := Nat.cast_sub h.le
  have hposQ : (0 : ℚ) < (m₂.unpair.1.unpair.1 : ℚ) - (m₂.unpair.1.unpair.2 : ℚ) := by
    have hlt : (m₂.unpair.1.unpair.2 : ℚ) < (m₂.unpair.1.unpair.1 : ℚ) := by exact_mod_cast h
    linarith
  have h1 : 1 ≤ (m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero _) (by omega))
  have hden :
      (((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1 : ℕ) : ℚ)
        + 1
      = ((m₁.unpair.2 : ℚ) + 1)
          * ((m₂.unpair.1.unpair.1 : ℚ) - (m₂.unpair.1.unpair.2 : ℚ)) := by
    have h2 : ((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1) + 1
        = (m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) :=
      Nat.succ_pred_eq_of_pos h1
    calc (((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1 : ℕ) : ℚ)
          + 1
        = ((((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) - 1) + 1
            : ℕ) : ℚ) := by push_cast; ring
      _ = (((m₁.unpair.2 + 1) * (m₂.unpair.1.unpair.1 - m₂.unpair.1.unpair.2) : ℕ) : ℚ) := by
          rw [h2]
      _ = ((m₁.unpair.2 : ℚ) + 1)
            * ((m₂.unpair.1.unpair.1 : ℚ) - (m₂.unpair.1.unpair.2 : ℚ)) := by
          rw [Nat.cast_mul, hsub]
          push_cast
          ring
  have hd1 : ((m₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have hd2 : ((m₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  rw [ratOfCode, ratOfCode, ratOfCode, divPosCode]
  simp only [Nat.unpair_pair]
  rw [hden]
  push_cast
  field_simp [hd1, hd2, hposQ.ne']

private theorem primrec₂_divPosCode : Primrec₂ divPosCode := by
  have a₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp Primrec.fst
  have b₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp Primrec.fst
  have a₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp Primrec.snd
  have b₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp Primrec.snd
  have d₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.2 + 1 :=
    Primrec.succ.comp (primrec_unpairSnd.comp Primrec.fst)
  have d₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.2 + 1 :=
    Primrec.succ.comp (primrec_unpairSnd.comp Primrec.snd)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec.nat_mul.comp a₁ d₂) (Primrec.nat_mul.comp b₁ d₂))
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp d₁ (Primrec.nat_sub.comp a₂ b₂))
      (Primrec.const 1))

/-! ### Direction B: from weak names to exact cylinder masses -/

/-- Decidable membership of a `false`-padded word in a word cylinder: the padded word
restricted to the first `|s|` coordinates must be `s`. -/
private def inCylB (w s : List Bool) : Bool :=
  decide (((List.range s.length).map fun i => w.getD i false) = s)

private theorem inCylB_iff_mem {w s : List Bool} :
    inCylB w s = true ↔ wordPoint w ∈ (cylinder s : Set Cantor) := by
  rw [inCylB, decide_eq_true_eq]
  constructor
  · intro h i hi
    rw [wordPoint_apply]
    calc w.getD i false
        = (((List.range s.length).map fun j => w.getD j false)[i]'(by simpa using hi)) := by
          simp
      _ = s[i] := List.getElem_of_eq h _
  · intro h
    refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
    have hcoord := h i h₂
    rw [wordPoint_apply] at hcoord
    simpa using hcoord

private theorem primrec₂_inCylB : Primrec₂ inCylB := by
  have hmap : Primrec fun p : List Bool × List Bool =>
      (List.range p.2.length).map fun i => p.1.getD i false :=
    Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.snd))
      (((Primrec.list_getD false).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  have hpred : PrimrecPred fun p : List Bool × List Bool =>
      ((List.range p.2.length).map fun i => p.1.getD i false) = p.2 :=
    Primrec.eq.comp hmap Primrec.snd
  obtain ⟨_, hraw⟩ := hpred
  exact hraw.of_eq fun p => decide_eq_decide.mpr Iff.rfl

/-- The exact rational cylinder mass of a decoded atomic measure. -/
private def cylWtQ (l : List (ℕ × ℕ)) (s : List Bool) : ℚ :=
  if wSumL l = 0 then cond (inCylB (denseWord 0) s) 1 0
  else (l.map fun pr => cond (inCylB (denseWord pr.1) s) (wRaw pr.2) 0).sum / wSumL l

private theorem cylWtQ_nonneg (l : List (ℕ × ℕ)) (s : List Bool) : 0 ≤ cylWtQ l s := by
  rw [cylWtQ]
  split_ifs with h0
  · cases inCylB (denseWord 0) s
    · simp
    · simp
  · have hpos : (0 : ℚ) < wSumL l := lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
    refine div_nonneg (List.sum_nonneg fun x hx => ?_) hpos.le
    obtain ⟨pr, -, rfl⟩ := List.mem_map.mp hx
    cases inCylB (denseWord pr.1) s
    · simp
    · simpa using wRaw_nonneg pr.2

/-- Casting a rational quotient sum. -/
private theorem cast_sum_div {n : ℕ} (a : Fin n → ℚ) (S : ℚ) :
    (((∑ i, a i) / S : ℚ) : ℝ) = ∑ i, ((a i / S : ℚ) : ℝ) := by
  push_cast
  rw [Finset.sum_div]

/-- **Exact evaluation**: the decoded atomic measure of a word cylinder is the rational
`cylWtQ`. -/
private theorem toMeasure_atomicOfList_cylinder (l : List (ℕ × ℕ)) (s : List Bool) :
    (atomicOfList cantorPresentation l).toMeasure (cylinder s)
      = ENNReal.ofReal ((cylWtQ l s : ℚ) : ℝ) := by
  by_cases h0 : wSumL l = 0
  · rw [toMeasure_atomicOfList_of_eq h0, cylWtQ, if_pos h0,
      show cantorPresentation.dense 0 = densePoint 0 from congrFun cantorPresentation_dense 0,
      Measure.dirac_apply' _ (measurableSet_cylinder s)]
    by_cases hmem : densePoint 0 ∈ (cylinder s : Set Cantor)
    · rw [Set.indicator_of_mem hmem, inCylB_iff_mem.mpr hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem,
        show inCylB (denseWord 0) s = false from
          Bool.eq_false_iff.mpr fun hc => hmem (inCylB_iff_mem.mp hc)]
      norm_num
  · have hpos : (0 : ℚ) < wSumL l := lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm h0)
    rw [toMeasure_atomicOfList_of_ne h0,
      sum_smul_dirac_apply _ _ (measurableSet_cylinder s), cylWtQ, if_neg h0]
    have hterm : ∀ i : Fin l.length,
        (cylinder s : Set Cantor).indicator
            (fun _ => ENNReal.ofReal ((wRaw l[i].2 / wSumL l : ℚ) : ℝ))
            (cantorPresentation.dense l[i].1)
          = ENNReal.ofReal
              (((cond (inCylB (denseWord l[i].1) s) (wRaw l[i].2) 0 / wSumL l : ℚ)) : ℝ) := by
      intro i
      have hdp : cantorPresentation.dense l[i].1 = wordPoint (denseWord l[i].1) :=
        congrFun cantorPresentation_dense l[i].1
      by_cases hc : inCylB (denseWord l[i].1) s = true
      · rw [hc, cond_true, Set.indicator_of_mem (by rw [hdp]; exact inCylB_iff_mem.mp hc)]
      · rw [Bool.eq_false_iff.mpr hc, cond_false,
          Set.indicator_of_notMem
            (by rw [hdp]; exact fun hmem => hc (inCylB_iff_mem.mpr hmem)),
          zero_div]
        simp
    rw [Finset.sum_congr rfl fun i _ => hterm i,
      ← ENNReal.ofReal_sum_of_nonneg fun i _ => by
        refine Rat.cast_nonneg.mpr (div_nonneg ?_ hpos.le)
        cases inCylB (denseWord l[i].1) s
        · simp
        · simpa using wRaw_nonneg l[i].2]
    congr 1
    rw [listSum_map_eq_finSum l fun pr => cond (inCylB (denseWord pr.1) s) (wRaw pr.2) 0,
      cast_sum_div]

/-- The total rational code of a decoded list's clamped weights. -/
private theorem ratOfCode_sumCode_clamp (l : List (ℕ × ℕ)) :
    ratOfCode (sumCode (l.map fun pr => clampCode pr.2)) = wSumL l := by
  rw [ratOfCode_sumCode, List.map_map, wSumL]
  congr 1
  exact List.map_congr_left fun pr _ => ratOfCode_clampCode_wRaw pr.2

private theorem ratOfCode_sumCode_sel (l : List (ℕ × ℕ)) (s : List Bool) :
    ratOfCode (sumCode (l.map fun pr =>
        cond (inCylB (denseWord pr.1) s) (clampCode pr.2) zeroCode))
      = (l.map fun pr => cond (inCylB (denseWord pr.1) s) (wRaw pr.2) 0).sum := by
  rw [ratOfCode_sumCode, List.map_map]
  congr 1
  refine List.map_congr_left fun pr _ => ?_
  change ratOfCode (cond (inCylB (denseWord pr.1) s) (clampCode pr.2) zeroCode)
      = cond (inCylB (denseWord pr.1) s) (wRaw pr.2) 0
  cases hc : inCylB (denseWord pr.1) s
  · rw [cond_false, cond_false, ratOfCode_zeroCode]
  · rw [cond_true, cond_true]
    exact ratOfCode_clampCode_wRaw pr.2

/-- The cylinder-weight code: an exact rational code of `cylWtQ`, total in `(l, s)`. -/
private def cylWtCode (l : List (ℕ × ℕ)) (s : List Bool) : ℕ :=
  if (sumCode (l.map fun pr => clampCode pr.2)).unpair.1.unpair.1
      = (sumCode (l.map fun pr => clampCode pr.2)).unpair.1.unpair.2 then
    cond (inCylB (denseWord 0) s) oneCode zeroCode
  else
    divPosCode
      (sumCode (l.map fun pr =>
        cond (inCylB (denseWord pr.1) s) (clampCode pr.2) zeroCode))
      (sumCode (l.map fun pr => clampCode pr.2))

private theorem ratOfCode_cylWtCode (l : List (ℕ × ℕ)) (s : List Bool) :
    ratOfCode (cylWtCode l s) = cylWtQ l s := by
  set S := sumCode (l.map fun pr => clampCode pr.2) with hS_def
  have hSval : ratOfCode S = wSumL l := ratOfCode_sumCode_clamp l
  by_cases h0 : S.unpair.1.unpair.1 = S.unpair.1.unpair.2
  · have hw0 : wSumL l = 0 := by
      rw [← hSval]
      exact (ratOfCode_eq_zero_iff S).mpr h0
    rw [cylWtCode, if_pos h0, cylWtQ, if_pos hw0]
    cases inCylB (denseWord 0) s
    · simpa using ratOfCode_zeroCode
    · simpa using ratOfCode_oneCode
  · have hw0 : wSumL l ≠ 0 := fun hw =>
      h0 ((ratOfCode_eq_zero_iff S).mp (hSval.trans hw))
    have hSpos : (0 : ℚ) < ratOfCode S := by
      rw [hSval]
      exact lt_of_le_of_ne (wSumL_nonneg l) (Ne.symm hw0)
    have hba : S.unpair.1.unpair.2 < S.unpair.1.unpair.1 := by
      by_contra hle
      push Not at hle
      have hnp : ratOfCode S ≤ 0 := by
        rw [ratOfCode]
        refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
        have hcast : (S.unpair.1.unpair.1 : ℚ) ≤ (S.unpair.1.unpair.2 : ℚ) := by
          exact_mod_cast hle
        linarith
      linarith
    rw [cylWtCode, if_neg h0, ratOfCode_divPosCode _ _ hba, ratOfCode_sumCode_sel, hSval,
      cylWtQ, if_neg hw0]

private theorem primrec₂_cylWtCode : Primrec₂ cylWtCode := by
  have hS : Primrec fun p : List (ℕ × ℕ) × List Bool =>
      sumCode (p.1.map fun pr => clampCode pr.2) :=
    primrec_sumCode.comp (Primrec.list_map Primrec.fst
      ((primrec_clampCode.comp (Primrec.snd.comp Primrec.snd)).to₂))
  have htest : PrimrecPred fun p : List (ℕ × ℕ) × List Bool =>
      (sumCode (p.1.map fun pr => clampCode pr.2)).unpair.1.unpair.1
        = (sumCode (p.1.map fun pr => clampCode pr.2)).unpair.1.unpair.2 :=
    Primrec.eq.comp ((primrec_unpairFst.comp primrec_unpairFst).comp hS)
      ((primrec_unpairSnd.comp primrec_unpairFst).comp hS)
  have hthen : Primrec fun p : List (ℕ × ℕ) × List Bool =>
      cond (inCylB (denseWord 0) p.2) oneCode zeroCode :=
    Primrec.cond (primrec₂_inCylB.comp (Primrec.const (denseWord 0)) Primrec.snd)
      (Primrec.const oneCode) (Primrec.const zeroCode)
  have hNum : Primrec fun p : List (ℕ × ℕ) × List Bool =>
      sumCode (p.1.map fun pr =>
        cond (inCylB (denseWord pr.1) p.2) (clampCode pr.2) zeroCode) :=
    primrec_sumCode.comp (Primrec.list_map Primrec.fst
      ((Primrec.cond
        (primrec₂_inCylB.comp
          (primrec_denseWord.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.snd.comp Primrec.fst))
        (primrec_clampCode.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.const zeroCode)).to₂))
  exact Primrec.ite htest hthen (primrec₂_divPosCode.comp hNum hS)

private theorem realPresentation_dense_eq (j : ℕ) :
    realPresentation.dense j = ((ratOfCode j : ℚ) : ℝ) := rfl

/-- **Direction B**: weak names compute `cantorMeasureRep` names — component `(s, n)` is
the exact rational cylinder mass of the decoded atomic at stage `|s| + n`. -/
private theorem computableMap_weak_to_cantor :
    ComputableMap (weakMeasureRep cantorPresentation) cantorMeasureRep id := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode
    (b := fun m _ => (denseWord m.unpair.1).length + m.unpair.2 + 1)
    (g := fun w => cylWtCode
      (ofNat (List (ℕ × ℕ)) ((ofNat (List ℕ) w.unpair.2).getD
        ((denseWord w.unpair.1.unpair.1).length + w.unpair.1.unpair.2) 0))
      (denseWord w.unpair.1.unpair.1))
    (Primrec.succ.comp (Primrec.nat_add.comp
      (Primrec.list_length.comp (primrec_denseWord.comp (primrec_unpairFst.comp Primrec.fst)))
      (primrec_unpairSnd.comp Primrec.fst)))
    (by
      have hsWord : Primrec fun w : ℕ => denseWord w.unpair.1.unpair.1 :=
        primrec_denseWord.comp (primrec_unpairFst.comp primrec_unpairFst)
      have hk : Primrec fun w : ℕ =>
          (denseWord w.unpair.1.unpair.1).length + w.unpair.1.unpair.2 :=
        Primrec.nat_add.comp (Primrec.list_length.comp hsWord)
          (primrec_unpairSnd.comp primrec_unpairFst)
      have hlCode : Primrec fun w : ℕ =>
          (ofNat (List ℕ) w.unpair.2).getD
            ((denseWord w.unpair.1.unpair.1).length + w.unpair.1.unpair.2) 0 :=
        (Primrec.list_getD 0).comp
          ((Primrec.ofNat (List ℕ)).comp primrec_unpairSnd) hk
      exact primrec₂_cylWtCode.comp
        ((Primrec.ofNat (List (ℕ × ℕ))).comp hlCode) hsWord)
  have hcomp : c.Computes fun p m =>
      cylWtCode (ofNat (List (ℕ × ℕ)) (p ((denseWord m.unpair.1).length + m.unpair.2)))
        (denseWord m.unpair.1) := by
    intro p m
    rw [hc p m]
    simp only [Nat.unpair_pair, ofNat_encode, streamTake_getD p (Nat.lt_succ_self _)]
  refine ⟨c, .of_computes hcomp fun p μ hp => ?_⟩
  have hW : WeakMeasureNames cantorPresentation p μ :=
    (weakMeasureRep_names_iff cantorPresentation).mp hp
  refine cantorMeasureRep_names_iff.mpr fun s => ?_
  refine Representation.subtype_names_iff.mpr ?_
  refine (realPresentation.cauchyRep_names_iff).mpr fun n => ?_
  rw [realPresentation_dense_eq, Real.dist_eq]
  simp only [Nat.unpair_pair, denseWord_encode]
  set k : ℕ := s.length + n with hk_def
  set l : List (ℕ × ℕ) := ofNat (List (ℕ × ℕ)) (p k) with hl_def
  rw [ratOfCode_cylWtCode]
  have hev : ((atomicOfList cantorPresentation l).toMeasure (cylinder s)).toReal
      = ((cylWtQ l s : ℚ) : ℝ) := by
    rw [toMeasure_atomicOfList_cylinder,
      ENNReal.toReal_ofReal (by exact_mod_cast cylWtQ_nonneg l s)]
  have hLP : levyProkhorovDist μ.toMeasure (atomicOfList cantorPresentation l).toMeasure
      ≤ ((2 : ℝ)⁻¹) ^ k := by
    rw [hl_def, ← atomic_eq]
    exact hW k
  have habs := abs_cylMass_sub_le (Nat.le_add_right s.length n) hLP
  rw [hev, abs_sub_comm] at habs
  exact habs.trans (half_pow_le_half_pow (Nat.le_add_left n s.length))

/-! ### Direction A: from measure names to weak names -/

/-- Component estimate extracted from a `cantorMeasureRep` name. -/
private theorem measureNames_est {F : Baire} {μ : ProbabilityMeasure Cantor}
    (hF : MeasureNames F μ) (s : List Bool) (j : ℕ) :
    |((ratOfCode (F (Nat.pair (Encodable.encode s) j)) : ℚ) : ℝ) - cylMass μ s|
      ≤ ((2 : ℝ)⁻¹) ^ j := by
  have h1 := Representation.subtype_names_iff.mp (hF s)
  have h2 := (realPresentation.cauchyRep_names_iff).mp h1 j
  rwa [realPresentation_dense_eq, Real.dist_eq,
    show (cylMass01 μ s).val = cylMass μ s from rfl] at h2

/-- **The renormalization estimate**: rational `η`-approximations of a probability
vector, renormalized by their (nonzero) sum, stay within total variation `2Kη`. -/
private theorem sum_abs_sub_normalized_le {K : ℕ} (a : Fin K → ℝ) (q : Fin K → ℚ)
    {η : ℝ}
    (hsum : ∑ i, a i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hqd : ∀ i, |(q i : ℝ) - a i| ≤ η)
    (hKη : (K : ℝ) * η ≤ 1 / 4) :
    (∑ j, q j : ℚ) ≠ 0 ∧
      ∑ i, |a i - ((q i / ∑ j, q j : ℚ) : ℝ)| ≤ 2 * ((K : ℝ) * η) := by
  have hcast : ((∑ i, q i : ℚ) : ℝ) = ∑ i, (q i : ℝ) := by push_cast; rfl
  have hΔ : ∑ i, |(q i : ℝ) - a i| ≤ (K : ℝ) * η := by
    calc ∑ i, |(q i : ℝ) - a i|
        ≤ ∑ _i : Fin K, η := Finset.sum_le_sum fun i _ => hqd i
      _ = (K : ℝ) * η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS1 : |((∑ i, q i : ℚ) : ℝ) - 1| ≤ ∑ i, |(q i : ℝ) - a i| := by
    have h1 : ((∑ i, q i : ℚ) : ℝ) - 1 = ∑ i, ((q i : ℝ) - a i) := by
      rw [hcast, Finset.sum_sub_distrib, hsum]
    rw [h1]
    exact Finset.abs_sum_le_sum_abs _ _
  have hS34 : (3 / 4 : ℝ) ≤ ((∑ i, q i : ℚ) : ℝ) := by
    have h := abs_le.mp (hS1.trans (hΔ.trans hKη))
    linarith [h.1]
  have hSR : (0 : ℝ) < ((∑ i, q i : ℚ) : ℝ) := lt_of_lt_of_le (by norm_num) hS34
  have hSQ : (0 : ℚ) < ∑ j, q j := by exact_mod_cast hSR
  have hSne : (∑ i, q i : ℚ) ≠ 0 := hSQ.ne'
  refine ⟨hSne, ?_⟩
  have hq0R : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast hq0 i
  have hterm : ∀ i : Fin K,
      |a i - ((q i / ∑ j, q j : ℚ) : ℝ)|
        ≤ |(q i : ℝ) - a i|
          + (q i : ℝ) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ)) := by
    intro i
    have hql : ((q i / ∑ j, q j : ℚ) : ℝ) = (q i : ℝ) / ((∑ j, q j : ℚ) : ℝ) := by
      push_cast
      rfl
    have hdiff : (q i : ℝ) - (q i : ℝ) / ((∑ j, q j : ℚ) : ℝ)
        = (q i : ℝ) * ((((∑ j, q j : ℚ) : ℝ) - 1) / ((∑ j, q j : ℚ) : ℝ)) := by
      field_simp
    have h2 : |(q i : ℝ) - ((q i / ∑ j, q j : ℚ) : ℝ)|
        = (q i : ℝ) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ)) := by
      rw [hql, hdiff, abs_mul, abs_div, abs_of_nonneg (hq0R i), abs_of_pos hSR]
    calc |a i - ((q i / ∑ j, q j : ℚ) : ℝ)|
        ≤ |a i - (q i : ℝ)| + |(q i : ℝ) - ((q i / ∑ j, q j : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ = |(q i : ℝ) - a i|
            + (q i : ℝ) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ)) := by
          rw [abs_sub_comm, h2]
  have habs : |((∑ j, q j : ℚ) : ℝ) - 1| ≤ (K : ℝ) * η := hS1.trans hΔ
  calc ∑ i, |a i - ((q i / ∑ j, q j : ℚ) : ℝ)|
      ≤ ∑ i, (|(q i : ℝ) - a i|
          + (q i : ℝ) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, |(q i : ℝ) - a i|)
          + (∑ i, (q i : ℝ)) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = (∑ i, |(q i : ℝ) - a i|) + |((∑ j, q j : ℚ) : ℝ) - 1| := by
        rw [← hcast, ← mul_div_assoc, mul_div_cancel_left₀ _ hSR.ne']
    _ ≤ (K : ℝ) * η + (K : ℝ) * η := add_le_add hΔ habs
    _ = 2 * ((K : ℝ) * η) := by ring

/-- The direction-A output list at precision `n`: level-`(n+2)` words with the raw
weight codes read off the name at packed precision `2n+5`. -/
private def approxList (F : Baire) (n : ℕ) : List (ℕ × ℕ) :=
  (wordsOf (n + 2)).map fun s =>
    (Encodable.encode s, F (Nat.pair (Encodable.encode s) (2 * n + 5)))

private theorem two_pow_bound (n : ℕ) :
    ((2 : ℝ) ^ (n + 2)) * ((2 : ℝ)⁻¹) ^ (2 * n + 5) = ((2 : ℝ)⁻¹) ^ (n + 3) := by
  have h : 2 * n + 5 = (n + 2) + (n + 3) := by ring
  rw [h, pow_add ((2 : ℝ)⁻¹) (n + 2) (n + 3), ← mul_assoc, ← mul_pow]
  norm_num

/-- Evaluating an atomic on a mapped index list. -/
private theorem toMeasure_atomicOfList_map {β : Type*} (t : List β) (g : β → ℕ × ℕ)
    (h0 : wSumL (t.map g) ≠ 0) :
    (atomicOfList cantorPresentation (t.map g)).toMeasure
      = ∑ i : Fin t.length,
          ENNReal.ofReal ((wRaw (g t[i]).2 / wSumL (t.map g) : ℚ) : ℝ)
            • Measure.dirac (cantorPresentation.dense (g t[i]).1) := by
  rw [toMeasure_atomicOfList_of_ne h0]
  have hlen : (t.map g).length = t.length := by simp
  rw [← Fin.sum_congr' _ hlen]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp [List.getElem_map]

/-- **The direction-A estimate**: the stage-`n` approximation list names a measure at LP
distance `≤ (2⁻¹)^n` from `μ` — discretization cost `(2⁻¹)^(n+2)` plus renormalized
weight cost `2·2^(n+2)·(2⁻¹)^(2n+5) = (2⁻¹)^(n+2)`. -/
private theorem levyProkhorov_approxList_le {F : Baire} {μ : ProbabilityMeasure Cantor}
    (hF : MeasureNames F μ) (n : ℕ) :
    levyProkhorovDist μ.toMeasure
        (atomic cantorPresentation (Encodable.encode (approxList F n))).toMeasure
      ≤ ((2 : ℝ)⁻¹) ^ n := by
  classical
  have hqd : ∀ i : Fin (wordsOf (n + 2)).length,
      |((wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5))) : ℚ) : ℝ)
          - cylMass μ (wordsOf (n + 2))[i]|
        ≤ ((2 : ℝ)⁻¹) ^ (2 * n + 5) := by
    intro i
    have hest := measureNames_est hF (wordsOf (n + 2))[i] (2 * n + 5)
    have hcast : ((wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5)))
          : ℚ) : ℝ)
        = max 0 (min 1
            ((ratOfCode (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5)))
              : ℚ) : ℝ)) := by
      rw [wRaw]
      push_cast
      rfl
    have hclamp_a : max 0 (min 1 (cylMass μ (wordsOf (n + 2))[i]))
        = cylMass μ (wordsOf (n + 2))[i] := by
      rw [min_eq_right (cylMass_le_one μ _), max_eq_right (cylMass_nonneg μ _)]
    calc |((wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5))) : ℚ) : ℝ)
          - cylMass μ (wordsOf (n + 2))[i]|
        = |max 0 (min 1
              ((ratOfCode (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5)))
                : ℚ) : ℝ))
            - max 0 (min 1 (cylMass μ (wordsOf (n + 2))[i]))| := by
          rw [hcast, hclamp_a]
      _ ≤ |((ratOfCode (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5)))
              : ℚ) : ℝ) - cylMass μ (wordsOf (n + 2))[i]| := abs_clamp_sub_clamp_le _ _
      _ ≤ ((2 : ℝ)⁻¹) ^ (2 * n + 5) := hest
  have hKcast : (((wordsOf (n + 2)).length : ℕ) : ℝ) = (2 : ℝ) ^ (n + 2) := by
    rw [length_wordsOf]
    push_cast
    ring
  have hKη : (((wordsOf (n + 2)).length : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (2 * n + 5) ≤ 1 / 4 := by
    rw [hKcast, two_pow_bound n]
    calc ((2 : ℝ)⁻¹) ^ (n + 3) ≤ ((2 : ℝ)⁻¹) ^ 2 :=
          half_pow_le_half_pow (by omega)
      _ = 1 / 4 := by norm_num
  obtain ⟨hSne, hsum_le⟩ :=
    sum_abs_sub_normalized_le
      (a := fun i : Fin (wordsOf (n + 2)).length => cylMass μ (wordsOf (n + 2))[i])
      (q := fun i : Fin (wordsOf (n + 2)).length =>
        wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5))))
      (by
        rw [← listSum_map_eq_finSum (wordsOf (n + 2)) (cylMass μ)]
        exact sum_map_wordsOf μ (n + 2))
      (fun i => wRaw_nonneg _) hqd hKη
  have hwS : wSumL (approxList F n)
      = ∑ i : Fin (wordsOf (n + 2)).length,
          wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5))) := by
    simp only [approxList, wSumL, List.map_map]
    rw [listSum_map_eq_finSum]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hS0 : wSumL (approxList F n) ≠ 0 := by
    rw [hwS]
    exact hSne
  have hdw : ∀ s : List Bool,
      cantorPresentation.dense (Encodable.encode s) = wordPoint s := by
    intro s
    rw [congrFun cantorPresentation_dense (Encodable.encode s), densePoint, denseWord_encode]
  have hQ : (atomic cantorPresentation (Encodable.encode (approxList F n))).toMeasure
      = ∑ i : Fin (wordsOf (n + 2)).length,
          ENNReal.ofReal
            ((wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5)))
                / ∑ jj : Fin (wordsOf (n + 2)).length,
                    wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[jj]) (2 * n + 5)))
              : ℚ) : ℝ)
            • Measure.dirac (wordPoint (wordsOf (n + 2))[i]) := by
    rw [atomic_encode]
    have hal : approxList F n = (wordsOf (n + 2)).map fun s =>
        (Encodable.encode s, F (Nat.pair (Encodable.encode s) (2 * n + 5))) := rfl
    rw [hal] at hS0 ⊢
    rw [toMeasure_atomicOfList_map _ _ hS0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdw, ← hal, hwS]
  have hd1 : levyProkhorovDist μ.toMeasure (discretize μ (n + 2)).toMeasure
      ≤ (1 / 2 : ℝ) ^ (n + 2) := levyProkhorovDist_discretize_le μ (n + 2)
  have hd2 : levyProkhorovDist (discretize μ (n + 2)).toMeasure
        (atomic cantorPresentation (Encodable.encode (approxList F n))).toMeasure
      ≤ ∑ i : Fin (wordsOf (n + 2)).length,
          |cylMass μ (wordsOf (n + 2))[i]
            - ((wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[i]) (2 * n + 5)))
                / ∑ jj : Fin (wordsOf (n + 2)).length,
                    wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[jj]) (2 * n + 5)))
              : ℚ) : ℝ)| := by
    refine levyProkhorovDist_le_sum_abs
      (fun i : Fin (wordsOf (n + 2)).length => wordPoint (wordsOf (n + 2))[i])
      _ _ ?_ _ _ (toMeasure_discretize μ (n + 2)) hQ
    intro i
    have hSpos : (0 : ℚ) < ∑ jj : Fin (wordsOf (n + 2)).length,
        wRaw (F (Nat.pair (Encodable.encode (wordsOf (n + 2))[jj]) (2 * n + 5))) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun jj _ => wRaw_nonneg _) (Ne.symm hSne)
    exact_mod_cast div_nonneg (wRaw_nonneg _) hSpos.le
  have e1 : ((2 : ℝ)⁻¹) ^ (n + 3) = ((2 : ℝ)⁻¹) ^ (n + 2) * 2⁻¹ := pow_succ _ _
  have e2 : ((2 : ℝ)⁻¹) ^ (n + 2) = ((2 : ℝ)⁻¹) ^ (n + 1) * 2⁻¹ := pow_succ _ _
  have e3 : ((2 : ℝ)⁻¹) ^ (n + 1) = ((2 : ℝ)⁻¹) ^ n * 2⁻¹ := pow_succ _ _
  have hp : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
  have hhalf : ((1 : ℝ) / 2) ^ (n + 2) = ((2 : ℝ)⁻¹) ^ (n + 2) := by norm_num
  have hKη_eq : (((wordsOf (n + 2)).length : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (2 * n + 5)
      = ((2 : ℝ)⁻¹) ^ (n + 3) := by
    rw [hKcast, two_pow_bound n]
  calc levyProkhorovDist μ.toMeasure
        (atomic cantorPresentation (Encodable.encode (approxList F n))).toMeasure
      ≤ levyProkhorovDist μ.toMeasure (discretize μ (n + 2)).toMeasure
        + levyProkhorovDist (discretize μ (n + 2)).toMeasure
            (atomic cantorPresentation (Encodable.encode (approxList F n))).toMeasure :=
        levyProkhorovDist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ (n + 2)
        + 2 * ((((wordsOf (n + 2)).length : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (2 * n + 5)) :=
        add_le_add hd1 (hd2.trans hsum_le)
    _ ≤ ((2 : ℝ)⁻¹) ^ n := by
        rw [hhalf, hKη_eq]
        linarith

/-- The prefix-length bound of the direction-A realizer. -/
private def maxPairIdx (n : ℕ) : ℕ :=
  ((wordsOf (n + 2)).map fun s => Nat.pair (Encodable.encode s) (2 * n + 5)).foldr max 0

private theorem le_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max hx') (le_max_right _ _)

private theorem lt_maxPairIdx_succ {n : ℕ} {s : List Bool} (hs : s ∈ wordsOf (n + 2)) :
    Nat.pair (Encodable.encode s) (2 * n + 5) < maxPairIdx n + 1 :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_map.mpr ⟨s, hs, rfl⟩))

private theorem primrec_wordsOf : Primrec wordsOf := by
  have hstep : Primrec₂ fun (_ : ℕ) (L : List (List Bool)) =>
      L.flatMap fun s => [s ++ [false], s ++ [true]] := by
    have hinner : Primrec₂ fun (_ : ℕ × List (List Bool)) (s : List Bool) =>
        ([s ++ [false], s ++ [true]] : List (List Bool)) :=
      (Primrec.list_cons.comp
        (Primrec.list_append.comp Primrec.snd (Primrec.const [false]))
        (Primrec.list_cons.comp
          (Primrec.list_append.comp Primrec.snd (Primrec.const [true]))
          (Primrec.const []))).to₂
    exact (Primrec.list_flatMap Primrec.snd hinner).to₂
  exact (Primrec.nat_iterate Primrec.id (Primrec.const [[]]) hstep).of_eq fun n => rfl

private theorem primrec_maxPairIdx : Primrec maxPairIdx := by
  have hmap : Primrec fun n : ℕ =>
      (wordsOf (n + 2)).map fun s => Nat.pair (Encodable.encode s) (2 * n + 5) :=
    Primrec.list_map
      (primrec_wordsOf.comp (Primrec.nat_add.comp Primrec.id (Primrec.const 2)))
      ((Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
          (Primrec.const 5))).to₂)
  exact (Primrec.list_foldr hmap (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun n => rfl

/-- **Direction A**: `cantorMeasureRep` names compute weak names — output coordinate `n`
is the encoded level-`(n+2)` approximation list read at packed precision `2n+5`. -/
private theorem computableMap_cantor_to_weak :
    ComputableMap cantorMeasureRep (weakMeasureRep cantorPresentation) id := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode
    (b := fun n _ => maxPairIdx n + 1)
    (g := fun w => Encodable.encode
      ((wordsOf (w.unpair.1 + 2)).map fun s =>
        (Encodable.encode s,
          (ofNat (List ℕ) w.unpair.2).getD
            (Nat.pair (Encodable.encode s) (2 * w.unpair.1 + 5)) 0)))
    (Primrec.succ.comp (primrec_maxPairIdx.comp Primrec.fst))
    (by
      have hwords : Primrec fun w : ℕ => wordsOf (w.unpair.1 + 2) :=
        primrec_wordsOf.comp
          (Primrec.nat_add.comp primrec_unpairFst (Primrec.const 2))
      have hinner : Primrec₂ fun (w : ℕ) (s : List Bool) =>
          (Encodable.encode s,
            (ofNat (List ℕ) w.unpair.2).getD
              (Nat.pair (Encodable.encode s) (2 * w.unpair.1 + 5)) 0) :=
        (Primrec.pair (Primrec.encode.comp Primrec.snd)
          ((Primrec.list_getD 0).comp
            ((Primrec.ofNat (List ℕ)).comp (primrec_unpairSnd.comp Primrec.fst))
            (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp (Primrec.const 2)
                  (primrec_unpairFst.comp Primrec.fst))
                (Primrec.const 5))))).to₂
      exact Primrec.encode.comp (Primrec.list_map hwords hinner))
  have hcomp : c.Computes fun F n => Encodable.encode (approxList F n) := by
    intro F n
    rw [hc F n]
    simp only [Nat.unpair_pair, ofNat_encode]
    rw [approxList]
    refine congrArg Part.some (congrArg (Encodable.encode (α := List (ℕ × ℕ)))
      (List.map_congr_left fun s hs => ?_))
    rw [streamTake_getD F (lt_maxPairIdx_succ hs)]
  refine ⟨c, .of_computes hcomp fun F μ hF => ?_⟩
  have hM : MeasureNames F μ := cantorMeasureRep_names_iff.mp hF
  refine (weakMeasureRep_names_iff cantorPresentation).mpr fun n => ?_
  exact levyProkhorov_approxList_le hM n

/-! ### The interface theorem -/

/-- **The unit 28 interface theorem**: the Cantor computable-measure representation is
computably equivalent to the generic weak measure representation instantiated at the
Cantor presentation. -/
theorem cantorMeasureRep_equiv_weak :
    cantorMeasureRep ≡c weakMeasureRep cantorPresentation :=
  ⟨computableMap_cantor_to_weak, computableMap_weak_to_cantor⟩

end ComputableAnalysis
