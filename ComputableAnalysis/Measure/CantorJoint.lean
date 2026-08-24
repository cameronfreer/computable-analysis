/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.CantorRepresentation
import ComputableAnalysis.Measure.WeakRepresentation
import ComputableAnalysis.Measure.CantorFacts
import Mathlib.Data.List.GetD

/-!
# Joint measures on Cantor × Cantor along the deinterleaving identification

The cylinder-mass route to computable joint measures on the presented product
`Cantor × Cantor` (unit 35): a measure on Cantor space *is* a joint law on the product,
through the pinned interleaving identification of units 20–23.

**The identification.** `cantorDeinterleave x = (even track of x, odd track of x)` is the
two-sided inverse of `Cantor.interleave` (`cantorDeinterleave_interleave`,
`interleave_cantorDeinterleave`), continuous and measurable coordinatewise.
`jointOfCantor μ` is the pushforward of `μ` along it, a probability measure on
`Cantor × Cantor`.

**Rectangle masses.** The preimage of the rectangle
`cylinder (wordEven w) ×ˢ cylinder (wordOdd w)` under `cantorDeinterleave` is exactly
`cylinder w`, for *every* word `w` (`cantorDeinterleave_preimage_prod`) — the constrained
even coordinates `0, 2, …` and odd coordinates `1, 3, …` of the deinterleaved tracks
together form the prefix constraint `w`. Hence `jointOfCantor_apply_prod`:
`(jointOfCantor μ) (cylinder (wordEven w) ×ˢ cylinder (wordOdd w)) = μ (cylinder w)`.
The subword form is primary because it is total in `w`; the equal-length rectangle form
`jointOfCantor_rectangle` (a rectangle of same-length word cylinders has the mass of the
interleaved word `wordInterleave s t`) is derived from it, and equal lengths are exactly
what both the realizer below and the conditioning construction consume — general
rectangles split into equal-length ones by `cylinder_eq_union_append`.

**The computability bridge** (`computableMap_jointOfCantor`). From a `cantorMeasureRep`
name of `μ` (unit 25 exact cylinder-mass component names) the realizer computes a weak
name of `jointOfCantor μ` on the presented product
`weakMeasureRep (cantorPresentation.prod cantorPresentation)` (units 17/27). Output
coordinate `n` is the encoded atom list of the level-`(n + 2)` product-cylinder
discretization, indexed by the `2 ^ (2n + 4)` interleaved words `w` of length `2n + 4`:
atom `Nat.pair (encode (wordEven w)) (encode (wordOdd w))` (the product dense pair
`(wordPoint (wordEven w), wordPoint (wordOdd w))`), weight read off the input name at
component `(w, 3n + 7)`. Estimate: level-`(n + 2)` product cylinders have diameter
`≤ (2⁻¹) ^ (n + 2)` in the max metric, so the discretization costs `(2⁻¹) ^ (n + 2)`,
and renormalizing the `2 ^ (2n + 4)` approximate weights costs
`2 · 2 ^ (2n + 4) · (2⁻¹) ^ (3n + 7) = (2⁻¹) ^ (n + 2)` more — total
`(2⁻¹) ^ (n + 1) ≤ (2⁻¹) ^ n`.

Implementation note: the discretization/renormalization toolkit of unit 28
(`ComputableAnalysis/Measure/WeakEquivalence.lean`) is private there and re-derived
privately here on the product space — sanctioned duplication, pending a later API pass;
the decoded-atomic branch evaluations cross the definitional equality with unit 27's
private clamped-weight helpers exactly as in unit 28.
-/

namespace ComputableAnalysis

open MeasureTheory Metric Encodable Denumerable OracleCode

open scoped PiNatInstances

/-! ### The deinterleaving identification -/

/-- Deinterleave a Cantor point into its even and odd tracks: the inverse of
`Cantor.interleave`. -/
def cantorDeinterleave (x : Cantor) : Cantor × Cantor :=
  (fun n => x (2 * n), fun n => x (2 * n + 1))

/-- Deinterleaving inverts interleaving. -/
@[simp]
theorem cantorDeinterleave_interleave (x y : Cantor) :
    cantorDeinterleave (Cantor.interleave x y) = (x, y) :=
  Prod.ext (funext fun n => Cantor.interleave_even x y n)
    (funext fun n => Cantor.interleave_odd x y n)

/-- Interleaving inverts deinterleaving. -/
@[simp]
theorem interleave_cantorDeinterleave (x : Cantor) :
    Cantor.interleave (cantorDeinterleave x).1 (cantorDeinterleave x).2 = x := by
  funext n
  unfold Cantor.interleave cantorDeinterleave
  split
  · next h => exact congrArg x (by omega)
  · next h => exact congrArg x (by omega)

/-- Deinterleaving is continuous: each output coordinate reads one input coordinate. -/
theorem continuous_cantorDeinterleave : Continuous cantorDeinterleave :=
  Continuous.prodMk (continuous_pi fun n => continuous_apply (2 * n))
    (continuous_pi fun n => continuous_apply (2 * n + 1))

/-- Deinterleaving is measurable: each output coordinate reads one input coordinate. -/
theorem measurable_cantorDeinterleave : Measurable cantorDeinterleave :=
  Measurable.prodMk (measurable_pi_lambda _ fun n => measurable_pi_apply (2 * n))
    (measurable_pi_lambda _ fun n => measurable_pi_apply (2 * n + 1))

/-- **The rectangle preimage**: the deinterleave preimage of the subword-cylinder
rectangle of `w` is the cylinder of `w`, for every word `w`. -/
theorem cantorDeinterleave_preimage_prod (w : List Bool) :
    cantorDeinterleave ⁻¹'
        ((cylinder (wordEven w) : Set Cantor) ×ˢ (cylinder (wordOdd w) : Set Cantor))
      = (cylinder w : Set Cantor) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_prod]
  constructor
  · rintro ⟨he, ho⟩
    have hmem := Cantor.interleave_mem_cylinder_iff.mpr ⟨he, ho⟩
    rwa [interleave_cantorDeinterleave] at hmem
  · intro hx
    have hmem : Cantor.interleave (cantorDeinterleave x).1 (cantorDeinterleave x).2
        ∈ (cylinder w : Set Cantor) := by
      rwa [interleave_cantorDeinterleave]
    exact Cantor.interleave_mem_cylinder_iff.mp hmem

/-! ### The joint measure -/

/-- The joint law of a Cantor measure along the interleaving identification: the
pushforward of `μ` under `cantorDeinterleave`, a probability measure on the product. -/
noncomputable def jointOfCantor (μ : ProbabilityMeasure Cantor) :
    ProbabilityMeasure (Cantor × Cantor) :=
  ⟨μ.toMeasure.map cantorDeinterleave,
    Measure.isProbabilityMeasure_map measurable_cantorDeinterleave.aemeasurable⟩

/-- The underlying measure of the joint law is the image measure. -/
theorem toMeasure_jointOfCantor (μ : ProbabilityMeasure Cantor) :
    (jointOfCantor μ).toMeasure = μ.toMeasure.map cantorDeinterleave := rfl

/-- **Subword rectangle masses of the joint law**: for every word `w`, the joint mass of
`cylinder (wordEven w) ×ˢ cylinder (wordOdd w)` is the `μ`-mass of `cylinder w`. -/
theorem jointOfCantor_apply_prod (μ : ProbabilityMeasure Cantor) (w : List Bool) :
    (jointOfCantor μ).toMeasure
        ((cylinder (wordEven w) : Set Cantor) ×ˢ (cylinder (wordOdd w) : Set Cantor))
      = μ.toMeasure (cylinder w) := by
  rw [toMeasure_jointOfCantor,
    Measure.map_apply measurable_cantorDeinterleave
      ((measurableSet_cylinder (wordEven w)).prod (measurableSet_cylinder (wordOdd w))),
    cantorDeinterleave_preimage_prod]

/-! ### The equal-length rectangle form -/

/-- Interleave two binary words positionwise: even positions read `s`, odd positions
read `t` — the word-level form of `Cantor.interleave`, consumed at equal lengths. -/
def wordInterleave (s t : List Bool) : List Bool :=
  List.ofFn fun i : Fin (s.length + t.length) =>
    if (i : ℕ) % 2 = 0 then s.getD ((i : ℕ) / 2) false else t.getD ((i : ℕ) / 2) false

/-- Length of an interleaved word. -/
@[simp]
theorem length_wordInterleave (s t : List Bool) :
    (wordInterleave s t).length = s.length + t.length := by
  simp [wordInterleave]

/-- At equal lengths, the even subword of an interleaved word is the first word. -/
theorem wordEven_wordInterleave {s t : List Bool} (h : s.length = t.length) :
    wordEven (wordInterleave s t) = s := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [length_wordEven, length_wordInterleave]
    omega
  · rw [getElem_wordEven h1]
    simp only [wordInterleave, List.getElem_ofFn]
    rw [ite_eq_left (show 2 * i % 2 = 0 by omega), show 2 * i / 2 = i from by omega]
    exact List.getD_eq_getElem _ _ h2

/-- At equal lengths, the odd subword of an interleaved word is the second word. -/
theorem wordOdd_wordInterleave {s t : List Bool} (h : s.length = t.length) :
    wordOdd (wordInterleave s t) = t := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · rw [length_wordOdd, length_wordInterleave]
    omega
  · rw [getElem_wordOdd h1]
    simp only [wordInterleave, List.getElem_ofFn]
    rw [ite_eq_right (show ¬(2 * i + 1) % 2 = 0 by omega),
      show (2 * i + 1) / 2 = i from by omega]
    exact List.getD_eq_getElem _ _ h2

/-- **The equal-length rectangle theorem**: a rectangle of same-length word cylinders
has, under the joint law, the `μ`-mass of the interleaved word. General rectangles
reduce to this form by splitting the shorter side with `cylinder_eq_union_append`. -/
theorem jointOfCantor_rectangle (μ : ProbabilityMeasure Cantor) {s t : List Bool}
    (h : s.length = t.length) :
    (jointOfCantor μ).toMeasure ((cylinder s : Set Cantor) ×ˢ (cylinder t : Set Cantor))
      = μ.toMeasure (cylinder (wordInterleave s t)) := by
  have happ := jointOfCantor_apply_prod μ (wordInterleave s t)
  rwa [wordEven_wordInterleave h, wordOdd_wordInterleave h] at happ

/-! ### Clamped weights: definitionally equal copies of unit 27's private helpers -/

/-- The clamped rational weight of a weight code (definitionally equal to the private
helper inside `atomicOfList`). -/
private def wRaw (c : ℕ) : ℚ := max 0 (min 1 (ratOfCode c))

private theorem wRaw_nonneg (c : ℕ) : 0 ≤ wRaw c := le_max_left _ _

/-- The (rational) total clamped weight of a decoded atom list (definitionally equal to
the private helper inside `atomicOfList`). -/
private def wSumL (l : List (ℕ × ℕ)) : ℚ := (l.map fun pr => wRaw pr.2).sum

/-- A mapped list sum as a `Fin` sum over positions. -/
private theorem listSum_map_eq_finSum {β M : Type*} [AddCommMonoid M] (l : List β)
    (g : β → M) : (l.map g).sum = ∑ i : Fin l.length, g l[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

/-! ### Evaluation of the decoded atomics on the product presentation

The two branch evaluations of unit 27's `atomicOfList`, at the presented product; the
proofs cross the definitional equality with the private clamped-weight helpers. -/

/-- Nonzero total weight: the decoded atomic is the renormalized weighted Dirac sum. -/
private theorem toMeasure_prodAtomicOfList_of_ne {l : List (ℕ × ℕ)} (h0 : wSumL l ≠ 0) :
    (atomicOfList (cantorPresentation.prod cantorPresentation) l).toMeasure
      = ∑ i : Fin l.length,
          ENNReal.ofReal ((wRaw l[i].2 / wSumL l : ℚ) : ℝ)
            • Measure.dirac
                ((cantorPresentation.prod cantorPresentation).dense l[i].1) := by
  exact congrArg ProbabilityMeasure.toMeasure (dite_eq_right h0)

/-- Decoding an encoded atom list. -/
private theorem prodAtomic_encode (l : List (ℕ × ℕ)) :
    atomic (cantorPresentation.prod cantorPresentation) (Encodable.encode l)
      = atomicOfList (cantorPresentation.prod cantorPresentation) l := by
  rw [atomic, Denumerable.ofNat_encode]

/-- Evaluating a decoded atomic on a mapped index list. -/
private theorem toMeasure_prodAtomicOfList_map {β : Type*} (t : List β) (g : β → ℕ × ℕ)
    (h0 : wSumL (t.map g) ≠ 0) :
    (atomicOfList (cantorPresentation.prod cantorPresentation) (t.map g)).toMeasure
      = ∑ i : Fin t.length,
          ENNReal.ofReal ((wRaw (g t[i]).2 / wSumL (t.map g) : ℚ) : ℝ)
            • Measure.dirac
                ((cantorPresentation.prod cantorPresentation).dense (g t[i]).1) := by
  rw [toMeasure_prodAtomicOfList_of_ne h0]
  have hlen : (t.map g).length = t.length := by simp
  rw [← Fin.sum_congr' _ hlen]
  refine Finset.sum_congr rfl fun i' _ => ?_
  simp [List.getElem_map]

/-! ### Finite atomic measures on the product -/

/-- A finite weighted sum of Diracs with nonnegative weights summing to `1` is a
probability measure. -/
private theorem isProbabilityMeasure_sum_smul_dirac {k : ℕ} {a : Fin k → ℝ}
    (x : Fin k → Cantor × Cantor) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) := by
  constructor
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => ha i, hsum, ENNReal.ofReal_one]

/-! ### Word machinery -/

private theorem half_pow_le_half_pow {k n : ℕ} (h : k ≤ n) :
    ((2 : ℝ)⁻¹) ^ n ≤ ((2 : ℝ)⁻¹) ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 : ((2 : ℝ)⁻¹) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ k := by positivity
  nlinarith

private theorem one_half_pow_le_one_half_pow {k n : ℕ} (h : k ≤ n) :
    ((1 : ℝ) / 2) ^ n ≤ ((1 : ℝ) / 2) ^ k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]
  have h1 : ((1 : ℝ) / 2) ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) < ((1 : ℝ) / 2) ^ k := by positivity
  nlinarith

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

/-! ### The product-cylinder discretization and its LP bound -/

/-- Every word cylinder has diameter `≤ (1/2)^|s|`. -/
private theorem dist_le_of_mem_cylinder {s : List Bool} {y z : Cantor}
    (hy : y ∈ (cylinder s : Set Cantor)) (hz : z ∈ (cylinder s : Set Cantor)) :
    dist y z ≤ (1 / 2 : ℝ) ^ s.length := by
  have h := cylinder_eq_of_mem hz
  rw [h] at hy
  exact PiNat.mem_cylinder_iff_dist_le.mp hy

/-- The level-`L` joint discretization: mass `cylMass μ w` at the deinterleaved
representative pair `(wordPoint (wordEven w), wordPoint (wordOdd w))`, over all
length-`L` words `w` — the product-cylinder discretization of `jointOfCantor μ`. -/
private noncomputable def jointDiscretize (μ : ProbabilityMeasure Cantor) (L : ℕ) :
    ProbabilityMeasure (Cantor × Cantor) :=
  ⟨∑ i : Fin (wordsOf L).length,
      ENNReal.ofReal (cylMass μ (wordsOf L)[i])
        • Measure.dirac
            (wordPoint (wordEven (wordsOf L)[i]), wordPoint (wordOdd (wordsOf L)[i])),
    isProbabilityMeasure_sum_smul_dirac _ (fun i => cylMass_nonneg μ _)
      (by
        rw [← listSum_map_eq_finSum (wordsOf L) (cylMass μ)]
        exact sum_map_wordsOf μ L)⟩

private theorem toMeasure_jointDiscretize (μ : ProbabilityMeasure Cantor) (L : ℕ) :
    (jointDiscretize μ L).toMeasure
      = ∑ i : Fin (wordsOf L).length,
          ENNReal.ofReal (cylMass μ (wordsOf L)[i])
            • Measure.dirac
                (wordPoint (wordEven (wordsOf L)[i]),
                  wordPoint (wordOdd (wordsOf L)[i])) := rfl

/-- **The joint discretization estimate**: the level-`L` product-cylinder discretization
is within `(1/2) ^ (L / 2)` of the joint law — the subword rectangles of the length-`L`
words cover the product, and each has diameter `≤ (1/2) ^ (L / 2)` in the max metric. -/
private theorem levyProkhorovDist_jointDiscretize_le (μ : ProbabilityMeasure Cantor)
    (L : ℕ) :
    levyProkhorovDist (jointOfCantor μ).toMeasure (jointDiscretize μ L).toMeasure
      ≤ (1 / 2 : ℝ) ^ (L / 2) := by
  refine levyProkhorovDist_le_of_forall_le _ _ (by positivity) fun ε B hε hB => ?_
  have key : (jointOfCantor μ).toMeasure B
      ≤ (jointDiscretize μ L).toMeasure (thickening ε B) := by
    have hcover : B ⊆ ⋃ i : Fin (wordsOf L).length,
        B ∩ ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
          ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor)) := by
      intro z hz
      obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp
        (streamTake_mem_wordsOf (Cantor.interleave z.1 z.2) L)
      refine Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hz, ?_⟩
      refine Set.mem_prod.mpr ?_
      have hmem : Cantor.interleave z.1 z.2 ∈ (cylinder ((wordsOf L)[i]'hi) : Set Cantor) := by
        rw [hix]
        exact mem_cylinder_streamTake _ _
      exact Cantor.interleave_mem_cylinder_iff.mp hmem
    calc (jointOfCantor μ).toMeasure B
        ≤ (jointOfCantor μ).toMeasure (⋃ i : Fin (wordsOf L).length,
            B ∩ ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
              ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor))) :=
          measure_mono hcover
      _ ≤ ∑' i : Fin (wordsOf L).length, (jointOfCantor μ).toMeasure
            (B ∩ ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
              ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor))) :=
          measure_iUnion_le _
      _ = ∑ i : Fin (wordsOf L).length, (jointOfCantor μ).toMeasure
            (B ∩ ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
              ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor))) :=
          tsum_fintype _
      _ ≤ ∑ i : Fin (wordsOf L).length,
            (ENNReal.ofReal (cylMass μ (wordsOf L)[i])
              • Measure.dirac
                  (wordPoint (wordEven (wordsOf L)[i]),
                    wordPoint (wordOdd (wordsOf L)[i]))) (thickening ε B) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rcases Set.eq_empty_or_nonempty
            (B ∩ ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
              ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor))) with hemp | hne
          · rw [hemp]
            simp
          · obtain ⟨b, hbB, hbc⟩ := hne
            obtain ⟨hb1, hb2⟩ := Set.mem_prod.mp hbc
            have hlen : ((wordsOf L)[i] : List Bool).length = L :=
              length_of_mem_wordsOf (List.getElem_mem _)
            have hpt : (wordPoint (wordEven (wordsOf L)[i]),
                wordPoint (wordOdd (wordsOf L)[i])) ∈ thickening ε B := by
              refine Metric.mem_thickening_iff.mpr ⟨b, hbB, lt_of_le_of_lt ?_ hε⟩
              have hde : dist (wordPoint (wordEven (wordsOf L)[i])) b.1
                  ≤ (1 / 2 : ℝ) ^ (wordEven ((wordsOf L)[i] : List Bool)).length :=
                dist_le_of_mem_cylinder
                  (streamExtend_mem_cylinder (wordEven (wordsOf L)[i]) fun _ => false) hb1
              have hdo : dist (wordPoint (wordOdd (wordsOf L)[i])) b.2
                  ≤ (1 / 2 : ℝ) ^ (wordOdd ((wordsOf L)[i] : List Bool)).length :=
                dist_le_of_mem_cylinder
                  (streamExtend_mem_cylinder (wordOdd (wordsOf L)[i]) fun _ => false) hb2
              rw [length_wordEven, hlen] at hde
              rw [length_wordOdd, hlen] at hdo
              rw [Prod.dist_eq]
              exact max_le
                (hde.trans (one_half_pow_le_one_half_pow (by omega)))
                (hdo.trans (one_half_pow_le_one_half_pow le_rfl))
            rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem hpt, mul_one]
            calc (jointOfCantor μ).toMeasure
                  (B ∩ ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
                    ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor)))
                ≤ (jointOfCantor μ).toMeasure
                    ((cylinder (wordEven (wordsOf L)[i]) : Set Cantor)
                      ×ˢ (cylinder (wordOdd (wordsOf L)[i]) : Set Cantor)) :=
                  measure_mono Set.inter_subset_right
              _ = ENNReal.ofReal (cylMass μ (wordsOf L)[i]) := by
                  rw [jointOfCantor_apply_prod, cylMass,
                    ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ = (jointDiscretize μ L).toMeasure (thickening ε B) := by
          rw [toMeasure_jointDiscretize, Measure.finsetSum_apply]
  exact key.trans le_self_add

/-! ### From measure names to joint weak names -/

private theorem realPresentation_dense_eq (j : ℕ) :
    realPresentation.dense j = ((ratOfCode j : ℚ) : ℝ) := rfl

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

/-- The stage-`n` joint approximation list: all interleaved words of length `2n + 4`
(the level-`(n + 2)` product discretization), atoms the paired subword indices, weights
read off the input name at precision `3n + 7`. -/
private def jointApproxList (F : Baire) (n : ℕ) : List (ℕ × ℕ) :=
  (wordsOf (2 * n + 4)).map fun w =>
    (Nat.pair (Encodable.encode (wordEven w)) (Encodable.encode (wordOdd w)),
      F (Nat.pair (Encodable.encode w) (3 * n + 7)))

private theorem two_pow_bound (n : ℕ) :
    ((2 : ℝ) ^ (2 * n + 4)) * ((2 : ℝ)⁻¹) ^ (3 * n + 7) = ((2 : ℝ)⁻¹) ^ (n + 3) := by
  have h : 3 * n + 7 = (2 * n + 4) + (n + 3) := by ring
  rw [h, pow_add ((2 : ℝ)⁻¹) (2 * n + 4) (n + 3), ← mul_assoc, ← mul_pow]
  norm_num

/-- The product dense point of a paired subword index. -/
private theorem prodDense_pair (w : List Bool) :
    (cantorPresentation.prod cantorPresentation).dense
        (Nat.pair (Encodable.encode (wordEven w)) (Encodable.encode (wordOdd w)))
      = (wordPoint (wordEven w), wordPoint (wordOdd w)) := by
  change (densePoint (Nat.pair (Encodable.encode (wordEven w))
        (Encodable.encode (wordOdd w))).unpair.1,
      densePoint (Nat.pair (Encodable.encode (wordEven w))
        (Encodable.encode (wordOdd w))).unpair.2)
    = (wordPoint (wordEven w), wordPoint (wordOdd w))
  rw [Nat.unpair_pair]
  simp only [densePoint, denseWord_encode]

/-- **The joint direction-A estimate**: the stage-`n` approximation list names a measure
at LP distance `≤ (2⁻¹)^n` from the joint law — discretization cost `(2⁻¹)^(n+2)` plus
renormalized weight cost `2 · 2^(2n+4) · (2⁻¹)^(3n+7) = (2⁻¹)^(n+2)`. -/
private theorem levyProkhorov_jointApproxList_le {F : Baire}
    {μ : ProbabilityMeasure Cantor} (hF : MeasureNames F μ) (n : ℕ) :
    levyProkhorovDist (jointOfCantor μ).toMeasure
        (atomic (cantorPresentation.prod cantorPresentation)
          (Encodable.encode (jointApproxList F n))).toMeasure
      ≤ ((2 : ℝ)⁻¹) ^ n := by
  classical
  have hqd : ∀ i : Fin (wordsOf (2 * n + 4)).length,
      |((wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i]) (3 * n + 7)))
          : ℚ) : ℝ)
          - cylMass μ (wordsOf (2 * n + 4))[i]|
        ≤ ((2 : ℝ)⁻¹) ^ (3 * n + 7) := by
    intro i
    have hest := measureNames_est hF (wordsOf (2 * n + 4))[i] (3 * n + 7)
    have hcast : ((wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i])
          (3 * n + 7))) : ℚ) : ℝ)
        = max 0 (min 1
            ((ratOfCode (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i])
              (3 * n + 7))) : ℚ) : ℝ)) := by
      rw [wRaw]
      push_cast
      rfl
    have hclamp_a : max 0 (min 1 (cylMass μ (wordsOf (2 * n + 4))[i]))
        = cylMass μ (wordsOf (2 * n + 4))[i] := by
      rw [min_eq_right (cylMass_le_one μ _), max_eq_right (cylMass_nonneg μ _)]
    calc |((wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i]) (3 * n + 7)))
          : ℚ) : ℝ)
          - cylMass μ (wordsOf (2 * n + 4))[i]|
        = |max 0 (min 1
              ((ratOfCode (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i])
                (3 * n + 7))) : ℚ) : ℝ))
            - max 0 (min 1 (cylMass μ (wordsOf (2 * n + 4))[i]))| := by
          rw [hcast, hclamp_a]
      _ ≤ |((ratOfCode (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i])
              (3 * n + 7))) : ℚ) : ℝ)
            - cylMass μ (wordsOf (2 * n + 4))[i]| := abs_clamp_sub_clamp_le _ _
      _ ≤ ((2 : ℝ)⁻¹) ^ (3 * n + 7) := hest
  have hKcast : (((wordsOf (2 * n + 4)).length : ℕ) : ℝ) = (2 : ℝ) ^ (2 * n + 4) := by
    rw [length_wordsOf]
    push_cast
    ring
  have hKη : (((wordsOf (2 * n + 4)).length : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (3 * n + 7)
      ≤ 1 / 4 := by
    rw [hKcast, two_pow_bound n]
    calc ((2 : ℝ)⁻¹) ^ (n + 3) ≤ ((2 : ℝ)⁻¹) ^ 2 :=
          half_pow_le_half_pow (by omega)
      _ = 1 / 4 := by norm_num
  obtain ⟨hSne, hsum_le⟩ :=
    sum_abs_sub_normalized_le
      (a := fun i : Fin (wordsOf (2 * n + 4)).length => cylMass μ (wordsOf (2 * n + 4))[i])
      (q := fun i : Fin (wordsOf (2 * n + 4)).length =>
        wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i]) (3 * n + 7))))
      (by
        rw [← listSum_map_eq_finSum (wordsOf (2 * n + 4)) (cylMass μ)]
        exact sum_map_wordsOf μ (2 * n + 4))
      (fun i => wRaw_nonneg _) hqd hKη
  have hwS : wSumL (jointApproxList F n)
      = ∑ i : Fin (wordsOf (2 * n + 4)).length,
          wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i]) (3 * n + 7))) := by
    simp only [jointApproxList, wSumL, List.map_map]
    rw [listSum_map_eq_finSum]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hS0 : wSumL (jointApproxList F n) ≠ 0 := by
    rw [hwS]
    exact hSne
  have hQ : (atomic (cantorPresentation.prod cantorPresentation)
        (Encodable.encode (jointApproxList F n))).toMeasure
      = ∑ i : Fin (wordsOf (2 * n + 4)).length,
          ENNReal.ofReal
            ((wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i]) (3 * n + 7)))
                / ∑ jj : Fin (wordsOf (2 * n + 4)).length,
                    wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[jj])
                      (3 * n + 7)))
              : ℚ) : ℝ)
            • Measure.dirac
                (wordPoint (wordEven (wordsOf (2 * n + 4))[i]),
                  wordPoint (wordOdd (wordsOf (2 * n + 4))[i])) := by
    rw [prodAtomic_encode]
    have hal : jointApproxList F n = (wordsOf (2 * n + 4)).map fun w =>
        (Nat.pair (Encodable.encode (wordEven w)) (Encodable.encode (wordOdd w)),
          F (Nat.pair (Encodable.encode w) (3 * n + 7))) := rfl
    rw [hal] at hS0 ⊢
    rw [toMeasure_prodAtomicOfList_map _ _ hS0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [prodDense_pair, ← hal, hwS]
  have hd1 : levyProkhorovDist (jointOfCantor μ).toMeasure
      (jointDiscretize μ (2 * n + 4)).toMeasure ≤ (1 / 2 : ℝ) ^ (n + 2) := by
    have h := levyProkhorovDist_jointDiscretize_le μ (2 * n + 4)
    rwa [show (2 * n + 4) / 2 = n + 2 from by omega] at h
  have hd2 : levyProkhorovDist (jointDiscretize μ (2 * n + 4)).toMeasure
        (atomic (cantorPresentation.prod cantorPresentation)
          (Encodable.encode (jointApproxList F n))).toMeasure
      ≤ ∑ i : Fin (wordsOf (2 * n + 4)).length,
          |cylMass μ (wordsOf (2 * n + 4))[i]
            - ((wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[i]) (3 * n + 7)))
                / ∑ jj : Fin (wordsOf (2 * n + 4)).length,
                    wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[jj])
                      (3 * n + 7)))
              : ℚ) : ℝ)| := by
    refine levyProkhorovDist_le_sum_abs
      (fun i : Fin (wordsOf (2 * n + 4)).length =>
        (wordPoint (wordEven (wordsOf (2 * n + 4))[i]),
          wordPoint (wordOdd (wordsOf (2 * n + 4))[i])))
      _ _ ?_ _ _ (toMeasure_jointDiscretize μ (2 * n + 4)) hQ
    intro i
    have hSpos : (0 : ℚ) < ∑ jj : Fin (wordsOf (2 * n + 4)).length,
        wRaw (F (Nat.pair (Encodable.encode (wordsOf (2 * n + 4))[jj]) (3 * n + 7))) :=
      lt_of_le_of_ne (Finset.sum_nonneg fun jj _ => wRaw_nonneg _) (Ne.symm hSne)
    exact_mod_cast div_nonneg (wRaw_nonneg _) hSpos.le
  have e1 : ((2 : ℝ)⁻¹) ^ (n + 3) = ((2 : ℝ)⁻¹) ^ (n + 2) * 2⁻¹ := pow_succ _ _
  have e2 : ((2 : ℝ)⁻¹) ^ (n + 2) = ((2 : ℝ)⁻¹) ^ (n + 1) * 2⁻¹ := pow_succ _ _
  have e3 : ((2 : ℝ)⁻¹) ^ (n + 1) = ((2 : ℝ)⁻¹) ^ n * 2⁻¹ := pow_succ _ _
  have hp : (0 : ℝ) ≤ ((2 : ℝ)⁻¹) ^ n := by positivity
  have hhalf : ((1 : ℝ) / 2) ^ (n + 2) = ((2 : ℝ)⁻¹) ^ (n + 2) := by norm_num
  have hKη_eq : (((wordsOf (2 * n + 4)).length : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (3 * n + 7)
      = ((2 : ℝ)⁻¹) ^ (n + 3) := by
    rw [hKcast, two_pow_bound n]
  calc levyProkhorovDist (jointOfCantor μ).toMeasure
        (atomic (cantorPresentation.prod cantorPresentation)
          (Encodable.encode (jointApproxList F n))).toMeasure
      ≤ levyProkhorovDist (jointOfCantor μ).toMeasure
          (jointDiscretize μ (2 * n + 4)).toMeasure
        + levyProkhorovDist (jointDiscretize μ (2 * n + 4)).toMeasure
            (atomic (cantorPresentation.prod cantorPresentation)
              (Encodable.encode (jointApproxList F n))).toMeasure :=
        levyProkhorovDist_triangle _ _ _
    _ ≤ (1 / 2 : ℝ) ^ (n + 2)
        + 2 * ((((wordsOf (2 * n + 4)).length : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ (3 * n + 7)) :=
        add_le_add hd1 (hd2.trans hsum_le)
    _ ≤ ((2 : ℝ)⁻¹) ^ n := by
        rw [hhalf, hKη_eq]
        linarith

/-! ### The realizer -/

/-- The prefix-length bound of the realizer. -/
private def jointMaxIdx (n : ℕ) : ℕ :=
  ((wordsOf (2 * n + 4)).map fun s => Nat.pair (Encodable.encode s) (3 * n + 7)).foldr max 0

private theorem le_foldr_max : ∀ {l : List ℕ} {x : ℕ}, x ∈ l → x ≤ l.foldr max 0
  | a :: l, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact le_max_left _ _
    · exact le_trans (le_foldr_max hx') (le_max_right _ _)

private theorem lt_jointMaxIdx_succ {n : ℕ} {s : List Bool} (hs : s ∈ wordsOf (2 * n + 4)) :
    Nat.pair (Encodable.encode s) (3 * n + 7) < jointMaxIdx n + 1 :=
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

private theorem primrec_jointMaxIdx : Primrec jointMaxIdx := by
  have hmap : Primrec fun n : ℕ =>
      (wordsOf (2 * n + 4)).map fun s => Nat.pair (Encodable.encode s) (3 * n + 7) :=
    Primrec.list_map
      (primrec_wordsOf.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 4)))
      ((Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
        (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 3) Primrec.fst)
          (Primrec.const 7))).to₂)
  exact (Primrec.list_foldr hmap (Primrec.const 0)
    ((Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun n => rfl

/-- List-level even subword (a `Primrec`-friendly form of `wordEven`). -/
private def wordEvenL (s : List Bool) : List Bool :=
  (List.range ((s.length + 1) / 2)).map fun i => s.getD (2 * i) false

/-- List-level odd subword (a `Primrec`-friendly form of `wordOdd`). -/
private def wordOddL (s : List Bool) : List Bool :=
  (List.range (s.length / 2)).map fun i => s.getD (2 * i + 1) false

private theorem wordEvenL_eq (s : List Bool) : wordEvenL s = wordEven s := by
  refine List.ext_getElem (by simp [wordEvenL]) fun i h1 h2 => ?_
  have hi : 2 * i < s.length := by
    have h2' := h2
    simp at h2'
    omega
  simp only [wordEvenL, List.getElem_map, List.getElem_range]
  rw [getElem_wordEven h2, List.getD_eq_getElem _ _ hi]

private theorem wordOddL_eq (s : List Bool) : wordOddL s = wordOdd s := by
  refine List.ext_getElem (by simp [wordOddL]) fun i h1 h2 => ?_
  have hi : 2 * i + 1 < s.length := by
    have h2' := h2
    simp at h2'
    omega
  simp only [wordOddL, List.getElem_map, List.getElem_range]
  rw [getElem_wordOdd h2, List.getD_eq_getElem _ _ hi]

private theorem primrec_wordEvenL : Primrec wordEvenL := by
  unfold wordEvenL
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp
      (Primrec.succ.comp Primrec.list_length) (Primrec.const 2)))
    ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to₂

private theorem primrec_wordOddL : Primrec wordOddL := by
  unfold wordOddL
  exact Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)))
    ((Primrec.list_getD false).comp Primrec.fst
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))).to₂

/-- **The computability bridge**: from a `cantorMeasureRep` name of `μ` the realizer
computes a weak name of `jointOfCantor μ` on the presented product — output coordinate
`n` is the encoded level-`(2n + 4)` interleaved discretization list, with atom pairs
`Nat.pair (encode (wordEven w)) (encode (wordOdd w))` and weights read at packed
precision `3n + 7`. -/
theorem computableMap_jointOfCantor :
    ComputableMap cantorMeasureRep
      (weakMeasureRep (cantorPresentation.prod cantorPresentation)) jointOfCantor := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode
    (b := fun n _ => jointMaxIdx n + 1)
    (g := fun v => Encodable.encode
      ((wordsOf (2 * v.unpair.1 + 4)).map fun w =>
        (Nat.pair (Encodable.encode (wordEvenL w)) (Encodable.encode (wordOddL w)),
          (ofNat (List ℕ) v.unpair.2).getD
            (Nat.pair (Encodable.encode w) (3 * v.unpair.1 + 7)) 0)))
    (Primrec.succ.comp (primrec_jointMaxIdx.comp Primrec.fst))
    (by
      have hwords : Primrec fun v : ℕ => wordsOf (2 * v.unpair.1 + 4) :=
        primrec_wordsOf.comp (Primrec.nat_add.comp
          (Primrec.nat_mul.comp (Primrec.const 2) primrec_unpairFst) (Primrec.const 4))
      have hinner : Primrec₂ fun (v : ℕ) (w : List Bool) =>
          (Nat.pair (Encodable.encode (wordEvenL w)) (Encodable.encode (wordOddL w)),
            (ofNat (List ℕ) v.unpair.2).getD
              (Nat.pair (Encodable.encode w) (3 * v.unpair.1 + 7)) 0) :=
        (Primrec.pair
          (Primrec₂.natPair.comp
            (Primrec.encode.comp (primrec_wordEvenL.comp Primrec.snd))
            (Primrec.encode.comp (primrec_wordOddL.comp Primrec.snd)))
          ((Primrec.list_getD 0).comp
            ((Primrec.ofNat (List ℕ)).comp (primrec_unpairSnd.comp Primrec.fst))
            (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.snd)
              (Primrec.nat_add.comp
                (Primrec.nat_mul.comp (Primrec.const 3)
                  (primrec_unpairFst.comp Primrec.fst))
                (Primrec.const 7))))).to₂
      exact Primrec.encode.comp (Primrec.list_map hwords hinner))
  have hcomp : c.Computes fun F n => Encodable.encode (jointApproxList F n) := by
    intro F n
    rw [hc F n]
    simp only [Nat.unpair_pair, ofNat_encode]
    rw [jointApproxList]
    refine congrArg Part.some (congrArg (Encodable.encode (α := List (ℕ × ℕ)))
      (List.map_congr_left fun s hs => ?_))
    rw [wordEvenL_eq, wordOddL_eq, streamTake_getD F (lt_jointMaxIdx_succ hs)]
  refine ⟨c, .of_computes hcomp fun F μ hF => ?_⟩
  have hM : MeasureNames F μ := cantorMeasureRep_names_iff.mp hF
  refine (weakMeasureRep_names_iff (cantorPresentation.prod cantorPresentation)).mpr
    fun n => ?_
  exact levyProkhorov_jointApproxList_le hM n

end ComputableAnalysis
