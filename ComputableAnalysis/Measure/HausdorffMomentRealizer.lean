/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.FiniteAtomicPerturbation
import ComputableAnalysis.Measure.MomentWeights
import ComputableAnalysis.Measure.UnitInterval

/-!
# From a moment name to a weak name

This is the effective layer over the two classical estimates already in place. Given a
moment name of `η` — a packed family of `[0, 1]`-names of all the moments — it emits, at
each output precision `n`, an index into the rational-atomic dense sequence `atomic` of
`ComputableAnalysis.Measure.WeakRepresentation` whose measure is within `2⁻ⁿ` of `η` in
Lévy–Prokhorov distance. The schedule is entirely dyadic:

* `momentLevel n = 2 ^ (3 (n + 1))` is the Bernstein degree `N`, the level at which
  `levyProkhorovDist_binomialApproximant_le` gives `2⁻⁽ⁿ⁺¹⁾`;
* `momentDepth n = 2 N + n + 2` is the depth at which the moment names are read, chosen so
  that the moment error `δ = 2⁻ᵈ` satisfies `2 · 3 ^ N · δ ≤ 2⁻⁽ⁿ⁺¹⁾` — the `ℓ¹` budget of
  `ComputableAnalysis.Measure.MomentWeights`, using the crude dyadic bound
  `3 ^ N ≤ 2 ^ (2 N)`;
* `momentBound n` is the length of the oracle prefix that covers every coordinate read.

Two facts make the assembly work.

* **The grid points are dense points.** `unitIntervalPresentation.dense m` is the clamp of
  `ratOfCode m`, and `ratOfCode (fracCode k N) = k / N` for `N ≠ 0`, so
  `dense_fracCode : unitIntervalPresentation.dense (fracCode k N) = bernstein.z k`. The two
  measures compared by `levyProkhorovDist_le_sum_abs` therefore genuinely sit on the same
  atoms, and no search over the dense sequence is ever needed.
* **The decoder's repair is the classical repair.** `atomicOfList` clamps its weight codes
  into `[0, 1]` and renormalises by their total; that is exactly `clipWeight` followed by
  `normWeight`. So the realizer emits *raw* approximate weight codes and
  `totalClipWeight_pos` is what rules out the decoder's degenerate zero-total branch.

Everything the realizer computes is exact rational arithmetic on codes
(`ComputableAnalysis.Metric.RatCodeArith`), so the whole postprocessor `momentPost` is
primitive recursive and `OracleCode.exists_prefixPostCode` turns it into a single oracle
code.
-/

namespace ComputableAnalysis

open MeasureTheory

/-! ### Primitive recursion for the arithmetic used by the realizer

These three facts are about `Nat` alone and have nothing to do with computable analysis;
their proper home is mathlib. They are kept **private** here so that the upstreaming
contribution can happen on its own schedule without this module having to wait for it, and
so that no downstream file starts depending on this location for them. -/

/-- Natural-number exponentiation is primitive recursive. -/
private theorem primrec₂_natPow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-- The factorial is primitive recursive. -/
private theorem primrec_factorial : Primrec Nat.factorial := by
  have hstep : Primrec₂ fun n ih : ℕ ↦ (n + 1) * ih :=
    Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd
  refine (Primrec.nat_rec₁ (α := ℕ) 1 hstep).of_eq fun n ↦ ?_
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.factorial_succ, ← ih]

/-- Binomial coefficients are primitive recursive, through the factorial formula. -/
private theorem primrec₂_choose : Primrec₂ Nat.choose := by
  have hfac : Primrec₂ fun n k : ℕ ↦
      if k ≤ n then n.factorial / (k.factorial * (n - k).factorial) else 0 :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (Primrec.nat_div.comp (primrec_factorial.comp Primrec.fst)
        (Primrec.nat_mul.comp (primrec_factorial.comp Primrec.snd)
          (primrec_factorial.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))))
      (Primrec.const 0)
  refine hfac.of_eq fun n k ↦ ?_
  by_cases h : k ≤ n
  · rw [if_pos h, Nat.choose_eq_factorial_div_factorial h]
  · rw [if_neg h, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_le h)]

/-! ### The coded grid points -/

/-- **The grid points are dense points.** For `N ≠ 0` and `k ≤ N` the dense point of
`unitIntervalPresentation` at index `fracCode k N` is exactly the Bernstein grid point
`bernstein.z k = k / N`; the presentation's clamp is inert because `k / N ∈ [0, 1]`. No
search is involved — the grid points of the binomial approximant are literally dense points
of the presentation. -/
theorem dense_fracCode {N : ℕ} (hN : N ≠ 0) (k : Fin (N + 1)) :
    unitIntervalPresentation.dense (fracCode (k : ℕ) N) = bernstein.z k := by
  have hNR : (0 : ℝ) < (N : ℝ) := by positivity
  have hkN : ((k : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
  have hval : ((((k : ℕ) : ℚ) / (N : ℚ) : ℚ) : ℝ) = ((k : ℕ) : ℝ) / (N : ℝ) := by
    push_cast
    ring
  refine Subtype.ext ?_
  change max 0 (min 1 (((ratOfCode (fracCode (k : ℕ) N)) : ℚ) : ℝ)) = ((k : ℕ) : ℝ) / (N : ℝ)
  rw [ratOfCode_fracCode hN, hval, min_eq_right ((div_le_one hNR).mpr hkN),
    max_eq_right (by positivity)]

/-! ### The precision schedule -/

/-- The Bernstein degree used at output precision `n`: the dyadic level `2 ^ (3 (n + 1))`
of `levyProkhorovDist_binomialApproximant_le`, one step finer than the output. -/
def momentLevel (n : ℕ) : ℕ := 2 ^ (3 * (n + 1))

/-- The depth at which the moment names are read at output precision `n`. It is chosen so
that the moment error `δ = 2⁻ᵈ` satisfies `2 · 3 ^ N · δ ≤ 2⁻⁽ⁿ⁺¹⁾`, using `3 ^ N ≤ 2 ^ 2N`. -/
def momentDepth (n : ℕ) : ℕ := 2 * momentLevel n + n + 2

/-- The length of the oracle prefix read at output precision `n`: enough to cover every
coordinate `Nat.pair i (momentDepth n)` with `i ≤ momentLevel n`. -/
def momentBound (n : ℕ) : ℕ := (momentLevel n + momentDepth n + 1) ^ 2

/-- The Cantor pairing is bounded by the square of the successor of the sum. -/
private theorem pair_lt_sq (a b : ℕ) : Nat.pair a b < (a + b + 1) ^ 2 := by
  rw [Nat.pair]
  split_ifs with h <;> nlinarith

/-- Every coordinate read at output precision `n` lies inside the prefix. -/
theorem pair_momentDepth_lt_momentBound {n i : ℕ} (hi : i ≤ momentLevel n) :
    Nat.pair i (momentDepth n) < momentBound n :=
  lt_of_lt_of_le (pair_lt_sq i (momentDepth n))
    (Nat.pow_le_pow_left (by omega) 2)

/-- `momentLevel n` is nonzero. -/
theorem momentLevel_ne_zero (n : ℕ) : momentLevel n ≠ 0 := by
  simp [momentLevel]

/-! ### The code-level weights -/

/-- The rational code of the `i`-th moment approximation, read out of a stream prefix at
depth `momentDepth n`. -/
def momentSliceCode (n : ℕ) (w : List ℕ) (i : ℕ) : ℕ :=
  w.getD (Nat.pair i (momentDepth n)) 0

/-- The `j`-th signed term of the alternating expansion of the `k`-th binomial weight,
as a rational code. -/
def momentTermCode (n : ℕ) (w : List ℕ) (k j : ℕ) : ℕ :=
  if j % 2 = 0 then
    mulCode (natCode ((momentLevel n - k).choose j)) (momentSliceCode n w (k + j))
  else
    negCode (mulCode (natCode ((momentLevel n - k).choose j)) (momentSliceCode n w (k + j)))

/-- The rational code of the `k`-th approximate binomial weight of
`ComputableAnalysis.Measure.MomentWeights`, built from the coded moment approximations by
exact rational arithmetic. -/
def momentWeightCode (n : ℕ) (w : List ℕ) (k : ℕ) : ℕ :=
  mulCode (natCode ((momentLevel n).choose k))
    (sumCode ((List.range (momentLevel n - k + 1)).map (momentTermCode n w k)))

/-- The atom list emitted at output precision `n`: the grid indices of the level-`N` grid
paired with the coded approximate weights. The decoder clamps and renormalises. -/
def momentAtomList (n : ℕ) (w : List ℕ) : List (ℕ × ℕ) :=
  (List.range (momentLevel n + 1)).map fun k ↦
    (fracCode k (momentLevel n), momentWeightCode n w k)

/-- The postprocessor of the realizer: on `Nat.pair n (encode w)` it emits the atomic
index encoding `momentAtomList n w`. -/
def momentPost (v : ℕ) : ℕ :=
  Encodable.encode (momentAtomList v.unpair.1 (Denumerable.ofNat (List ℕ) v.unpair.2))

/-! ### Primitive recursiveness of the postprocessor -/

/-- `momentLevel` is primitive recursive. -/
theorem primrec_momentLevel : Primrec momentLevel :=
  primrec₂_natPow.comp (Primrec.const 2)
    (Primrec.nat_mul.comp (Primrec.const 3) Primrec.succ)

/-- `momentDepth` is primitive recursive. -/
theorem primrec_momentDepth : Primrec momentDepth :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_momentLevel)
      Primrec.id)
    (Primrec.const 2)

/-- `momentBound` is primitive recursive. -/
theorem primrec_momentBound : Primrec momentBound :=
  primrec₂_natPow.comp
    (Primrec.nat_add.comp (Primrec.nat_add.comp primrec_momentLevel primrec_momentDepth)
      (Primrec.const 1))
    (Primrec.const 2)

/-- Slice codes are primitive recursive in the packed argument `((n, w), i)`. -/
private theorem primrec_sliceAux :
    Primrec fun x : (ℕ × List ℕ) × ℕ ↦ momentSliceCode x.1.1 x.1.2 x.2 :=
  (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst)
    (Primrec₂.natPair.comp Primrec.snd
      (primrec_momentDepth.comp (Primrec.fst.comp Primrec.fst)))

/-- The unsigned part of a term code is primitive recursive in `(((n, w), k), j)`. -/
private theorem primrec_termBodyAux :
    Primrec fun x : ((ℕ × List ℕ) × ℕ) × ℕ ↦
      mulCode (natCode ((momentLevel x.1.1.1 - x.1.2).choose x.2))
        (momentSliceCode x.1.1.1 x.1.1.2 (x.1.2 + x.2)) :=
  primrec₂_mulCode.comp
    (primrec_natCode.comp
      (primrec₂_choose.comp
        (Primrec.nat_sub.comp
          (primrec_momentLevel.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst))
        Primrec.snd))
    (primrec_sliceAux.comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_add.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)))

/-- Term codes are primitive recursive in the packed argument `(((n, w), k), j)`. -/
private theorem primrec_termAux :
    Primrec fun x : ((ℕ × List ℕ) × ℕ) × ℕ ↦ momentTermCode x.1.1.1 x.1.1.2 x.1.2 x.2 :=
  Primrec.ite
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0))
    primrec_termBodyAux (primrec_negCode.comp primrec_termBodyAux)

/-- Weight codes are primitive recursive in the packed argument `((n, w), k)`. -/
private theorem primrec_weightAux :
    Primrec fun x : (ℕ × List ℕ) × ℕ ↦ momentWeightCode x.1.1 x.1.2 x.2 :=
  primrec₂_mulCode.comp
    (primrec_natCode.comp
      (primrec₂_choose.comp (primrec_momentLevel.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd))
    (primrec_sumCode.comp
      (Primrec.list_map
        (Primrec.list_range.comp
          (Primrec.nat_add.comp
            (Primrec.nat_sub.comp
              (primrec_momentLevel.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
            (Primrec.const 1)))
        primrec_termAux.to₂))

/-- The atom list is primitive recursive in the packed argument `(n, w)`. -/
private theorem primrec_atomAux :
    Primrec fun x : ℕ × List ℕ ↦ momentAtomList x.1 x.2 :=
  Primrec.list_map
    (Primrec.list_range.comp
      (Primrec.nat_add.comp (primrec_momentLevel.comp Primrec.fst) (Primrec.const 1)))
    (Primrec.pair
      (primrec₂_fracCode.comp Primrec.snd
        (primrec_momentLevel.comp (Primrec.fst.comp Primrec.fst)))
      primrec_weightAux).to₂

/-- `momentPost` is primitive recursive: the whole realizer is rational arithmetic on a
decoded prefix, with primitive-recursive index bookkeeping. -/
theorem primrec_momentPost : Primrec momentPost := by
  have hpair : Primrec fun v : ℕ ↦ (v.unpair.1, Denumerable.ofNat (List ℕ) v.unpair.2) :=
    Primrec.pair (Primrec.fst.comp Primrec.unpair)
      ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp Primrec.unpair))
  -- `henc` is elaborated without an expected type on purpose: ascribing the composite
  -- forces a unification that does not terminate in reasonable time.
  have henc := Primrec.encode.comp (primrec_atomAux.comp hpair)
  unfold momentPost
  exact henc

/-! ### The value specification of the realizer -/

/-- The real moment approximation named by the depth-`momentDepth n` slice of the `i`-th
moment name inside `F`. -/
noncomputable def momentApprox (F : Baire) (n i : ℕ) : ℝ :=
  ((ratOfCode (F (Nat.pair i (momentDepth n))) : ℚ) : ℝ)

/-- A moment name approximates every moment to within `2⁻ᵈ` at reading depth `d`. -/
theorem abs_momentApprox_sub_le {F : Baire} {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)}
    (hF : MomentNames F η) (n i : ℕ) :
    |momentApprox F n i - moment η i| ≤ (2 : ℝ)⁻¹ ^ momentDepth n := by
  have h := realPresentation.cauchyRep_names_iff.mp
    (Representation.subtype_names_iff.mp (hF i)) (momentDepth n)
  rw [Real.dist_eq] at h
  exact h

/-- A list sum over `List.range` is the corresponding `Finset.range` sum. -/
private theorem listSum_map_range {M : Type*} [AddCommMonoid M] (m : ℕ) (g : ℕ → M) :
    ((List.range m).map g).sum = ∑ j ∈ Finset.range m, g j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, ih]
    simp

/-- The decoded term code is the corresponding signed term of the moment expansion. -/
private theorem ratOfCode_momentTermCode (n : ℕ) (w : List ℕ) (k j : ℕ) :
    ratOfCode (momentTermCode n w k j)
      = (-1 : ℚ) ^ j * ((momentLevel n - k).choose j : ℚ)
          * ratOfCode (momentSliceCode n w (k + j)) := by
  rw [momentTermCode]
  split_ifs with h
  · rw [ratOfCode_mulCode, ratOfCode_natCode, (Nat.even_iff.mpr h).neg_one_pow, one_mul]
  · rw [ratOfCode_negCode, ratOfCode_mulCode, ratOfCode_natCode,
      (Nat.odd_iff.mpr (Nat.mod_two_eq_zero_or_one j |>.resolve_left h)).neg_one_pow]
    ring

/-- The weight code decodes to the exact rational alternating sum of the coded slices. -/
private theorem ratOfCode_momentWeightCode_rat (n : ℕ) (w : List ℕ) (k : ℕ) :
    ratOfCode (momentWeightCode n w k)
      = ((momentLevel n).choose k : ℚ) * ∑ j ∈ Finset.range (momentLevel n - k + 1),
          (-1 : ℚ) ^ j * ((momentLevel n - k).choose j : ℚ)
            * ratOfCode (momentSliceCode n w (k + j)) := by
  rw [momentWeightCode, ratOfCode_mulCode, ratOfCode_natCode, ratOfCode_sumCode, List.map_map,
    listSum_map_range]
  exact congrArg _ (Finset.sum_congr rfl fun j _ ↦ ratOfCode_momentTermCode n w k j)

/-- Reading a slice out of the prefix recovers the oracle coordinate. -/
theorem momentSliceCode_streamTake (F : Baire) {n i : ℕ} (hi : i ≤ momentLevel n) :
    momentSliceCode n (streamTake F (momentBound n)) i = F (Nat.pair i (momentDepth n)) := by
  have hlt : Nat.pair i (momentDepth n) < (streamTake F (momentBound n)).length := by
    rw [length_streamTake]
    exact pair_momentDepth_lt_momentBound hi
  rw [momentSliceCode, List.getD_eq_getElem _ _ hlt, getElem_streamTake]

/-- The `ℕ`-indexed form of `approxWeight`, convenient for `Finset.range` bookkeeping. -/
noncomputable def approxWeightNat (N k : ℕ) (a : ℕ → ℝ) : ℝ :=
  (N.choose k : ℝ) * ∑ j ∈ Finset.range (N - k + 1),
    (-1 : ℝ) ^ j * ((N - k).choose j : ℝ) * a (k + j)

/-- On `Fin (N + 1)` indices the `ℕ`-indexed form is `approxWeight`. -/
theorem approxWeightNat_coe (N : ℕ) (k : Fin (N + 1)) (a : ℕ → ℝ) :
    approxWeightNat N (k : ℕ) a = approxWeight N k a := rfl

/-- **The weight codes decode to the approximate weights.** -/
theorem ratOfCode_momentWeightCode (F : Baire) {n k : ℕ} (hk : k ≤ momentLevel n) :
    ((ratOfCode (momentWeightCode n (streamTake F (momentBound n)) k) : ℚ) : ℝ)
      = approxWeightNat (momentLevel n) k (momentApprox F n) := by
  have hrat : ratOfCode (momentWeightCode n (streamTake F (momentBound n)) k)
      = ((momentLevel n).choose k : ℚ) * ∑ j ∈ Finset.range (momentLevel n - k + 1),
          (-1 : ℚ) ^ j * ((momentLevel n - k).choose j : ℚ)
            * ratOfCode (F (Nat.pair (k + j) (momentDepth n))) := by
    rw [ratOfCode_momentWeightCode_rat]
    refine congrArg _ (Finset.sum_congr rfl fun j hj ↦ ?_)
    rw [Finset.mem_range] at hj
    rw [momentSliceCode_streamTake F (show k + j ≤ momentLevel n by omega)]
  rw [hrat, approxWeightNat]
  simp only [momentApprox]
  push_cast
  rfl

/-- The decoder's clamped weight at a weight code is the clipped approximate weight. -/
theorem clampedWeight_momentWeightCode (F : Baire) {n k : ℕ} (hk : k ≤ momentLevel n) :
    ((clampedWeight (momentWeightCode n (streamTake F (momentBound n)) k) : ℚ) : ℝ)
      = clipWeight (approxWeightNat (momentLevel n) k (momentApprox F n)) := by
  rw [clampedWeight, clipWeight, ← ratOfCode_momentWeightCode F hk]
  push_cast
  rfl

/-! ### The emitted atom list -/

/-- The emitted atom list has one atom per grid point. -/
theorem length_momentAtomList (n : ℕ) (w : List ℕ) :
    (momentAtomList n w).length = momentLevel n + 1 := by
  simp [momentAtomList]

/-- The `j`-th atom of the emitted list is the `j`-th grid point with its weight code. -/
theorem getElem_momentAtomList (n : ℕ) (w : List ℕ)
    (j : Fin (momentAtomList n w).length) :
    (momentAtomList n w)[j]
      = (fracCode (j : ℕ) (momentLevel n), momentWeightCode n w (j : ℕ)) := by
  rw [Fin.getElem_fin]
  simp [momentAtomList]

/-- The decoder's total clamped weight is the clipped total of
`ComputableAnalysis.Measure.MomentWeights`. -/
theorem clampedWeightSum_momentAtomList (F : Baire) (n : ℕ) :
    ((clampedWeightSum (momentAtomList n (streamTake F (momentBound n))) : ℚ) : ℝ)
      = totalClipWeight (momentLevel n) (momentApprox F n) := by
  have hnat : totalClipWeight (momentLevel n) (momentApprox F n)
      = ∑ k ∈ Finset.range (momentLevel n + 1),
          clipWeight (approxWeightNat (momentLevel n) k (momentApprox F n)) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun k ↦ clipWeight (approxWeightNat (momentLevel n) k (momentApprox F n)))]
    rfl
  have hlhs : clampedWeightSum (momentAtomList n (streamTake F (momentBound n)))
      = ∑ k ∈ Finset.range (momentLevel n + 1),
          clampedWeight (momentWeightCode n (streamTake F (momentBound n)) k) := by
    rw [clampedWeightSum, momentAtomList, List.map_map, listSum_map_range]
    rfl
  rw [hlhs, hnat]
  push_cast
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  exact clampedWeight_momentWeightCode F (by omega)

/-! ### The error budget -/

/-- The dyadic cancellation behind the error budget. -/
private theorem dyadic_cancel (N m : ℕ) :
    (2 : ℝ) ^ (2 * N) * (2 : ℝ)⁻¹ ^ (2 * N + m) = (2 : ℝ)⁻¹ ^ m := by
  rw [pow_add, ← mul_assoc, ← mul_pow]
  norm_num

/-- The crude bound `3 ^ N ≤ 2 ^ (2 N)` keeping the whole schedule dyadic. -/
private theorem three_pow_le (N : ℕ) : (3 : ℝ) ^ N ≤ (2 : ℝ) ^ (2 * N) := by
  rw [pow_mul]
  gcongr
  norm_num

/-- **The moment-error budget.** Reading the moments at depth `momentDepth n` makes the
`ℓ¹` weight error `3 ^ N · δ` at most `2⁻⁽ⁿ⁺²⁾`. -/
theorem momentError_le (n : ℕ) :
    (3 : ℝ) ^ momentLevel n * (2 : ℝ)⁻¹ ^ momentDepth n ≤ (2 : ℝ)⁻¹ ^ (n + 2) := by
  refine (mul_le_mul_of_nonneg_right (three_pow_le (momentLevel n))
    (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ momentDepth n)).trans_eq ?_
  rw [momentDepth, show 2 * momentLevel n + n + 2 = 2 * momentLevel n + (n + 2) by ring,
    dyadic_cancel]

/-- The budget is small enough for `totalClipWeight_pos` to apply. -/
theorem momentError_lt_one (n : ℕ) :
    (3 : ℝ) ^ momentLevel n * (2 : ℝ)⁻¹ ^ momentDepth n < 1 :=
  (momentError_le n).trans_lt (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))

/-- The doubled budget — the price of normalisation — still fits the half-step `2⁻⁽ⁿ⁺¹⁾`. -/
theorem momentError_double_le (n : ℕ) :
    2 * (3 : ℝ) ^ momentLevel n * (2 : ℝ)⁻¹ ^ momentDepth n ≤ (2 : ℝ)⁻¹ ^ (n + 1) := by
  calc 2 * (3 : ℝ) ^ momentLevel n * (2 : ℝ)⁻¹ ^ momentDepth n
      = 2 * ((3 : ℝ) ^ momentLevel n * (2 : ℝ)⁻¹ ^ momentDepth n) := by ring
    _ ≤ 2 * (2 : ℝ)⁻¹ ^ (n + 2) :=
        mul_le_mul_of_nonneg_left (momentError_le n) (by norm_num)
    _ = (2 : ℝ)⁻¹ ^ (n + 1) := by rw [pow_succ]; ring

/-! ### The realizer's estimate -/

/-- **The emitted atomic measure, over the Bernstein grid.** The decoder's clamping and
renormalisation reproduce exactly the `clipWeight`/`normWeight` repair of
`ComputableAnalysis.Measure.MomentWeights`, and the emitted dense indices are the grid
points. -/
theorem toMeasure_atomic_momentAtomList {F : Baire}
    {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)} (hF : MomentNames F η) (n : ℕ) :
    (atomic unitIntervalPresentation
        (Encodable.encode (momentAtomList n (streamTake F (momentBound n))))).toMeasure
      = ∑ k : Fin (momentLevel n + 1),
          ENNReal.ofReal (normWeight (momentLevel n) k (momentApprox F n))
            • Measure.dirac (bernstein.z k) := by
  have hN : momentLevel n ≠ 0 := momentLevel_ne_zero n
  have ha : ∀ i, |momentApprox F n i - moment η i| ≤ (2 : ℝ)⁻¹ ^ momentDepth n :=
    fun i ↦ abs_momentApprox_sub_le hF n i
  have hpos : 0 < totalClipWeight (momentLevel n) (momentApprox F n) :=
    totalClipWeight_pos (momentLevel n) ha (momentError_lt_one n)
  have hsum := clampedWeightSum_momentAtomList F n
  have hS0 : clampedWeightSum (momentAtomList n (streamTake F (momentBound n))) ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero] at hsum
    exact hpos.ne hsum
  have hlen : (momentAtomList n (streamTake F (momentBound n))).length = momentLevel n + 1 :=
    length_momentAtomList n _
  rw [atomic_encode_eq_atomicOfList, toMeasure_atomicOfList_of_ne_zero _ hS0,
    ← Fin.sum_congr' (fun k : Fin (momentLevel n + 1) ↦
      ENNReal.ofReal (normWeight (momentLevel n) k (momentApprox F n))
        • Measure.dirac (bernstein.z k)) hlen]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hj : (j : ℕ) ≤ momentLevel n := by
    have := j.isLt
    omega
  have hw : (((clampedWeight (momentAtomList n (streamTake F (momentBound n)))[j].2
        / clampedWeightSum (momentAtomList n (streamTake F (momentBound n))) : ℚ)) : ℝ)
      = normWeight (momentLevel n) (Fin.cast hlen j) (momentApprox F n) := by
    rw [getElem_momentAtomList n _ j, normWeight, ← approxWeightNat_coe]
    push_cast
    rw [clampedWeight_momentWeightCode F hj, hsum]
    rfl
  have hd : unitIntervalPresentation.dense
      (momentAtomList n (streamTake F (momentBound n)))[j].1
      = bernstein.z (Fin.cast hlen j) := by
    rw [getElem_momentAtomList n _ j]
    exact dense_fracCode hN (Fin.cast hlen j)
  rw [hw, hd]

/-- **The realizer meets the weak-name rate.** Splitting through the binomial approximant:
`2⁻⁽ⁿ⁺¹⁾` from the Chebyshev estimate of
`ComputableAnalysis.Measure.BinomialApproximant` and `2⁻⁽ⁿ⁺¹⁾` from the `ℓ¹` weight
estimate of `ComputableAnalysis.Measure.MomentWeights`, on the *same* atoms. -/
theorem levyProkhorovDist_atomic_momentAtomList_le {F : Baire}
    {η : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)} (hF : MomentNames F η) (n : ℕ) :
    levyProkhorovDist η.toMeasure
        (atomic unitIntervalPresentation
          (Encodable.encode (momentAtomList n (streamTake F (momentBound n))))).toMeasure
      ≤ (2 : ℝ)⁻¹ ^ n := by
  have ha : ∀ i, |momentApprox F n i - moment η i| ≤ (2 : ℝ)⁻¹ ^ momentDepth n :=
    fun i ↦ abs_momentApprox_sub_le hF n i
  have hbridge := levyProkhorovDist_le_sum_abs
    (fun k : Fin (momentLevel n + 1) ↦ bernstein.z k)
    (fun k ↦ binomialWeight (momentLevel n) k η)
    (fun k ↦ normWeight (momentLevel n) k (momentApprox F n))
    (fun k ↦ normWeight_nonneg (momentLevel n) k (momentApprox F n))
    (binomialApproximant (momentLevel n) η)
    (atomic unitIntervalPresentation
      (Encodable.encode (momentAtomList n (streamTake F (momentBound n)))))
    (binomialApproximant_toMeasure (momentLevel n) η)
    (toMeasure_atomic_momentAtomList hF n)
  have hl1 : ∑ k : Fin (momentLevel n + 1),
      |binomialWeight (momentLevel n) k η
        - normWeight (momentLevel n) k (momentApprox F n)|
      ≤ 2 * 3 ^ momentLevel n * (2 : ℝ)⁻¹ ^ momentDepth n := by
    rw [Finset.sum_congr rfl fun k _ ↦
      abs_sub_comm (binomialWeight (momentLevel n) k η)
        (normWeight (momentLevel n) k (momentApprox F n))]
    exact sum_abs_normWeight_sub_le (momentLevel n) ha (momentError_lt_one n)
  have hfirst : levyProkhorovDist η.toMeasure
      (binomialApproximant (momentLevel n) η).toMeasure ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    levyProkhorovDist_binomialApproximant_le (n + 1) η
  have htri := levyProkhorovDist_triangle η.toMeasure
    (binomialApproximant (momentLevel n) η).toMeasure
    (atomic unitIntervalPresentation
      (Encodable.encode (momentAtomList n (streamTake F (momentBound n))))).toMeasure
  have hhalf : (2 : ℝ)⁻¹ ^ (n + 1) + (2 : ℝ)⁻¹ ^ (n + 1) = (2 : ℝ)⁻¹ ^ n := by
    rw [pow_succ]
    ring
  linarith [hbridge.trans (hl1.trans (momentError_double_le n))]

end ComputableAnalysis
