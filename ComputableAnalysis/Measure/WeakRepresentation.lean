/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.ForMathlib.PrimrecArith
import ComputableAnalysis.Metric.CauchyRepresentation
import ComputableAnalysis.Metric.RatCodeArith
import ComputableAnalysis.ForMathlib.REPredClosure
import ComputableAnalysis.Measure.FiniteAtomicPerturbation
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Data.List.GetD

/-!
# The weak measure representation and the effective Prokhorov presentation

Over the generic contract `[MetricSpace X] [MeasurableSpace X] [BorelSpace X]` with a
`ComputableMetricPresentation X`, this unit builds the effective theory of the weak
topology on `ProbabilityMeasure X` (unit 27):

* `atomicOfList` / `atomic` — the rational-atomic dense sequence, built **directly** as
  finite weighted sums of Dirac measures at dense points, with a total decoding scheme
  (an index decodes to a list of `(dense-index, weight-code)` pairs; weights are clamped
  to `[0,1]` and renormalized; zero total weight defaults to `dirac (P.dense 0)`).
  The decoder carries a public specification — `clampedWeight`, `clampedWeightSum`,
  `clampedWeight_eq_ratOfCode_clampCode`, `atomic_encode_eq_atomicOfList` and the two
  branch equations `toMeasure_atomicOfList_of_ne_zero` /
  `toMeasure_atomicOfList_of_eq_zero` — so that a weak name can be *constructed* outside
  this file, not only consumed.
* `exists_atomic_close` — generic Lévy–Prokhorov density of the atomics: the
  first-dense-point cell decomposition, finite truncation by countable additivity (no
  tightness theorem), and rational-weight perturbation.
* `WeakMeasureNames` / `weakMeasureRep` — the weak measure representation, stated
  **directly on the carrier** `ProbabilityMeasure X`: a name is a stream of atomic
  indices approximating the measure at the pinned rate `((2:ℝ)⁻¹)^n` in Lévy–Prokhorov
  distance, with the `@[simp]` names characterization `weakMeasureRep_names_iff`.
* `exists_certifiedWeightCode` / `exists_completeCertifiedWeightCode` — masked atomic masses
  from positive membership information alone. The first bounds the mass below from a bitmask
  over the raw decoded list; the second supplies the uniform normalized atom list, whose
  accumulator is exact once the mask is complete.
* `prokhorovPresentation` — the effective Prokhorov presentation of the `LevyProkhorov`
  metric synonym: both convention 7 semidecisions are fully discharged through the Σ₁
  characterizations of strict LP-distance comparisons between atomics (five-level Σ₁
  assemblies through unit 26's `REPred` closure riders, with subset tables as bounded
  bitmasks and coded-rational weight arithmetic).

Quarantine rule (frozen): the `LevyProkhorov` synonym never appears in a
`Representation` carrier or a public statement other than `prokhorovPresentation`'s
type; the synonym-side `cauchyRep` bridge lemmas are private. Implementation
disciplines: the coded-rational layer is sealed `[local irreducible]` after its
semantics/`Primrec` lemmas, and `repred_comp` on the gt-side assembly pins `(g := ...)`
explicitly.
-/

set_option linter.style.longFile 2300

namespace ComputableAnalysis

open MeasureTheory Metric Encodable Denumerable

/-! ### The total atomic decoding: clamped weights of a decoded atom list -/

/-- The clamped rational weight of a weight code: the atomic decoder reads the second
component of every decoded pair through this function. -/
def clampedWeight (c : ℕ) : ℚ := max 0 (min 1 (ratOfCode c))

/-- The decoded weight of a code is the public rational-code clamp `clampCode` read
through `ratOfCode`.  This ties the atomic decoder to the coded-rational API, so a
weight code may be produced — and its decoded weight computed — without unfolding
`clampedWeight`. -/
theorem clampedWeight_eq_ratOfCode_clampCode (c : ℕ) :
    clampedWeight c = ratOfCode (clampCode c) :=
  (ratOfCode_clampCode c).symm

/-- Decoded weights are nonnegative. -/
theorem clampedWeight_nonneg (c : ℕ) : 0 ≤ clampedWeight c := le_max_left _ _

/-- The (rational) total clamped weight of a decoded atom list: the normalizing constant
of `atomicOfList`, whose vanishing selects the default branch. -/
def clampedWeightSum (l : List (ℕ × ℕ)) : ℚ := (l.map fun pr => clampedWeight pr.2).sum

/-- The total clamped weight is nonnegative, so the branch test `clampedWeightSum l ≠ 0`
of `atomicOfList` is equivalent to `0 < clampedWeightSum l`. -/
theorem clampedWeightSum_nonneg (l : List (ℕ × ℕ)) : 0 ≤ clampedWeightSum l :=
  List.sum_nonneg fun x hx => by
    obtain ⟨pr, -, rfl⟩ := List.mem_map.mp hx
    exact clampedWeight_nonneg _

/-- A mapped list sum as a `Fin` sum over positions. -/
private theorem listSum_map_eq_finSum {β M : Type*} [AddCommMonoid M] (l : List β)
    (g : β → M) : (l.map g).sum = ∑ i : Fin l.length, g l[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

/-- The normalized weights of a decoded atom list sum to `1`.  Together with
`normalizedWeight_nonneg` this exhibits the weights of
`toMeasure_atomicOfList_of_ne_zero` as a probability vector. -/
theorem sum_normalizedWeight {l : List (ℕ × ℕ)} (h0 : clampedWeightSum l ≠ 0) :
    ∑ i : Fin l.length, ((clampedWeight l[i].2 / clampedWeightSum l : ℚ) : ℝ) = 1 := by
  have : ∑ i : Fin l.length, ((clampedWeight l[i].2 / clampedWeightSum l : ℚ) : ℝ)
      = (((∑ i : Fin l.length, clampedWeight l[i].2) / clampedWeightSum l : ℚ) : ℝ) := by
    push_cast
    rw [Finset.sum_div]
  rw [this]
  have hsum : ∑ i : Fin l.length, clampedWeight l[i].2 = clampedWeightSum l :=
    (listSum_map_eq_finSum l fun pr => clampedWeight pr.2).symm
  rw [hsum, div_self h0]
  norm_num

/-- The normalized weights of a decoded atom list are nonnegative. -/
theorem normalizedWeight_nonneg {l : List (ℕ × ℕ)} (h0 : clampedWeightSum l ≠ 0)
    (i : Fin l.length) :
    (0 : ℝ) ≤ ((clampedWeight l[i].2 / clampedWeightSum l : ℚ) : ℝ) := by
  have hpos : (0 : ℚ) < clampedWeightSum l :=
    lt_of_le_of_ne (clampedWeightSum_nonneg l) (Ne.symm h0)
  exact_mod_cast div_nonneg (clampedWeight_nonneg _) hpos.le

/-! Uniform (total, `ℕ`-indexed) atomic data of a decoded list: atom count, dense-point
index, and rational weight (the default zero-weight branch has one atom at index `0`). -/

/-- Number of atoms of the decoded measure (the default branch has one atom). -/
private def atomCount (l : List (ℕ × ℕ)) : ℕ := if clampedWeightSum l = 0 then 1 else l.length

/-- Dense-point index of the `i`-th atom. -/
private def atomIdx (l : List (ℕ × ℕ)) (i : ℕ) : ℕ :=
  if clampedWeightSum l = 0 then 0 else (l.getD i (0, 0)).1

/-- Rational weight of the `i`-th atom. -/
private def atomWt (l : List (ℕ × ℕ)) (i : ℕ) : ℚ :=
  if clampedWeightSum l = 0 then 1 else clampedWeight (l.getD i (0, 0)).2 / clampedWeightSum l

private theorem atomWt_nonneg (l : List (ℕ × ℕ)) (i : ℕ) : 0 ≤ atomWt l i := by
  rw [atomWt]
  split_ifs with h0
  · exact zero_le_one
  · have hpos : (0 : ℚ) < clampedWeightSum l :=
      lt_of_le_of_ne (clampedWeightSum_nonneg l) (Ne.symm h0)
    exact div_nonneg (clampedWeight_nonneg _) hpos.le

section Atomics

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

omit [MetricSpace X] [BorelSpace X] in
/-- A finite weighted sum of Diracs with nonnegative weights summing to `1` is a
probability measure — the direct bundling behind `atomicOfList`. -/
private theorem isProbabilityMeasure_sum_smul_dirac {k : ℕ} {a : Fin k → ℝ}
    (x : Fin k → X) (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) :
    IsProbabilityMeasure (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) := by
  constructor
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => ha i, hsum, ENNReal.ofReal_one]

/-- The atomic probability measure of a decoded atom list: directly a weighted sum of
Dirac measures at dense points of the presentation.  Weight codes decode through
`ratOfCode`, clamped to `[0,1]` and renormalized by their positive rational sum; zero
total weight (in particular the empty list) denotes the default `dirac (P.dense 0)`. -/
noncomputable def atomicOfList (l : List (ℕ × ℕ)) : ProbabilityMeasure X :=
  if h0 : clampedWeightSum l = 0 then ⟨Measure.dirac (P.dense 0), inferInstance⟩
  else
    ⟨∑ i : Fin l.length,
        ENNReal.ofReal ((clampedWeight l[i].2 / clampedWeightSum l : ℚ) : ℝ)
          • Measure.dirac (P.dense l[i].1),
      isProbabilityMeasure_sum_smul_dirac _ (normalizedWeight_nonneg h0) (sum_normalizedWeight h0)⟩

/-- The rational-atomic dense sequence of the weak topology on `ProbabilityMeasure X`:
an index `m` decodes (via `Denumerable (List (ℕ × ℕ))`) to a list of
`(dense-index, weight-code)` pairs, then to the atomic measure `atomicOfList`. -/
noncomputable def atomic (m : ℕ) : ProbabilityMeasure X :=
  atomicOfList P (ofNat (List (ℕ × ℕ)) m)

omit [BorelSpace X] in
/-- The atomic sequence hits every decoded atom list: at the index encoding `l` it is
`atomicOfList P l`.  This is what lets an explicit atom list be used as an index into
the dense sequence, hence inside `WeakMeasureNames`. -/
theorem atomic_encode_eq_atomicOfList (l : List (ℕ × ℕ)) :
    atomic P (Encodable.encode l) = atomicOfList P l := by
  rw [atomic, Denumerable.ofNat_encode]

omit [BorelSpace X] in
/-- **Specification of `atomicOfList`, main branch.**  When the total clamped weight is
nonzero, the decoded measure is the weighted sum of Dirac masses at the dense points
named by the first components, with the normalized clamped weights of the second
components. -/
theorem toMeasure_atomicOfList_of_ne_zero {l : List (ℕ × ℕ)}
    (h0 : clampedWeightSum l ≠ 0) :
    (atomicOfList P l).toMeasure
      = ∑ i : Fin l.length,
          ENNReal.ofReal ((clampedWeight l[i].2 / clampedWeightSum l : ℚ) : ℝ)
            • Measure.dirac (P.dense l[i].1) := by
  rw [atomicOfList, dif_neg h0]
  rfl

omit [BorelSpace X] in
/-- **Specification of `atomicOfList`, default branch.**  Zero total clamped weight (in
particular the empty list) denotes the point mass at the first dense point. -/
theorem toMeasure_atomicOfList_of_eq_zero {l : List (ℕ × ℕ)}
    (h0 : clampedWeightSum l = 0) :
    (atomicOfList P l).toMeasure = Measure.dirac (P.dense 0) := by
  rw [atomicOfList, dif_pos h0]
  rfl

omit [BorelSpace X] in
/-- The decoded atomic measure in uniform form: a `Fin (atomCount l)` weighted Dirac
sum over `atomIdx`/`atomWt`. -/
private theorem toMeasure_atomic_eq_sum (l : List (ℕ × ℕ)) :
    (atomicOfList P l).toMeasure
      = ∑ i : Fin (atomCount l),
          ENNReal.ofReal ((atomWt l i : ℚ) : ℝ) • Measure.dirac (P.dense (atomIdx l i)) := by
  by_cases h0 : clampedWeightSum l = 0
  · rw [toMeasure_atomicOfList_of_eq_zero P h0]
    have hc : (1 : ℕ) = atomCount l := (if_pos h0).symm
    rw [← Fin.sum_congr' _ hc, Fin.sum_univ_one]
    simp [atomWt, atomIdx, h0]
  · rw [toMeasure_atomicOfList_of_ne_zero P h0]
    have hc : l.length = atomCount l := (if_neg h0).symm
    rw [← Fin.sum_congr' _ hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.val_cast]
    simp only [atomWt, atomIdx, if_neg h0]
    rw [List.getD_eq_getElem _ _ j.2]
    rfl

/-! #### Generic LP density: cells, truncation, discretization

The first-dense-point cell decomposition: `cell P r i` collects the points whose FIRST
dense point within distance `r` is `P.dense i`.  Cells are Borel, pairwise disjoint,
cover `X` (density — no tightness theorem), and have radius `≤ r` around their atom. -/

/-- The level-`r` cell of dense-point index `i`. -/
private def cell (r : ℝ) (i : ℕ) : Set X :=
  {z | dist z (P.dense i) ≤ r ∧ ∀ j < i, r < dist z (P.dense j)}

private theorem measurableSet_cell (r : ℝ) (i : ℕ) : MeasurableSet (cell P r i) := by
  have hset : cell P r i
      = Metric.closedBall (P.dense i) r
          ∩ ⋂ j ∈ Finset.range i, (Metric.closedBall (P.dense j) r)ᶜ := by
    ext z
    simp only [cell, Set.mem_setOf_eq, Set.mem_inter_iff, Metric.mem_closedBall,
      Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range, not_le]
  rw [hset]
  exact measurableSet_closedBall.inter
    (MeasurableSet.biInter (Finset.range i).countable_toSet fun j _ =>
      measurableSet_closedBall.compl)

omit [MeasurableSpace X] [BorelSpace X] in
private theorem cell_pairwise_disjoint (r : ℝ) :
    Pairwise (Function.onFun Disjoint (cell P r)) := by
  have key : ∀ i j, i < j → Disjoint (cell P r i) (cell P r j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro z ⟨hzi, -⟩ ⟨-, hzj⟩
    exact absurd hzi (not_le.mpr (hzj i hij))
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

omit [MeasurableSpace X] [BorelSpace X] in
private theorem iUnion_cell {r : ℝ} (hr : 0 < r) : ⋃ i, cell P r i = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  have hex : ∃ i, dist z (P.dense i) ≤ r := by
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp P.denseRange z r hr
    exact ⟨i, hi.le⟩
  classical
  exact Set.mem_iUnion.mpr
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_le.mp (Nat.find_min hex hj)⟩

/-- Cell masses sum to `1`: countable additivity over the cell partition (this replaces
any tightness theorem in the finite-truncation step). -/
private theorem tsum_measure_cell (μ : ProbabilityMeasure X) {r : ℝ} (hr : 0 < r) :
    ∑' i, μ.toMeasure (cell P r i) = 1 := by
  rw [← measure_iUnion (cell_pairwise_disjoint P r) (measurableSet_cell P r),
    iUnion_cell P hr, measure_univ]

/-- The real mass of a cell. -/
private noncomputable def cellMass (μ : ProbabilityMeasure X) (r : ℝ) (i : ℕ) : ℝ :=
  (μ.toMeasure (cell P r i)).toReal

omit [BorelSpace X] in
private theorem cellMass_nonneg (μ : ProbabilityMeasure X) (r : ℝ) (i : ℕ) :
    0 ≤ cellMass P μ r i := ENNReal.toReal_nonneg

omit [BorelSpace X] in
private theorem cellMass_le_one (μ : ProbabilityMeasure X) (r : ℝ) (i : ℕ) :
    cellMass P μ r i ≤ 1 := by
  have h := prob_le_one (μ := μ.toMeasure) (s := cell P r i)
  simpa [cellMass] using ENNReal.toReal_mono ENNReal.one_ne_top h

private theorem measure_biUnion_range_cell (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    μ.toMeasure (⋃ i ∈ Finset.range N, cell P r i)
      = ∑ i ∈ Finset.range N, μ.toMeasure (cell P r i) :=
  measure_biUnion_finset ((cell_pairwise_disjoint P r).set_pairwise _)
    fun i _ => measurableSet_cell P r i

private theorem sum_range_cellMass_eq (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, cellMass P μ r i
      = (μ.toMeasure (⋃ i ∈ Finset.range N, cell P r i)).toReal := by
  rw [measure_biUnion_range_cell, ENNReal.toReal_sum fun i _ => measure_ne_top _ _]
  exact Finset.sum_congr rfl fun i _ => rfl

private theorem sum_range_cellMass_le_one (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    ∑ i ∈ Finset.range N, cellMass P μ r i ≤ 1 := by
  rw [sum_range_cellMass_eq]
  have h := prob_le_one (μ := μ.toMeasure) (s := ⋃ i ∈ Finset.range N, cell P r i)
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top h

/-- The truncation remainder: the mass not captured by the first `N` cells (it is
dumped onto atom `0`). -/
private noncomputable def tailMass (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) : ℝ :=
  1 - ∑ i ∈ Finset.range N, cellMass P μ r i

private theorem tailMass_nonneg (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    0 ≤ tailMass P μ r N :=
  sub_nonneg.mpr (sum_range_cellMass_le_one P μ r N)

omit [BorelSpace X] in
private theorem tailMass_le_one (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    tailMass P μ r N ≤ 1 := by
  have h := Finset.sum_nonneg fun i (_ : i ∈ Finset.range N) => cellMass_nonneg P μ r i
  rw [tailMass]
  linarith

/-- Existence of a truncation level with small remainder: monotone convergence of the
finite partial cell sums (countable additivity), no tightness theorem. -/
private theorem exists_tailMass_le (μ : ProbabilityMeasure X) {r : ℝ} (hr : 0 < r)
    {ε' : ℝ} (hε' : 0 < ε') : ∃ N, tailMass P μ r N ≤ ε' := by
  by_cases h1 : ε' < 1
  swap
  · refine ⟨0, ?_⟩
    simp only [tailMass, Finset.range_zero, Finset.sum_empty, sub_zero]
    exact not_lt.mp h1
  · have hlt : ENNReal.ofReal (1 - ε') < ∑' i, μ.toMeasure (cell P r i) := by
      rw [tsum_measure_cell P μ hr]
      exact ENNReal.ofReal_lt_one.mpr (by linarith)
    rw [ENNReal.tsum_eq_iSup_sum] at hlt
    obtain ⟨s, hs⟩ := lt_iSup_iff.mp hlt
    obtain ⟨N, hsN⟩ := s.exists_nat_subset_range
    refine ⟨N, ?_⟩
    have hlt' : ENNReal.ofReal (1 - ε') < ∑ i ∈ Finset.range N, μ.toMeasure (cell P r i) :=
      lt_of_lt_of_le hs (Finset.sum_le_sum_of_subset hsN)
    have hne : (∑ i ∈ Finset.range N, μ.toMeasure (cell P r i)) ≠ ⊤ := by
      rw [← measure_biUnion_range_cell]
      exact measure_ne_top _ _
    have hsum : (∑ i ∈ Finset.range N, μ.toMeasure (cell P r i)).toReal
        = ∑ i ∈ Finset.range N, cellMass P μ r i := by
      rw [ENNReal.toReal_sum fun i _ => measure_ne_top _ _]
      exact Finset.sum_congr rfl fun i _ => rfl
    have hreal : 1 - ε' < ∑ i ∈ Finset.range N, cellMass P μ r i := by
      have := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hne).mpr hlt'
      rwa [ENNReal.toReal_ofReal (by linarith), hsum] at this
    rw [tailMass]
    linarith

/-- Dense-point index of the `i`-th truncation atom (the remainder atom is `0`). -/
private def truncIdx (N i : ℕ) : ℕ := if i < N then i else 0

/-- Weight of the `i`-th truncation atom. -/
private noncomputable def truncWt (μ : ProbabilityMeasure X) (r : ℝ) (N i : ℕ) : ℝ :=
  if i < N then cellMass P μ r i else tailMass P μ r N

private theorem truncWt_nonneg (μ : ProbabilityMeasure X) (r : ℝ) (N i : ℕ) :
    0 ≤ truncWt P μ r N i := by
  rw [truncWt]
  split_ifs
  · exact cellMass_nonneg P μ r i
  · exact tailMass_nonneg P μ r N

omit [BorelSpace X] in
private theorem truncWt_le_one (μ : ProbabilityMeasure X) (r : ℝ) (N i : ℕ) :
    truncWt P μ r N i ≤ 1 := by
  rw [truncWt]
  split_ifs
  · exact cellMass_le_one P μ r i
  · exact tailMass_le_one P μ r N

omit [BorelSpace X] in
private theorem sum_truncWt (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    ∑ i : Fin (N + 1), truncWt P μ r N (i : ℕ) = 1 := by
  rw [← Finset.sum_range fun i => truncWt P μ r N i, Finset.sum_range_succ]
  have h1 : ∑ i ∈ Finset.range N, truncWt P μ r N i
      = ∑ i ∈ Finset.range N, cellMass P μ r i :=
    Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
  rw [h1, truncWt, if_neg (lt_irrefl N), tailMass]
  ring

/-- The level-`(r, N)` truncated discretization of `μ`: cell masses at their dense
atoms, remainder at atom `0` — directly a weighted Dirac sum. -/
private noncomputable def truncMeasure (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    ProbabilityMeasure X :=
  ⟨∑ i : Fin (N + 1),
      ENNReal.ofReal (truncWt P μ r N (i : ℕ)) • Measure.dirac (P.dense (truncIdx N i)),
    isProbabilityMeasure_sum_smul_dirac _ (fun i => truncWt_nonneg P μ r N i)
      (sum_truncWt P μ r N)⟩

private theorem toMeasure_truncMeasure (μ : ProbabilityMeasure X) (r : ℝ) (N : ℕ) :
    (truncMeasure P μ r N).toMeasure
      = ∑ i : Fin (N + 1),
          ENNReal.ofReal (truncWt P μ r N (i : ℕ))
            • Measure.dirac (P.dense (truncIdx N i)) := rfl

/-- **The truncated discretization estimate**:
`levyProkhorovDist μ (trunc μ r N) ≤ r + tailMass`.  Mass moved within a cell to its
atom stays inside every `ε`-thickening with `ε > r`; the untruncated remainder costs at
most the tail mass; the reverse bound is free for probability measures. -/
private theorem levyProkhorovDist_trunc_le (μ : ProbabilityMeasure X) {r : ℝ}
    (hr : 0 < r) (N : ℕ) :
    levyProkhorovDist μ.toMeasure (truncMeasure P μ r N).toMeasure
      ≤ r + tailMass P μ r N := by
  refine levyProkhorovDist_le_of_forall_le _ _
    (add_nonneg hr.le (tailMass_nonneg P μ r N)) fun ε B hε hB => ?_
  have hrε : r < ε := lt_of_le_of_lt (le_add_of_nonneg_right (tailMass_nonneg P μ r N)) hε
  have htailε : tailMass P μ r N ≤ ε :=
    le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_left hr.le) hε)
  set U : Set X := ⋃ i ∈ Finset.range N, cell P r i with hU_def
  have hUm : MeasurableSet U :=
    (Finset.range N).measurableSet_biUnion fun i _ => measurableSet_cell P r i
  -- split the mass of `B` along the first `N` cells and the remainder
  have hsplit : μ.toMeasure B
      ≤ ∑ i ∈ Finset.range N, μ.toMeasure (B ∩ cell P r i) + μ.toMeasure Uᶜ := by
    calc μ.toMeasure B
        ≤ μ.toMeasure ((⋃ i ∈ Finset.range N, B ∩ cell P r i) ∪ (B ∩ Uᶜ)) := by
          refine measure_mono fun z hz => ?_
          by_cases hzU : z ∈ U
          · obtain ⟨i, hi, hzc⟩ := Set.mem_iUnion₂.mp hzU
            exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, hi, hz, hzc⟩)
          · exact Or.inr ⟨hz, hzU⟩
      _ ≤ μ.toMeasure (⋃ i ∈ Finset.range N, B ∩ cell P r i) + μ.toMeasure (B ∩ Uᶜ) :=
          measure_union_le _ _
      _ ≤ ∑ i ∈ Finset.range N, μ.toMeasure (B ∩ cell P r i) + μ.toMeasure Uᶜ :=
          add_le_add (measure_biUnion_finset_le _ _)
            (measure_mono Set.inter_subset_right)
  -- the remainder is the tail mass
  have hcompl : μ.toMeasure Uᶜ = ENNReal.ofReal (tailMass P μ r N) := by
    have hofReal : ENNReal.ofReal (∑ i ∈ Finset.range N, cellMass P μ r i)
        = μ.toMeasure U := by
      rw [sum_range_cellMass_eq, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [prob_compl_eq_one_sub hUm, tailMass,
      ENNReal.ofReal_sub _ (Finset.sum_nonneg fun i _ => cellMass_nonneg P μ r i),
      ENNReal.ofReal_one, hofReal]
  -- each cell piece is dominated by its atom's contribution to the thickening
  have hcell : ∀ i ∈ Finset.range N, μ.toMeasure (B ∩ cell P r i)
      ≤ (ENNReal.ofReal (cellMass P μ r i) • Measure.dirac (P.dense i))
          (thickening ε B) := by
    intro i _
    rcases Set.eq_empty_or_nonempty (B ∩ cell P r i) with hemp | ⟨b, hbB, hbc⟩
    · rw [hemp]
      simp
    · have hpt : P.dense i ∈ thickening ε B := by
        refine Metric.mem_thickening_iff.mpr ⟨b, hbB, ?_⟩
        rw [dist_comm]
        exact lt_of_le_of_lt hbc.1 hrε
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem hpt, mul_one]
      calc μ.toMeasure (B ∩ cell P r i)
          ≤ μ.toMeasure (cell P r i) := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal (cellMass P μ r i) :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  -- the atom contributions are dominated by the truncated measure
  have hν : ∑ i ∈ Finset.range N,
      (ENNReal.ofReal (cellMass P μ r i) • Measure.dirac (P.dense i)) (thickening ε B)
        ≤ (truncMeasure P μ r N).toMeasure (thickening ε B) := by
    calc ∑ i ∈ Finset.range N,
        (ENNReal.ofReal (cellMass P μ r i) • Measure.dirac (P.dense i)) (thickening ε B)
        = ∑ i ∈ Finset.range N,
            (ENNReal.ofReal (truncWt P μ r N i)
              • Measure.dirac (P.dense (truncIdx N i))) (thickening ε B) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp only [truncWt, truncIdx, if_pos (Finset.mem_range.mp hi)]
      _ ≤ ∑ i ∈ Finset.range (N + 1),
            (ENNReal.ofReal (truncWt P μ r N i)
              • Measure.dirac (P.dense (truncIdx N i))) (thickening ε B) := by
          rw [Finset.sum_range_succ]
          exact le_self_add
      _ = (truncMeasure P μ r N).toMeasure (thickening ε B) := by
          rw [toMeasure_truncMeasure, Measure.finsetSum_apply,
            ← Finset.sum_range fun i =>
              (ENNReal.ofReal (truncWt P μ r N i)
                • Measure.dirac (P.dense (truncIdx N i))) (thickening ε B)]
  calc μ.toMeasure B
      ≤ ∑ i ∈ Finset.range N, μ.toMeasure (B ∩ cell P r i) + μ.toMeasure Uᶜ := hsplit
    _ ≤ (truncMeasure P μ r N).toMeasure (thickening ε B)
        + ENNReal.ofReal (tailMass P μ r N) :=
        add_le_add ((Finset.sum_le_sum hcell).trans hν) (le_of_eq hcompl)
    _ ≤ (truncMeasure P μ r N).toMeasure (thickening ε B) + ENNReal.ofReal ε :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal htailε)

/-! #### Evaluation of finite atomic measures -/

omit [MetricSpace X] [BorelSpace X] in
/-- Evaluating a finite atomic measure on a measurable set: indicator sums. -/
private theorem sum_smul_dirac_apply {k : ℕ} (a : Fin k → ℝ) (x : Fin k → X) {A : Set X}
    (hA : MeasurableSet A) :
    (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) A
      = ∑ i, A.indicator (fun _ => ENNReal.ofReal (a i)) (x i) := by
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  by_cases hi : x i ∈ A
  · simp [Set.indicator_of_mem hi]
  · simp [Set.indicator_of_notMem hi]

end Atomics

/-! ### Rational approximation of unit-interval reals -/

/-- Clamping is 1-Lipschitz. -/
private theorem abs_clamp_sub_clamp_le (p q : ℝ) :
    |max 0 (min 1 p) - max 0 (min 1 q)| ≤ |p - q| := by
  have h2 : |min 1 p - min 1 q| ≤ |p - q| := by
    refine (abs_min_sub_min_le_max 1 p 1 q).trans ?_
    rw [sub_self, abs_zero]
    exact max_le (abs_nonneg _) le_rfl
  refine (abs_max_sub_max_le_max 0 (min 1 p) 0 (min 1 q)).trans ?_
  rw [sub_self, abs_zero]
  exact max_le (abs_nonneg _) h2

/-- Every `[0,1]` real is within `η` of a `[0,1]` rational. -/
private theorem exists_rat_close {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {η : ℝ}
    (hη : 0 < η) : ∃ q : ℚ, 0 ≤ q ∧ q ≤ 1 ∧ |(q : ℝ) - c| ≤ η := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c - η < c by linarith)
  refine ⟨max 0 (min 1 q), le_max_left _ _, max_le zero_le_one (min_le_left _ _), ?_⟩
  have hcast : ((max 0 (min 1 q) : ℚ) : ℝ) = max 0 (min 1 (q : ℝ)) := by push_cast; rfl
  have hc : max 0 (min 1 c) = c := by rw [min_eq_right hc1, max_eq_right hc0]
  calc |((max 0 (min 1 q) : ℚ) : ℝ) - c|
      = |max 0 (min 1 (q : ℝ)) - max 0 (min 1 c)| := by rw [hcast, hc]
    _ ≤ |(q : ℝ) - c| := abs_clamp_sub_clamp_le _ _
    _ ≤ η := by
        rw [abs_le]
        constructor <;> linarith

section Density

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

/-- **Generic Lévy–Prokhorov density of the atomic sequence**: every Borel probability
measure on a presented metric space is within any `ε > 0` of some decoded atomic index,
in the Lévy–Prokhorov distance.  Route: truncated cell discretization +
rational-weight perturbation. -/
theorem exists_atomic_close (μ : ProbabilityMeasure X) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, levyProkhorovDist μ.toMeasure (atomic P m).toMeasure < ε := by
  classical
  have hmin0 : 0 < min ε 1 := lt_min hε one_pos
  set r : ℝ := min ε 1 / 8 with hr_def
  have hr : 0 < r := by positivity
  obtain ⟨N, hN⟩ := exists_tailMass_le P μ hr (ε' := min ε 1 / 8) (by positivity)
  set K : ℕ := N + 1 with hK_def
  -- the perturbation budget
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  have hden : (0 : ℝ) < 4 * ((K : ℝ) + 1) := by positivity
  set η : ℝ := min ε 1 / (4 * ((K : ℝ) + 1)) with hη_def
  have hη : 0 < η := div_pos hmin0 hden
  have hKη14 : (K : ℝ) * η ≤ 1 / 4 := by
    rw [hη_def, ← mul_div_assoc, div_le_iff₀ hden]
    have h1 : (K : ℝ) * min ε 1 ≤ (K : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (min_le_right ε 1) hK0
    nlinarith
  have hKηε : (K : ℝ) * η ≤ ε / 4 := by
    rw [hη_def, ← mul_div_assoc, div_le_iff₀ hden]
    have h1 : (K : ℝ) * min ε 1 ≤ (K : ℝ) * ε :=
      mul_le_mul_of_nonneg_left (min_le_left ε 1) hK0
    nlinarith
  -- rational approximations of the truncation weights
  choose q hq0 hq1 hqd using fun i : Fin K =>
    exists_rat_close (truncWt_nonneg P μ r N (i : ℕ)) (truncWt_le_one P μ r N (i : ℕ)) hη
  have hcsum : ∑ i : Fin K, truncWt P μ r N (i : ℕ) = 1 := sum_truncWt P μ r N
  have hcast : ((∑ i, q i : ℚ) : ℝ) = ∑ i, (q i : ℝ) := by push_cast; rfl
  have hΔ : ∑ i, |(q i : ℝ) - truncWt P μ r N (i : ℕ)| ≤ (K : ℝ) * η := by
    calc ∑ i, |(q i : ℝ) - truncWt P μ r N (i : ℕ)|
        ≤ ∑ _i : Fin K, η := Finset.sum_le_sum fun i _ => hqd i
      _ = (K : ℝ) * η := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hS1 : |((∑ i, q i : ℚ) : ℝ) - 1|
      ≤ ∑ i, |(q i : ℝ) - truncWt P μ r N (i : ℕ)| := by
    have h1 : ((∑ i, q i : ℚ) : ℝ) - 1
        = ∑ i, ((q i : ℝ) - truncWt P μ r N (i : ℕ)) := by
      rw [hcast, Finset.sum_sub_distrib, hcsum]
    rw [h1]
    exact Finset.abs_sum_le_sum_abs _ _
  have hS34 : (3 / 4 : ℝ) ≤ ((∑ i, q i : ℚ) : ℝ) := by
    have h := abs_le.mp (hS1.trans (hΔ.trans hKη14))
    linarith [h.1]
  have hSR : (0 : ℝ) < ((∑ i, q i : ℚ) : ℝ) := lt_of_lt_of_le (by norm_num) hS34
  have hSQ : (0 : ℚ) < ∑ j, q j := by exact_mod_cast hSR
  have hSne : (∑ i, q i : ℚ) ≠ 0 := hSQ.ne'
  -- the atomic index: encode the list of (dense-index, weight-code) pairs
  set l : List (ℕ × ℕ) :=
    List.ofFn (fun i : Fin K =>
      (truncIdx N (i : ℕ), (ratOfCode_surjective (q i)).choose)) with hl_def
  have hlen : l.length = K := List.length_ofFn
  have hget : ∀ j : Fin l.length,
      l[j] = (truncIdx N ((Fin.cast hlen j : Fin K) : ℕ),
        (ratOfCode_surjective (q (Fin.cast hlen j))).choose) := fun j =>
    List.getElem_ofFn j.isLt
  have hclampedWeight : ∀ i : Fin K, clampedWeight ((ratOfCode_surjective (q i)).choose) = q i := by
    intro i
    rw [clampedWeight, (ratOfCode_surjective (q i)).choose_spec,
      min_eq_right (hq1 i), max_eq_right (hq0 i)]
  have hwS : clampedWeightSum l = ∑ i, q i := by
    rw [clampedWeightSum, listSum_map_eq_finSum,
      ← Fin.sum_congr' (fun i : Fin K => q i) hlen]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hget j]
    exact hclampedWeight _
  have hS0' : clampedWeightSum l ≠ 0 := by
    rw [hwS]
    exact hSne
  have hQ : (atomic P (Encodable.encode l)).toMeasure
      = ∑ i : Fin K,
          ENNReal.ofReal ((q i / ∑ j, q j : ℚ) : ℝ)
            • Measure.dirac (P.dense (truncIdx N (i : ℕ))) := by
    rw [atomic_encode_eq_atomicOfList, toMeasure_atomicOfList_of_ne_zero P hS0',
      ← Fin.sum_congr' (fun i : Fin K =>
        ENNReal.ofReal ((q i / ∑ j, q j : ℚ) : ℝ)
          • Measure.dirac (P.dense (truncIdx N (i : ℕ)))) hlen]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hget j]
    simp only [hwS, hclampedWeight]
  -- the weight-difference estimate
  have hq0R : ∀ i, (0 : ℝ) ≤ (q i : ℝ) := fun i => by exact_mod_cast hq0 i
  have hterm : ∀ i : Fin K,
      |truncWt P μ r N (i : ℕ) - ((q i / ∑ j, q j : ℚ) : ℝ)|
        ≤ |(q i : ℝ) - truncWt P μ r N (i : ℕ)|
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
    calc |truncWt P μ r N (i : ℕ) - ((q i / ∑ j, q j : ℚ) : ℝ)|
        ≤ |truncWt P μ r N (i : ℕ) - (q i : ℝ)|
            + |(q i : ℝ) - ((q i / ∑ j, q j : ℚ) : ℝ)| := abs_sub_le _ _ _
      _ = |(q i : ℝ) - truncWt P μ r N (i : ℕ)|
            + (q i : ℝ) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ)) := by
          rw [abs_sub_comm, h2]
  have hsum_le : ∑ i : Fin K, |truncWt P μ r N (i : ℕ) - ((q i / ∑ j, q j : ℚ) : ℝ)|
      ≤ 2 * ((K : ℝ) * η) := by
    have habs : |((∑ j, q j : ℚ) : ℝ) - 1| ≤ (K : ℝ) * η := hS1.trans hΔ
    calc ∑ i : Fin K, |truncWt P μ r N (i : ℕ) - ((q i / ∑ j, q j : ℚ) : ℝ)|
        ≤ ∑ i, (|(q i : ℝ) - truncWt P μ r N (i : ℕ)|
            + (q i : ℝ) * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ))) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = (∑ i, |(q i : ℝ) - truncWt P μ r N (i : ℕ)|)
            + (∑ i, (q i : ℝ))
              * (|((∑ j, q j : ℚ) : ℝ) - 1| / ((∑ j, q j : ℚ) : ℝ)) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      _ = (∑ i, |(q i : ℝ) - truncWt P μ r N (i : ℕ)|)
            + |((∑ j, q j : ℚ) : ℝ) - 1| := by
          rw [← hcast, ← mul_div_assoc, mul_div_cancel_left₀ _ hSR.ne']
      _ ≤ (K : ℝ) * η + (K : ℝ) * η := add_le_add hΔ habs
      _ = 2 * ((K : ℝ) * η) := by ring
  -- assembly
  refine ⟨Encodable.encode l, ?_⟩
  have hd1 : levyProkhorovDist μ.toMeasure (truncMeasure P μ r N).toMeasure
      ≤ r + tailMass P μ r N := levyProkhorovDist_trunc_le P μ hr N
  have hd2 : levyProkhorovDist (truncMeasure P μ r N).toMeasure
        (atomic P (Encodable.encode l)).toMeasure
      ≤ ∑ i : Fin K, |truncWt P μ r N (i : ℕ) - ((q i / ∑ j, q j : ℚ) : ℝ)| :=
    levyProkhorovDist_le_sum_abs (fun i : Fin K => P.dense (truncIdx N (i : ℕ)))
      (fun i => truncWt P μ r N (i : ℕ)) (fun i => ((q i / ∑ j, q j : ℚ) : ℝ))
      (fun i => by exact_mod_cast div_nonneg (hq0 i) hSQ.le)
      _ _ (toMeasure_truncMeasure P μ r N) hQ
  have hminε : min ε 1 ≤ ε := min_le_left _ _
  calc levyProkhorovDist μ.toMeasure (atomic P (Encodable.encode l)).toMeasure
      ≤ levyProkhorovDist μ.toMeasure (truncMeasure P μ r N).toMeasure
        + levyProkhorovDist (truncMeasure P μ r N).toMeasure
            (atomic P (Encodable.encode l)).toMeasure := levyProkhorovDist_triangle _ _ _
    _ ≤ (r + tailMass P μ r N) + 2 * ((K : ℝ) * η) :=
        add_le_add hd1 (hd2.trans hsum_le)
    _ < ε := by
        rw [hr_def]
        linarith [hN, hKηε, hminε, hε]

/-- Density of the decoded atomics in the LP metric — the `denseRange` field of the
Prokhorov presentation. -/
private theorem denseRange_atomic :
    DenseRange fun m =>
      (LevyProkhorov.ofMeasure (atomic P m) : LevyProkhorov (ProbabilityMeasure X)) := by
  rw [Metric.denseRange_iff]
  intro ν s hs
  obtain ⟨m, hm⟩ := exists_atomic_close P ν.toMeasure hs
  refine ⟨m, ?_⟩
  calc dist ν (LevyProkhorov.ofMeasure (atomic P m))
      = levyProkhorovDist ν.toMeasure.toMeasure (atomic P m).toMeasure :=
        LevyProkhorov.dist_probabilityMeasure_def _ _
    _ < s := hm

end Density

/-! ### The weak measure representation, directly on the carrier

At this mathlib pin `LevyProkhorov` is a one-field structure, not a definitional type
synonym, so `Representation (LevyProkhorov (ProbabilityMeasure X))` is *not* defeq to
`Representation (ProbabilityMeasure X)`.  The weak representation is therefore stated
directly on the carrier through the names predicate `WeakMeasureNames`; the private
bridge lemmas below identify its names with the `cauchyRep` names of any presentation
of the synonym whose dense sequence is `ofMeasure ∘ atomic P`.  Downstream code never
touches the synonym. -/

section WeakRep

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

/-- `p` weak-names `μ`: the decoded atomic measures approximate `μ` at the pinned rate
`((2:ℝ)⁻¹)^n` in Lévy–Prokhorov distance. -/
def WeakMeasureNames (p : Baire) (μ : ProbabilityMeasure X) : Prop :=
  ∀ n : ℕ, levyProkhorovDist μ.toMeasure (atomic P (p n)).toMeasure ≤ ((2 : ℝ)⁻¹) ^ n

/-- A weak name determines its measure: LP distance zero forces equality through the
metric-space instance on the `LevyProkhorov` synonym. -/
private theorem weakMeasureNames_unique {p : Baire} {μ ν : ProbabilityMeasure X}
    (hμ : WeakMeasureNames P p μ) (hν : WeakMeasureNames P p ν) : μ = ν := by
  have hbound : ∀ n : ℕ,
      levyProkhorovDist μ.toMeasure ν.toMeasure ≤ 2 * ((2 : ℝ)⁻¹) ^ n := fun n =>
    calc levyProkhorovDist μ.toMeasure ν.toMeasure
        ≤ levyProkhorovDist μ.toMeasure (atomic P (p n)).toMeasure
          + levyProkhorovDist (atomic P (p n)).toMeasure ν.toMeasure :=
          levyProkhorovDist_triangle _ _ _
      _ ≤ ((2 : ℝ)⁻¹) ^ n + ((2 : ℝ)⁻¹) ^ n := by
          refine add_le_add (hμ n) ?_
          rw [levyProkhorovDist_comm]
          exact hν n
      _ = 2 * ((2 : ℝ)⁻¹) ^ n := by ring
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * ((2 : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num :
      ((2 : ℝ)⁻¹) < 1)).const_mul 2
  have hle : levyProkhorovDist μ.toMeasure ν.toMeasure ≤ 0 := ge_of_tendsto' hlim hbound
  have h0 : levyProkhorovDist μ.toMeasure ν.toMeasure = 0 :=
    le_antisymm hle ENNReal.toReal_nonneg
  have hdist : dist (LevyProkhorov.ofMeasure μ : LevyProkhorov (ProbabilityMeasure X))
      (LevyProkhorov.ofMeasure ν) = 0 := by
    rw [LevyProkhorov.dist_probabilityMeasure_def]
    exact h0
  have heq := eq_of_dist_eq_zero hdist
  exact congrArg LevyProkhorov.toMeasure heq

/-- **The weak measure representation**: the fast Cauchy representation at the pinned
rate against the decoded atomic dense sequence in Lévy–Prokhorov distance, stated
directly on the carrier `ProbabilityMeasure X`. -/
noncomputable def weakMeasureRep : Representation (ProbabilityMeasure X) where
  rep p := ⟨∃ μ, WeakMeasureNames P p μ, fun h => h.choose⟩
  onto μ := by
    classical
    have h : ∀ n : ℕ, ∃ m,
        levyProkhorovDist μ.toMeasure (atomic P m).toMeasure ≤ ((2 : ℝ)⁻¹) ^ n := fun n => by
      obtain ⟨m, hm⟩ := exists_atomic_close P μ
        (ε := ((2 : ℝ)⁻¹) ^ n) (by positivity)
      exact ⟨m, hm.le⟩
    have hname : WeakMeasureNames P (fun n => (h n).choose) μ := fun n => (h n).choose_spec
    exact ⟨fun n => (h n).choose, ⟨μ, hname⟩,
      weakMeasureNames_unique P (Exists.choose_spec _) hname⟩

/-- Names of `weakMeasureRep` are exactly `WeakMeasureNames` — the frozen names
characterization; downstream code never touches the `LevyProkhorov` synonym. -/
@[simp]
theorem weakMeasureRep_names_iff {p : Baire} {μ : ProbabilityMeasure X} :
    (weakMeasureRep P).Names p μ ↔ WeakMeasureNames P p μ := by
  constructor
  · rintro ⟨hex, rfl⟩
    exact hex.choose_spec
  · intro h
    exact ⟨⟨μ, h⟩, weakMeasureNames_unique P (Exists.choose_spec _) h⟩

/-- (Quarantined bridge.) Weak names are exactly `cauchyRep`-style `NamesPoint` on the
synonym, for any presentation whose dense sequence is `ofMeasure ∘ atomic P`. -/
private theorem weakMeasureNames_iff_namesPoint
    (P' : ComputableMetricPresentation (LevyProkhorov (ProbabilityMeasure X)))
    (hd : ∀ m, P'.dense m = LevyProkhorov.ofMeasure (atomic P m))
    {p : Baire} {μ : ProbabilityMeasure X} :
    WeakMeasureNames P p μ ↔ P'.NamesPoint p (LevyProkhorov.ofMeasure μ) := by
  unfold WeakMeasureNames ComputableMetricPresentation.NamesPoint
  refine forall_congr' fun n => ?_
  rw [hd, LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist_comm]

/-- (Quarantined bridge.) The names-level identification of `weakMeasureRep P` with the
fast Cauchy representation of any Prokhorov-type presentation of the synonym. -/
private theorem weakMeasureRep_names_iff_cauchyRep
    (P' : ComputableMetricPresentation (LevyProkhorov (ProbabilityMeasure X)))
    (hd : ∀ m, P'.dense m = LevyProkhorov.ofMeasure (atomic P m))
    {p : Baire} {μ : ProbabilityMeasure X} :
    (weakMeasureRep P).Names p μ ↔ P'.cauchyRep.Names p (LevyProkhorov.ofMeasure μ) := by
  rw [weakMeasureRep_names_iff, P'.cauchyRep_names_iff,
    weakMeasureNames_iff_namesPoint P P' hd]

end WeakRep

/-! ### The finite reduction of LP-distance comparisons

Atom distances `dist (P.dense i) (P.dense j)` are only semidecidably comparable, so two
Σ₁ forms with r.e.-shaped atoms result: `dist < t` via `strictFinCond` (strict `<`
comparisons only, matching `ltSemidec`) with an `∃ δ' : ℚ` search, and `t < dist` via a
finite violation certificate with strict `>` comparisons only (matching `gtSemidec`).
The non-strict `finCond` characterization is the bridge used to prove the certificate
form. -/

section FiniteCharacterization

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

open Classical in
/-- The one-sided finite Prokhorov condition at threshold `δ` (non-strict distances). -/
private def finCond {k l : ℕ} (x : Fin k → X) (y : Fin l → X)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (δ : ℝ) : Prop :=
  ∀ T : Finset (Fin k),
    ∑ i ∈ T, a i
      ≤ (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ, b j) + δ

open Classical in
/-- The STRICT one-sided finite Prokhorov condition: only strict atom-distance
comparisons appear — the semidecidable-generic replacement for `finCond`. -/
private def strictFinCond {k l : ℕ} (x : Fin k → X) (y : Fin l → X)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (δ : ℝ) : Prop :=
  ∀ T : Finset (Fin k),
    ∑ i ∈ T, a i
      ≤ (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < δ, b j) + δ

omit [MetricSpace X] [BorelSpace X] in
/-- Filter form of the atomic evaluation. -/
private theorem sum_smul_dirac_apply_filter {k : ℕ} (a : Fin k → ℝ) (x : Fin k → X)
    {A : Set X} (hA : MeasurableSet A) [DecidablePred fun i => x i ∈ A] :
    (∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i)) A
      = ∑ i ∈ Finset.univ.filter fun i => x i ∈ A, ENNReal.ofReal (a i) := by
  rw [sum_smul_dirac_apply a x hA, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : x i ∈ A
  · rw [Set.indicator_of_mem hi, if_pos hi]
  · rw [Set.indicator_of_notMem hi, if_neg hi]

/-- **Soundness of the non-strict finite condition** (one direction suffices for
probability measures). -/
private theorem levyProkhorovDist_le_of_finCond {k l : ℕ} (x : Fin k → X) (y : Fin l → X)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {δ : ℝ} (hδ : 0 ≤ δ) (h : finCond x y a b δ) :
    levyProkhorovDist Pμ.toMeasure Qμ.toMeasure ≤ δ := by
  classical
  refine levyProkhorovDist_le_of_forall_le _ _ hδ fun ε B hε hB => ?_
  set T : Finset (Fin k) := Finset.univ.filter fun i => x i ∈ B with hT
  have hPB : Pμ.toMeasure B = ∑ i ∈ T, ENNReal.ofReal (a i) := by
    rw [hP, sum_smul_dirac_apply_filter a x hB]
  have hsubthick : ∀ j : Fin l, (∃ i ∈ T, dist (y j) (x i) ≤ δ) →
      y j ∈ thickening ε B := by
    rintro j ⟨i, hiT, hd⟩
    have hxB : x i ∈ B := (Finset.mem_filter.mp hiT).2
    exact Metric.mem_thickening_iff.mpr ⟨x i, hxB, lt_of_le_of_lt hd hε⟩
  have hQthick : ∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ,
      ENNReal.ofReal (b j) ≤ Qμ.toMeasure (thickening ε B) := by
    rw [hQ, sum_smul_dirac_apply_filter b y isOpen_thickening.measurableSet]
    refine Finset.sum_le_sum_of_subset fun j hj => ?_
    obtain ⟨-, hex⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsubthick j hex⟩
  calc Pμ.toMeasure B = ∑ i ∈ T, ENNReal.ofReal (a i) := hPB
    _ = ENNReal.ofReal (∑ i ∈ T, a i) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => ha i).symm
    _ ≤ ENNReal.ofReal
        ((∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ, b j) + δ) :=
        ENNReal.ofReal_le_ofReal (h T)
    _ ≤ ENNReal.ofReal
          (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ, b j)
        + ENNReal.ofReal δ := ENNReal.ofReal_add_le
    _ = (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ,
          ENNReal.ofReal (b j)) + ENNReal.ofReal δ := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hb j]
    _ ≤ Qμ.toMeasure (thickening ε B) + ENNReal.ofReal ε :=
        add_le_add hQthick (ENNReal.ofReal_le_ofReal hε.le)

/-- **Soundness of the strict finite condition**: identical to the non-strict case
(strict comparisons are stronger). -/
private theorem levyProkhorovDist_le_of_strictFinCond {k l : ℕ} (x : Fin k → X)
    (y : Fin l → X) (a : Fin k → ℝ) (b : Fin l → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ j, 0 ≤ b j) (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {δ : ℝ} (hδ : 0 ≤ δ) (h : strictFinCond x y a b δ) :
    levyProkhorovDist Pμ.toMeasure Qμ.toMeasure ≤ δ := by
  classical
  refine levyProkhorovDist_le_of_finCond x y a b ha hb Pμ Qμ hP hQ hδ fun T => ?_
  refine (h T).trans (add_le_add ?_ le_rfl)
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hb j
  obtain ⟨-, i, hiT, hd⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hiT, hd.le⟩

/-- **Completeness of the non-strict finite condition** (breakpoint collapse). -/
private theorem finCond_of_levyProkhorovDist_le {k l : ℕ} (x : Fin k → X)
    (y : Fin l → X) (a : Fin k → ℝ) (b : Fin l → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ j, 0 ≤ b j) (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {δ : ℝ} (hδ : 0 ≤ δ) (h : levyProkhorovDist Pμ.toMeasure Qμ.toMeasure ≤ δ) :
    finCond x y a b δ := by
  classical
  intro T
  set A : Set X := ↑(T.image x) with hA_def
  have hA : MeasurableSet A := (T.image x).finite_toSet.isClosed.measurableSet
  have hmemA : ∀ z, z ∈ A ↔ ∃ i ∈ T, x i = z := by
    intro z
    rw [hA_def, Finset.mem_coe, Finset.mem_image]
  have hthick_mem : ∀ (ε : ℝ) (j : Fin l),
      y j ∈ thickening ε A ↔ ∃ i ∈ T, dist (y j) (x i) < ε := by
    intro ε j
    rw [Metric.mem_thickening_iff]
    constructor
    · rintro ⟨z, hzA, hz⟩
      obtain ⟨i, hiT, rfl⟩ := (hmemA z).mp hzA
      exact ⟨i, hiT, hz⟩
    · rintro ⟨i, hiT, hi⟩
      exact ⟨x i, (hmemA (x i)).mpr ⟨i, hiT, rfl⟩, hi⟩
  have hstep : ∀ {ε : ℝ}, δ < ε →
      ∑ i ∈ T, a i
        ≤ (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < ε, b j) + ε := by
    intro ε hε
    have hεpos : 0 < ε := lt_of_le_of_lt hδ hε
    have hedist : levyProkhorovEDist Pμ.toMeasure Qμ.toMeasure < ENNReal.ofReal ε := by
      refine (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr ?_
      exact lt_of_le_of_lt h hε
    have hmeas := left_measure_le_of_levyProkhorovEDist_lt hedist (B := A) hA
    rw [ENNReal.toReal_ofReal hεpos.le] at hmeas
    have hPA : ENNReal.ofReal (∑ i ∈ T, a i) ≤ Pμ.toMeasure A := by
      rw [hP, sum_smul_dirac_apply_filter a x hA,
        ENNReal.ofReal_sum_of_nonneg fun i _ => ha i]
      refine Finset.sum_le_sum_of_subset fun i hiT => ?_
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmemA (x i)).mpr ⟨i, hiT, rfl⟩⟩
    have hQth : Qμ.toMeasure (thickening ε A)
        = ENNReal.ofReal
            (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < ε, b j) := by
      rw [hQ, sum_smul_dirac_apply_filter b y isOpen_thickening.measurableSet,
        ENNReal.ofReal_sum_of_nonneg fun j _ => hb j]
      refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
      exact hthick_mem ε j
    have hchain : ENNReal.ofReal (∑ i ∈ T, a i)
        ≤ ENNReal.ofReal
            ((∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < ε, b j) + ε) := by
      refine (hPA.trans hmeas).trans ?_
      rw [hQth, ← ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => hb j) hεpos.le]
    have hrhs : 0 ≤ (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < ε, b j)
        + ε := add_nonneg (Finset.sum_nonneg fun j _ => hb j) hεpos.le
    exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hchain
  by_contra hcon
  push Not at hcon
  set γ : ℝ := (∑ i ∈ T, a i
    - ((∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ, b j) + δ)) / 2
    with hγ_def
  have hγ0 : 0 < γ := by
    rw [hγ_def]
    linarith [hcon]
  set D : Finset ℝ :=
    ((Finset.univ : Finset (Fin l × Fin k)).filter
      fun p => δ < dist (y p.1) (x p.2)).image fun p => dist (y p.1) (x p.2) with hD_def
  have hDgt : ∀ d ∈ D, δ < d := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
    exact (Finset.mem_filter.mp hp).2
  obtain ⟨ε, hδε, hεγ, hsub⟩ :
      ∃ ε : ℝ, δ < ε ∧ ε ≤ δ + γ ∧
        ∀ j : Fin l, (∃ i ∈ T, dist (y j) (x i) < ε) →
          ∃ i ∈ T, dist (y j) (x i) ≤ δ := by
    rcases D.eq_empty_or_nonempty with hD | hD
    · refine ⟨δ + γ, by linarith, le_rfl, ?_⟩
      rintro j ⟨i, hiT, -⟩
      refine ⟨i, hiT, ?_⟩
      by_contra hgt
      push Not at hgt
      have hmem : dist (y j) (x i) ∈ D := Finset.mem_image.mpr
        ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, rfl⟩
      rw [hD] at hmem
      exact absurd hmem (Finset.notMem_empty _)
    · have hδdmin : δ < D.min' hD := hDgt _ (D.min'_mem hD)
      refine ⟨min (δ + γ) ((δ + D.min' hD) / 2),
        lt_min (by linarith) (by linarith), min_le_left _ _, ?_⟩
      rintro j ⟨i, hiT, hlt⟩
      refine ⟨i, hiT, ?_⟩
      by_contra hgt
      push Not at hgt
      have hmem : dist (y j) (x i) ∈ D := Finset.mem_image.mpr
        ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, rfl⟩
      have hge : D.min' hD ≤ dist (y j) (x i) := D.min'_le _ hmem
      have hlt' := lt_of_lt_of_le hlt (min_le_right _ _)
      linarith
  have h1 := hstep hδε
  have h2 : ∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < ε, b j
      ≤ ∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ δ, b j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hb j
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hsub j (Finset.mem_filter.mp hj).2⟩
  linarith

/-- **The non-strict finite characterization** of the LP distance between finite atomic
probability measures. -/
private theorem levyProkhorovDist_le_iff_finCond {k l : ℕ} (x : Fin k → X)
    (y : Fin l → X) (a : Fin k → ℝ) (b : Fin l → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    levyProkhorovDist Pμ.toMeasure Qμ.toMeasure ≤ δ ↔
      finCond x y a b δ ∧ finCond y x b a δ := by
  constructor
  · intro h
    refine ⟨finCond_of_levyProkhorovDist_le x y a b ha hb Pμ Qμ hP hQ hδ h,
      finCond_of_levyProkhorovDist_le y x b a hb ha Qμ Pμ hQ hP hδ ?_⟩
    rwa [levyProkhorovDist_comm]
  · rintro ⟨h1, -⟩
    exact levyProkhorovDist_le_of_finCond x y a b ha hb Pμ Qμ hP hQ hδ h1

/-- **Completeness of the strict finite condition** — direct (no breakpoint collapse):
`thickening` is open, so a strict inequality `LP < δ` immediately evaluates through the
strict filter. -/
private theorem strictFinCond_of_levyProkhorovDist_lt {k l : ℕ} (x : Fin k → X)
    (y : Fin l → X) (a : Fin k → ℝ) (b : Fin l → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ j, 0 ≤ b j) (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {δ : ℝ} (h : levyProkhorovDist Pμ.toMeasure Qμ.toMeasure < δ) :
    strictFinCond x y a b δ := by
  classical
  intro T
  set A : Set X := ↑(T.image x) with hA_def
  have hA : MeasurableSet A := (T.image x).finite_toSet.isClosed.measurableSet
  have hmemA : ∀ z, z ∈ A ↔ ∃ i ∈ T, x i = z := by
    intro z
    rw [hA_def, Finset.mem_coe, Finset.mem_image]
  have hδ0 : 0 < δ := lt_of_le_of_lt ENNReal.toReal_nonneg h
  have hedist : levyProkhorovEDist Pμ.toMeasure Qμ.toMeasure < ENNReal.ofReal δ :=
    (ENNReal.lt_ofReal_iff_toReal_lt (levyProkhorovEDist_ne_top _ _)).mpr h
  have hmeas := left_measure_le_of_levyProkhorovEDist_lt hedist (B := A) hA
  rw [ENNReal.toReal_ofReal hδ0.le] at hmeas
  have hPA : ENNReal.ofReal (∑ i ∈ T, a i) ≤ Pμ.toMeasure A := by
    rw [hP, sum_smul_dirac_apply_filter a x hA,
      ENNReal.ofReal_sum_of_nonneg fun i _ => ha i]
    refine Finset.sum_le_sum_of_subset fun i hiT => ?_
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hmemA (x i)).mpr ⟨i, hiT, rfl⟩⟩
  have hQth : Qμ.toMeasure (thickening δ A)
      = ENNReal.ofReal
          (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < δ, b j) := by
    rw [hQ, sum_smul_dirac_apply_filter b y isOpen_thickening.measurableSet,
      ENNReal.ofReal_sum_of_nonneg fun j _ => hb j]
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ?_) fun _ _ => rfl
    rw [Metric.mem_thickening_iff]
    constructor
    · rintro ⟨z, hzA, hz⟩
      obtain ⟨i, hiT, rfl⟩ := (hmemA z).mp hzA
      exact ⟨i, hiT, hz⟩
    · rintro ⟨i, hiT, hi⟩
      exact ⟨x i, (hmemA (x i)).mpr ⟨i, hiT, rfl⟩, hi⟩
  have hchain : ENNReal.ofReal (∑ i ∈ T, a i)
      ≤ ENNReal.ofReal
          ((∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < δ, b j) + δ) := by
    refine (hPA.trans hmeas).trans ?_
    rw [hQth, ← ENNReal.ofReal_add (Finset.sum_nonneg fun j _ => hb j) hδ0.le]
  have hrhs : 0 ≤ (∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < δ, b j)
      + δ := add_nonneg (Finset.sum_nonneg fun j _ => hb j) hδ0.le
  exact (ENNReal.ofReal_le_ofReal_iff hrhs).mp hchain

/-- **The Σ₁ characterization of `dist < t`** (`ltSemidec` shape): a rational
`δ'`-search over BOTH strict finite conditions. -/
private theorem levyProkhorovDist_lt_iff_exists_rat_strict {k l : ℕ} (x : Fin k → X)
    (y : Fin l → X) (a : Fin k → ℝ) (b : Fin l → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j) (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {t : ℝ} :
    levyProkhorovDist Pμ.toMeasure Qμ.toMeasure < t ↔
      ∃ δ' : ℚ, 0 ≤ δ' ∧ (δ' : ℝ) < t
        ∧ strictFinCond x y a b (δ' : ℝ) ∧ strictFinCond y x b a (δ' : ℝ) := by
  constructor
  · intro h
    have h0 : (0 : ℝ) ≤ levyProkhorovDist Pμ.toMeasure Qμ.toMeasure :=
      ENNReal.toReal_nonneg
    obtain ⟨δ', h1, h2⟩ := exists_rat_btwn h
    refine ⟨δ', by exact_mod_cast le_trans h0 h1.le, h2, ?_, ?_⟩
    · exact strictFinCond_of_levyProkhorovDist_lt x y a b ha hb Pμ Qμ hP hQ h1
    · exact strictFinCond_of_levyProkhorovDist_lt y x b a hb ha Qμ Pμ hQ hP
        (by rwa [levyProkhorovDist_comm])
  · rintro ⟨δ', hδ'0, hδ't, hfc, -⟩
    have hδ'0R : (0 : ℝ) ≤ (δ' : ℝ) := by exact_mod_cast hδ'0
    exact lt_of_le_of_lt
      (levyProkhorovDist_le_of_strictFinCond x y a b ha hb Pμ Qμ hP hQ hδ'0R hfc) hδ't

omit [MeasurableSpace X] [BorelSpace X] in
/-- The strict finite condition in WITNESSED form: the r.e.-friendly `∃ S` shape whose
atoms are (i) decidable rational weight comparisons and (ii) strict atom-distance
comparisons — precisely the presentation's `ltSemidec` predicates. -/
private theorem strictFinCond_iff_witness {k l : ℕ} (x : Fin k → X) (y : Fin l → X)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (hb : ∀ j, 0 ≤ b j) (δ : ℝ) :
    strictFinCond x y a b δ ↔
      ∀ T : Finset (Fin k), ∃ S : Finset (Fin l),
        (∀ j ∈ S, ∃ i ∈ T, dist (y j) (x i) < δ)
          ∧ ∑ i ∈ T, a i ≤ (∑ j ∈ S, b j) + δ := by
  classical
  constructor
  · intro h T
    exact ⟨Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) < δ,
      fun j hj => (Finset.mem_filter.mp hj).2, h T⟩
  · intro h T
    obtain ⟨S, hS1, hS2⟩ := h T
    refine hS2.trans (add_le_add ?_ le_rfl)
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => ?_) fun j _ _ => hb j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS1 j hj⟩

/-- **The Σ₁ certificate characterization of `t < dist`** (`gtSemidec` shape): a finite
violation certificate whose atoms are (i) decidable rational weight comparisons and
(ii) strict `t < dist` comparisons — precisely the presentation's `gtSemidec`
predicates.  No `δ'`-search is needed. -/
private theorem lt_levyProkhorovDist_iff_cert {k l : ℕ} (x : Fin k → X) (y : Fin l → X)
    (a : Fin k → ℝ) (b : Fin l → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (Pμ Qμ : ProbabilityMeasure X)
    (hP : Pμ.toMeasure = ∑ i, ENNReal.ofReal (a i) • Measure.dirac (x i))
    (hQ : Qμ.toMeasure = ∑ j, ENNReal.ofReal (b j) • Measure.dirac (y j))
    {t : ℝ} :
    t < levyProkhorovDist Pμ.toMeasure Qμ.toMeasure ↔
      (∃ T : Finset (Fin k), ∃ S : Finset (Fin l),
        (∀ j, j ∉ S → ∀ i ∈ T, t < dist (y j) (x i))
          ∧ (∑ j ∈ S, b j) + t < ∑ i ∈ T, a i)
      ∨ (∃ T : Finset (Fin l), ∃ S : Finset (Fin k),
        (∀ j, j ∉ S → ∀ i ∈ T, t < dist (x j) (y i))
          ∧ (∑ j ∈ S, a j) + t < ∑ i ∈ T, b i) := by
  classical
  constructor
  · intro h
    by_cases ht : 0 ≤ t
    · have hnot : ¬ levyProkhorovDist Pμ.toMeasure Qμ.toMeasure ≤ t := not_le.mpr h
      have hnc : ¬ (finCond x y a b t ∧ finCond y x b a t) := fun hc =>
        absurd ((levyProkhorovDist_le_iff_finCond x y a b ha hb Pμ Qμ hP hQ ht).mpr hc)
          hnot
      rcases not_and_or.mp hnc with hnc1 | hnc2
      · left
        simp only [finCond] at hnc1
        push Not at hnc1
        obtain ⟨T, hT⟩ := hnc1
        refine ⟨T, Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ t,
          fun j hj i hiT => ?_, hT⟩
        by_contra hle
        push Not at hle
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hiT, hle⟩)
      · right
        simp only [finCond] at hnc2
        push Not at hnc2
        obtain ⟨T, hT⟩ := hnc2
        refine ⟨T, Finset.univ.filter fun j => ∃ i ∈ T, dist (x j) (y i) ≤ t,
          fun j hj i hiT => ?_, hT⟩
        by_contra hle
        push Not at hle
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, hiT, hle⟩)
    · left
      refine ⟨∅, ∅, fun j hj i hiT => absurd hiT (Finset.notMem_empty i), ?_⟩
      simp only [Finset.sum_empty, zero_add]
      exact not_le.mp ht
  · rintro (⟨T, S, hout, hlt⟩ | ⟨T, S, hout, hlt⟩)
    · by_contra hnot
      push Not at hnot
      have ht0 : 0 ≤ t := le_trans ENNReal.toReal_nonneg hnot
      have hfc := (levyProkhorovDist_le_iff_finCond x y a b ha hb Pμ Qμ hP hQ ht0).mp hnot
      have h1 := hfc.1 T
      have hsub : (Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ t) ⊆ S := by
        intro j hj
        by_contra hjS
        obtain ⟨i, hiT, hd⟩ := (Finset.mem_filter.mp hj).2
        exact absurd hd (not_le.mpr (hout j hjS i hiT))
      have h2 : ∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (y j) (x i) ≤ t, b j
          ≤ ∑ j ∈ S, b j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => hb j
      linarith
    · by_contra hnot
      push Not at hnot
      have ht0 : 0 ≤ t := le_trans ENNReal.toReal_nonneg hnot
      have hfc := (levyProkhorovDist_le_iff_finCond x y a b ha hb Pμ Qμ hP hQ ht0).mp hnot
      have h1 := hfc.2 T
      have hsub : (Finset.univ.filter fun j => ∃ i ∈ T, dist (x j) (y i) ≤ t) ⊆ S := by
        intro j hj
        by_contra hjS
        obtain ⟨i, hiT, hd⟩ := (Finset.mem_filter.mp hj).2
        exact absurd hd (not_le.mpr (hout j hjS i hiT))
      have h2 : ∑ j ∈ Finset.univ.filter fun j => ∃ i ∈ T, dist (x j) (y i) ≤ t, a j
          ≤ ∑ j ∈ S, a j :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ha j
      linarith

end FiniteCharacterization

/-! ### The Σ₁ characterizations at the atomic level -/

/-- The decoded list of an atomic index. -/
private def atomList (m : ℕ) : List (ℕ × ℕ) := ofNat (List (ℕ × ℕ)) m

/-- The decoded real weight vector of an atomic index. -/
private def atomWtR (m i : ℕ) : ℝ := ((atomWt (atomList m) i : ℚ) : ℝ)

private theorem atomWtR_nonneg (m i : ℕ) : 0 ≤ atomWtR m i := by
  rw [atomWtR]
  exact_mod_cast atomWt_nonneg (atomList m) i

section AtomicSigma

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)

/-- The decoded atom points of an atomic index: dense points of the presentation. -/
private noncomputable def atomPt (m i : ℕ) : X := P.dense (atomIdx (atomList m) i)

omit [BorelSpace X] in
private theorem toMeasure_atomic (m : ℕ) :
    (atomic P m).toMeasure
      = ∑ i : Fin (atomCount (atomList m)),
          ENNReal.ofReal (atomWtR m i) • Measure.dirac (atomPt P m i) := by
  rw [atomic]
  exact toMeasure_atomic_eq_sum P _

/-- **Σ₁ characterization of `dist (atomic m₁) (atomic m₂) < t`** on the LP synonym:
an `∃ δ' : ℚ` search over the two witnessed strict finite conditions. -/
private theorem dist_atomic_lt_iff (m₁ m₂ : ℕ) (t : ℝ) :
    dist (LevyProkhorov.ofMeasure (atomic P m₁) : LevyProkhorov (ProbabilityMeasure X))
        (LevyProkhorov.ofMeasure (atomic P m₂)) < t ↔
      ∃ δ' : ℚ, 0 ≤ δ' ∧ (δ' : ℝ) < t
        ∧ strictFinCond (fun i => atomPt P m₁ i) (fun j => atomPt P m₂ j)
            (fun i : Fin (atomCount (atomList m₁)) => atomWtR m₁ i)
            (fun j : Fin (atomCount (atomList m₂)) => atomWtR m₂ j) (δ' : ℝ)
        ∧ strictFinCond (fun j => atomPt P m₂ j) (fun i => atomPt P m₁ i)
            (fun j : Fin (atomCount (atomList m₂)) => atomWtR m₂ j)
            (fun i : Fin (atomCount (atomList m₁)) => atomWtR m₁ i) (δ' : ℝ) := by
  rw [LevyProkhorov.dist_probabilityMeasure_def]
  exact levyProkhorovDist_lt_iff_exists_rat_strict _ _ _ _
    (fun i => atomWtR_nonneg m₁ i) (fun j => atomWtR_nonneg m₂ j) _ _
    (toMeasure_atomic P m₁) (toMeasure_atomic P m₂)

/-- **Σ₁ certificate characterization of `t < dist (atomic m₁) (atomic m₂)`** on the LP
synonym: a finite certificate with decidable rational comparisons and strict
`t < dist (P.dense e₁) (P.dense e₂)` atoms — the `gtSemidec` shape, no rational
search. -/
private theorem lt_dist_atomic_iff (m₁ m₂ : ℕ) (t : ℝ) :
    t < dist (LevyProkhorov.ofMeasure (atomic P m₁) : LevyProkhorov (ProbabilityMeasure X))
        (LevyProkhorov.ofMeasure (atomic P m₂)) ↔
      (∃ T : Finset (Fin (atomCount (atomList m₁))),
       ∃ S : Finset (Fin (atomCount (atomList m₂))),
        (∀ j, j ∉ S → ∀ i ∈ T, t < dist (atomPt P m₂ j) (atomPt P m₁ i))
          ∧ (∑ j ∈ S, atomWtR m₂ j) + t < ∑ i ∈ T, atomWtR m₁ i)
      ∨ (∃ T : Finset (Fin (atomCount (atomList m₂))),
         ∃ S : Finset (Fin (atomCount (atomList m₁))),
        (∀ j, j ∉ S → ∀ i ∈ T, t < dist (atomPt P m₁ j) (atomPt P m₂ i))
          ∧ (∑ j ∈ S, atomWtR m₁ j) + t < ∑ i ∈ T, atomWtR m₂ i) := by
  rw [LevyProkhorov.dist_probabilityMeasure_def]
  exact lt_levyProkhorovDist_iff_cert _ _ _ _
    (fun i => atomWtR_nonneg m₁ i) (fun j => atomWtR_nonneg m₂ j) _ _
    (toMeasure_atomic P m₁) (toMeasure_atomic P m₂)

end AtomicSigma

/-! ### `RatCode` arithmetic: code-level `+`, clamp, `/`, and comparisons -/

/-- Code-level addition of coded rationals (cross-multiplication of unnormalized
fractions). -/
private def ratAddCode (c₁ c₂ : RatCode) : RatCode :=
  Nat.pair
    (Nat.pair
      (c₁.unpair.1.unpair.1 * (c₂.unpair.2 + 1) + c₂.unpair.1.unpair.1 * (c₁.unpair.2 + 1))
      (c₁.unpair.1.unpair.2 * (c₂.unpair.2 + 1) + c₂.unpair.1.unpair.2 * (c₁.unpair.2 + 1)))
    ((c₁.unpair.2 + 1) * (c₂.unpair.2 + 1) - 1)

private theorem ratOfCode_ratAddCode (c₁ c₂ : RatCode) :
    ratOfCode (ratAddCode c₁ c₂) = ratOfCode c₁ + ratOfCode c₂ := by
  have h1 : 1 ≤ (c₁.unpair.2 + 1) * (c₂.unpair.2 + 1) :=
    Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hD : (((c₁.unpair.2 + 1) * (c₂.unpair.2 + 1) - 1 : ℕ) : ℚ) + 1
      = ((c₁.unpair.2 : ℚ) + 1) * ((c₂.unpair.2 : ℚ) + 1) := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  rw [ratOfCode, ratOfCode, ratOfCode, ratAddCode]
  simp only [Nat.unpair_pair]
  rw [hD]
  have h₁ : ((c₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((c₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Code-level clamp to `[0, 1]`: decodes to `clampedWeight`. -/
private def ratClampCode (c : RatCode) : RatCode :=
  if c.unpair.1.unpair.1 ≤ c.unpair.1.unpair.2 then zeroCode
  else if c.unpair.1.unpair.2 + c.unpair.2 + 1 ≤ c.unpair.1.unpair.1 then oneCode
  else c

private theorem ratOfCode_ratClampCode (c : RatCode) :
    ratOfCode (ratClampCode c) = clampedWeight c := by
  have hd : (0 : ℚ) < (c.unpair.2 : ℚ) + 1 := by positivity
  rw [ratClampCode, clampedWeight]
  split_ifs with h1 h2
  · have hx : ratOfCode c ≤ 0 := by
      have hnum : (c.unpair.1.unpair.1 : ℚ) - c.unpair.1.unpair.2 ≤ 0 := by
        have : (c.unpair.1.unpair.1 : ℚ) ≤ c.unpair.1.unpair.2 := by exact_mod_cast h1
        linarith
      rw [ratOfCode]
      exact div_nonpos_iff.mpr (Or.inr ⟨hnum, hd.le⟩)
    rw [ratOfCode_zeroCode, min_eq_right (hx.trans zero_le_one), max_eq_left hx]
  · have hx : 1 ≤ ratOfCode c := by
      rw [ratOfCode, le_div_iff₀ hd, one_mul]
      have : (c.unpair.1.unpair.2 : ℚ) + c.unpair.2 + 1 ≤ c.unpair.1.unpair.1 := by
        exact_mod_cast h2
      linarith
    rw [ratOfCode_oneCode, min_eq_left hx, max_eq_right zero_le_one]
  · have hb : (c.unpair.1.unpair.2 : ℚ) < c.unpair.1.unpair.1 := by
      exact_mod_cast not_le.mp h1
    have ha : (c.unpair.1.unpair.1 : ℚ) < c.unpair.1.unpair.2 + c.unpair.2 + 1 := by
      exact_mod_cast not_le.mp h2
    have hx0 : 0 ≤ ratOfCode c := by
      rw [ratOfCode]
      exact div_nonneg (by linarith) hd.le
    have hx1 : ratOfCode c ≤ 1 := by
      rw [ratOfCode, div_le_one hd]
      linarith
    rw [min_eq_right hx1, max_eq_right hx0]

/-- Code-level division of coded rationals; correct whenever the divisor decodes to a
positive rational (numerator slot `a` exceeds slot `b`). -/
private def ratDivCode (c₁ c₂ : RatCode) : RatCode :=
  Nat.pair
    (Nat.pair (c₁.unpair.1.unpair.1 * (c₂.unpair.2 + 1))
      (c₁.unpair.1.unpair.2 * (c₂.unpair.2 + 1)))
    ((c₂.unpair.1.unpair.1 - c₂.unpair.1.unpair.2) * (c₁.unpair.2 + 1) - 1)

/-- Positivity of a decoded rational is the strict slot comparison. -/
private theorem ratOfCode_pos_iff (c : RatCode) :
    0 < ratOfCode c ↔ c.unpair.1.unpair.2 < c.unpair.1.unpair.1 := by
  have hd : (0 : ℚ) < (c.unpair.2 : ℚ) + 1 := by positivity
  rw [ratOfCode, lt_div_iff₀ hd, zero_mul, sub_pos]
  exact_mod_cast Iff.rfl

private theorem ratOfCode_ratDivCode (c₁ c₂ : RatCode)
    (h : c₂.unpair.1.unpair.2 < c₂.unpair.1.unpair.1) :
    ratOfCode (ratDivCode c₁ c₂) = ratOfCode c₁ / ratOfCode c₂ := by
  have hpos : 1 ≤ (c₂.unpair.1.unpair.1 - c₂.unpair.1.unpair.2) * (c₁.unpair.2 + 1) :=
    Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Nat.sub_ne_zero_of_lt h) (Nat.succ_ne_zero _))
  have hD : (((c₂.unpair.1.unpair.1 - c₂.unpair.1.unpair.2) * (c₁.unpair.2 + 1) - 1 : ℕ) : ℚ)
        + 1
      = ((c₂.unpair.1.unpair.1 : ℚ) - c₂.unpair.1.unpair.2) * ((c₁.unpair.2 : ℚ) + 1) := by
    rw [Nat.cast_sub hpos, Nat.cast_mul, Nat.cast_sub h.le]
    push_cast
    ring
  have hb2 : (0 : ℚ) < (c₂.unpair.1.unpair.1 : ℚ) - c₂.unpair.1.unpair.2 :=
    sub_pos.mpr (by exact_mod_cast h)
  have h₁ : ((c₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((c₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  rw [ratOfCode, ratOfCode, ratOfCode, ratDivCode]
  simp only [Nat.unpair_pair]
  rw [hD]
  push_cast
  field_simp

/-! ### `Primrec` bookkeeping for the code-level arithmetic -/

private theorem primrec_upFst : Primrec fun m : ℕ => m.unpair.1 :=
  Primrec.fst.comp Primrec.unpair

private theorem primrec_upSnd : Primrec fun m : ℕ => m.unpair.2 :=
  Primrec.snd.comp Primrec.unpair

private theorem primrec_numA : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
  primrec_upFst.comp primrec_upFst

private theorem primrec_numB : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
  primrec_upSnd.comp primrec_upFst

private theorem primrec_den1 : Primrec fun m : ℕ => m.unpair.2 + 1 :=
  Primrec.succ.comp primrec_upSnd

private theorem primrec_ratAddCode : Primrec₂ ratAddCode :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (primrec_numA.comp Primrec.fst) (primrec_den1.comp Primrec.snd))
        (Primrec.nat_mul.comp (primrec_numA.comp Primrec.snd) (primrec_den1.comp Primrec.fst)))
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (primrec_numB.comp Primrec.fst) (primrec_den1.comp Primrec.snd))
        (Primrec.nat_mul.comp (primrec_numB.comp Primrec.snd) (primrec_den1.comp Primrec.fst))))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (primrec_den1.comp Primrec.fst) (primrec_den1.comp Primrec.snd))
      (Primrec.const 1))

private theorem primrec_ratClampCode : Primrec ratClampCode :=
  Primrec.ite (Primrec.nat_le.comp primrec_numA primrec_numB)
    (Primrec.const zeroCode)
    (Primrec.ite
      (Primrec.nat_le.comp
        (Primrec.succ.comp (Primrec.nat_add.comp primrec_numB primrec_upSnd))
        primrec_numA)
      (Primrec.const oneCode)
      Primrec.id)

private theorem primrec_ratDivCode : Primrec₂ ratDivCode :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (Primrec.nat_mul.comp (primrec_numA.comp Primrec.fst) (primrec_den1.comp Primrec.snd))
      (Primrec.nat_mul.comp (primrec_numB.comp Primrec.fst) (primrec_den1.comp Primrec.snd)))
    (Primrec.nat_sub.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_sub.comp (primrec_numA.comp Primrec.snd) (primrec_numB.comp Primrec.snd))
        (primrec_den1.comp Primrec.fst))
      (Primrec.const 1))

/-! ### `testBit`, powers of two, and subset bitmasks -/

/-- Powers of two, primitively — the shared proof lives in `ForMathlib/PrimrecArith.lean`. -/
private theorem primrec_pow2 : Primrec fun k : ℕ => 2 ^ k := primrec_pow 2

private theorem primrec_testBit : Primrec₂ Nat.testBit := by
  have h : PrimrecPred fun p : ℕ × ℕ => p.1 / 2 ^ p.2 % 2 = 1 :=
    Primrec.eq.comp
      (Primrec.nat_mod.comp
        (Primrec.nat_div.comp Primrec.fst (primrec_pow2.comp Primrec.snd))
        (Primrec.const 2))
      (Primrec.const 1)
  exact h.decide.of_eq fun p => (Nat.testBit_eq_decide_div_mod_eq).symm

/-- Every `Bool` predicate on an initial segment is the bit pattern of a bounded
mask. -/
private theorem exists_mask (k : ℕ) (f : ℕ → Bool) :
    ∃ mask, mask < 2 ^ k ∧ ∀ i, i < k → mask.testBit i = f i := by
  induction k with
  | zero => exact ⟨0, Nat.one_pos, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ k ih =>
    obtain ⟨m, hm, hbits⟩ := ih
    refine ⟨bif f k then 2 ^ k + m else m, ?_, fun i hi => ?_⟩
    · cases f k with
      | false =>
        rw [Bool.cond_false]
        calc m < 2 ^ k := hm
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k)
      | true =>
        rw [Bool.cond_true, pow_succ, Nat.mul_two]
        exact Nat.add_lt_add_left hm _
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · cases hfk : f k with
        | false => rw [Bool.cond_false]; exact hbits i hlt
        | true => rw [Bool.cond_true, Nat.testBit_two_pow_add_gt hlt]; exact hbits i hlt
      · cases hfk : f i with
        | false => rw [Bool.cond_false]; exact Nat.testBit_lt_two_pow hm
        | true =>
          rw [Bool.cond_true, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm]
          rfl

/-- The bitmask of an arbitrary `Finset (Fin k)`. -/
private theorem exists_finset_mask {k : ℕ} (T : Finset (Fin k)) :
    ∃ mask, mask < 2 ^ k
      ∧ ∀ (i : ℕ) (hi : i < k), (mask.testBit i = true ↔ ⟨i, hi⟩ ∈ T) := by
  obtain ⟨mask, hlt, hbits⟩ :=
    exists_mask k fun i => if hi : i < k then decide (⟨i, hi⟩ ∈ T) else false
  refine ⟨mask, hlt, fun i hi => ?_⟩
  rw [hbits i hi, dif_pos hi, decide_eq_true_iff]

/-! ### The uniform coded atomic data -/

private theorem primrec_atomList : Primrec atomList := Primrec.ofNat (List (ℕ × ℕ))

/-- Code of the clamped weight sum of a decoded atom list. -/
private def wSumCode : List (ℕ × ℕ) → RatCode
  | [] => zeroCode
  | pr :: l => ratAddCode (ratClampCode pr.2) (wSumCode l)

private theorem clampedWeightSum_cons (pr : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    clampedWeightSum (pr :: l) = clampedWeight pr.2 + clampedWeightSum l := by
  rw [clampedWeightSum, List.map_cons, List.sum_cons]
  rfl

private theorem ratOfCode_wSumCode (l : List (ℕ × ℕ)) :
    ratOfCode (wSumCode l) = clampedWeightSum l := by
  induction l with
  | nil =>
    rw [wSumCode, ratOfCode_zeroCode]
    rw [clampedWeightSum, List.map_nil, List.sum_nil]
  | cons pr l ih =>
    rw [wSumCode, ratOfCode_ratAddCode, ratOfCode_ratClampCode, ih, clampedWeightSum_cons]

private theorem primrec_wSumCode : Primrec wSumCode := by
  have h : Primrec fun l : List (ℕ × ℕ) =>
      l.foldr (fun pr acc => ratAddCode (ratClampCode pr.2) acc) zeroCode :=
    (Primrec.list_foldr Primrec.id (Primrec.const zeroCode)
      ((primrec_ratAddCode.comp
        (primrec_ratClampCode.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂)).of_eq fun l => rfl
  refine h.of_eq fun l => ?_
  induction l with
  | nil => rfl
  | cons pr l ih => rw [List.foldr_cons, ih, wSumCode]

/-- The coded-side test `0 < clampedWeightSum (atomList m)` as it appears in the uniform
data. -/
private theorem wSum_pos_iff (m : ℕ) :
    ratOfCode zeroCode < ratOfCode (wSumCode (atomList m))
      ↔ ¬ clampedWeightSum (atomList m) = 0 := by
  rw [ratOfCode_zeroCode, ratOfCode_wSumCode]
  constructor
  · exact fun h => h.ne'
  · exact fun h => lt_of_le_of_ne (clampedWeightSum_nonneg _) (Ne.symm h)

/-- Uniform atom count, computed on codes. -/
private def natAtomCount (m : ℕ) : ℕ :=
  if ratOfCode zeroCode < ratOfCode (wSumCode (atomList m)) then (atomList m).length else 1

private theorem natAtomCount_eq (m : ℕ) : natAtomCount m = atomCount (atomList m) := by
  rw [natAtomCount, atomCount]
  by_cases h : clampedWeightSum (atomList m) = 0
  · rw [if_neg (fun hc => (wSum_pos_iff m).mp hc h), if_pos h]
  · rw [if_pos ((wSum_pos_iff m).mpr h), if_neg h]

private theorem primrec_natAtomCount : Primrec natAtomCount :=
  Primrec.ite
    (primrecPred_ratLt (Primrec.const zeroCode) (primrec_wSumCode.comp primrec_atomList))
    (Primrec.list_length.comp primrec_atomList)
    (Primrec.const 1)

/-- Uniform dense-point index, computed on codes. -/
private def natAtomIdx (m i : ℕ) : ℕ :=
  if ratOfCode zeroCode < ratOfCode (wSumCode (atomList m)) then
    ((atomList m).getD i (0, 0)).1
  else 0

private theorem natAtomIdx_eq (m i : ℕ) : natAtomIdx m i = atomIdx (atomList m) i := by
  rw [natAtomIdx, atomIdx]
  by_cases h : clampedWeightSum (atomList m) = 0
  · rw [if_neg (fun hc => (wSum_pos_iff m).mp hc h), if_pos h]
  · rw [if_pos ((wSum_pos_iff m).mpr h), if_neg h]

private theorem primrec_natAtomIdx : Primrec₂ natAtomIdx :=
  Primrec.ite
    (primrecPred_ratLt (Primrec.const zeroCode)
      (primrec_wSumCode.comp (primrec_atomList.comp Primrec.fst)))
    (Primrec.fst.comp
      ((Primrec.list_getD ((0 : ℕ), (0 : ℕ))).comp (primrec_atomList.comp Primrec.fst)
        Primrec.snd))
    (Primrec.const 0)

/-- Uniform coded atom weight: decodes to `atomWt`. -/
private def natAtomWtCode (m i : ℕ) : RatCode :=
  if ratOfCode zeroCode < ratOfCode (wSumCode (atomList m)) then
    ratDivCode (ratClampCode ((atomList m).getD i (0, 0)).2) (wSumCode (atomList m))
  else oneCode

private theorem ratOfCode_natAtomWtCode (m i : ℕ) :
    ratOfCode (natAtomWtCode m i) = atomWt (atomList m) i := by
  rw [natAtomWtCode, atomWt]
  by_cases h : clampedWeightSum (atomList m) = 0
  · rw [if_neg (fun hc => (wSum_pos_iff m).mp hc h), if_pos h, ratOfCode_oneCode]
  · have hpos : 0 < clampedWeightSum (atomList m) :=
      lt_of_le_of_ne (clampedWeightSum_nonneg _) (Ne.symm h)
    have hnum : (wSumCode (atomList m)).unpair.1.unpair.2
        < (wSumCode (atomList m)).unpair.1.unpair.1 :=
      (ratOfCode_pos_iff _).mp (by rw [ratOfCode_wSumCode]; exact hpos)
    rw [if_pos ((wSum_pos_iff m).mpr h), if_neg h, ratOfCode_ratDivCode _ _ hnum,
      ratOfCode_ratClampCode, ratOfCode_wSumCode]

private theorem primrec_natAtomWtCode : Primrec₂ natAtomWtCode :=
  Primrec.ite
    (primrecPred_ratLt (Primrec.const zeroCode)
      (primrec_wSumCode.comp (primrec_atomList.comp Primrec.fst)))
    (primrec_ratDivCode.comp
      (primrec_ratClampCode.comp (Primrec.snd.comp
        ((Primrec.list_getD ((0 : ℕ), (0 : ℕ))).comp (primrec_atomList.comp Primrec.fst)
          Primrec.snd)))
      (primrec_wSumCode.comp (primrec_atomList.comp Primrec.fst)))
    (Primrec.const oneCode)

/-- Coded masked weight sum: the code of
`∑_{i < k, testBit mask i} atomWt (atomList m) i`. -/
private def maskWtSumCode (m k mask : ℕ) : RatCode :=
  Nat.rec (motive := fun _ => RatCode) zeroCode
    (fun n ih => bif mask.testBit n then ratAddCode (natAtomWtCode m n) ih else ih) k

private theorem ratOfCode_maskWtSumCode (m k mask : ℕ) :
    ratOfCode (maskWtSumCode m k mask)
      = ∑ i ∈ Finset.range k,
          if mask.testBit i = true then atomWt (atomList m) i else 0 := by
  induction k with
  | zero =>
    rw [show maskWtSumCode m 0 mask = zeroCode from rfl, ratOfCode_zeroCode,
      Finset.range_zero, Finset.sum_empty]
  | succ k ih =>
    rw [show maskWtSumCode m (k + 1) mask
        = (bif mask.testBit k then ratAddCode (natAtomWtCode m k) (maskWtSumCode m k mask)
            else maskWtSumCode m k mask) from rfl,
      Finset.sum_range_succ]
    cases htb : mask.testBit k with
    | false =>
      rw [Bool.cond_false, ih, if_neg (by exact Bool.false_ne_true), add_zero]
    | true =>
      rw [Bool.cond_true, ratOfCode_ratAddCode, ratOfCode_natAtomWtCode, ih, if_pos rfl]
      exact add_comm _ _

private theorem primrec_maskWtSumCode :
    Primrec fun p : ℕ × ℕ × ℕ => maskWtSumCode p.1 p.2.1 p.2.2 := by
  have hh : Primrec₂ fun (p : ℕ × ℕ × ℕ) (q : ℕ × RatCode) =>
      bif p.2.2.testBit q.1 then ratAddCode (natAtomWtCode p.1 q.1) q.2 else q.2 :=
    Primrec.cond
      (primrec_testBit.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd))
      (primrec_ratAddCode.comp
        (primrec_natAtomWtCode.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.nat_rec' (Primrec.fst.comp Primrec.snd) (Primrec.const zeroCode) hh).of_eq
    fun p => rfl

/-- The bridge from coded masked sums to `Finset (Fin k)` sums, through a matching
bitmask. -/
private theorem ratOfCode_maskWtSumCode_eq_sum {k : ℕ} (m mask : ℕ) (S : Finset (Fin k))
    (h : ∀ (i : ℕ) (hi : i < k), (mask.testBit i = true ↔ ⟨i, hi⟩ ∈ S)) :
    ratOfCode (maskWtSumCode m k mask) = ∑ j ∈ S, atomWt (atomList m) (j : ℕ) := by
  rw [ratOfCode_maskWtSumCode,
    ← Fin.sum_univ_eq_sum_range
      (fun i => if mask.testBit i = true then atomWt (atomList m) i else 0) k]
  calc ∑ i : Fin k, (if mask.testBit (i : ℕ) = true then atomWt (atomList m) (i : ℕ) else 0)
      = ∑ i : Fin k, (if i ∈ S then atomWt (atomList m) (i : ℕ) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hmem : i ∈ S
        · rw [if_pos hmem, if_pos]
          rw [h (i : ℕ) i.isLt]
          simpa using hmem
        · rw [if_neg hmem, if_neg]
          rw [h (i : ℕ) i.isLt]
          simpa using hmem
    _ = ∑ j ∈ S, atomWt (atomList m) (j : ℕ) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! With the semantics and `Primrec` lemmas established, the coded machinery is sealed:
nothing downstream may unfold it (unfolding `natAtomCount`-style bodies drags numeral
evaluation of `Nat.unpair`/`Nat.sqrt` into `isDefEq` and blows up elaboration). -/
attribute [local irreducible] zeroCode oneCode ratOfCode ratAddCode ratClampCode
  ratDivCode wSumCode natAtomCount natAtomIdx natAtomWtCode maskWtSumCode

/-- Filter-defined finsets satisfy the bitmask membership interface. -/
private theorem filter_mask_interface {k : ℕ} (mask : ℕ) :
    ∀ (i : ℕ) (hi : i < k),
      (mask.testBit i = true ↔
        ⟨i, hi⟩ ∈ Finset.univ.filter fun i : Fin k => mask.testBit (i : ℕ) = true) := by
  intro i hi
  rw [Finset.mem_filter]
  exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩

/-! ### The Prokhorov presentation: both semidecisions discharged -/

section Presentation

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable (P : ComputableMetricPresentation X)


/-! ### Certified weights: the narrow public interface for masked atomic lower bounds -/

/-- The certified-weight accumulator: the summed weights of the atoms a bitmask certifies.
The branch is on **zero total raw weight**, not on the list being empty — `atomicOfList` then
denotes the default Dirac regardless of what atoms are listed, so a masked weight sum would
overshoot its mass. Returning `zeroCode` there is what makes the bound below unconditional.
Bits at or beyond the list length are ignored, since the sum runs to `(atomList m).length`. -/
private def certWtCode (m mask : ℕ) : RatCode :=
  if ratOfCode zeroCode < ratOfCode (wSumCode (atomList m)) then
    maskWtSumCode m (atomList m).length mask
  else zeroCode

private theorem primrec_certWtCode : Primrec₂ certWtCode :=
  Primrec.ite
    (primrecPred_ratLt (Primrec.const zeroCode)
      (primrec_wSumCode.comp (primrec_atomList.comp Primrec.fst)))
    (primrec_maskWtSumCode.comp
      (Primrec.fst.pair
        ((Primrec.list_length.comp (primrec_atomList.comp Primrec.fst)).pair Primrec.snd)))
    (Primrec.const zeroCode)

omit [BorelSpace X] in
/-- **Certified weights under-estimate the atomic mass.** One primitive recursive accumulator
takes an atom-list index and a bitmask of atoms *certified* to lie in `A`, and returns a
rational code whose value is at most the mass `atomic P m` gives `A`.

This is the interface a realizer needs when it can only decide atom membership
semidecidably: certifying fewer atoms yields a smaller — still valid — lower bound, so
positive information alone suffices and no negative membership decision is ever required.

Deliberately narrow: the weight layer this is proved from stays private, and this is the only
statement about atomic masses exposed. -/
theorem exists_certifiedWeightCode :
    ∃ acc : ℕ → ℕ → RatCode, Primrec₂ acc ∧
      ∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
        (∀ i, i < (ofNat (List (ℕ × ℕ)) m).length → mask.testBit i = true →
          P.dense ((ofNat (List (ℕ × ℕ)) m).getD i (0, 0)).1 ∈ A) →
        ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A := by
  classical
  refine ⟨certWtCode, primrec_certWtCode, fun m mask A hA hcert => ?_⟩
  rw [certWtCode]
  by_cases hdeg : ratOfCode zeroCode < ratOfCode (wSumCode (atomList m))
  · rw [if_pos hdeg]
    have hne : ¬ clampedWeightSum (atomList m) = 0 := (wSum_pos_iff m).mp hdeg
    set l := atomList m with hl
    -- the atomic mass as a `Fin l.length` sum, then as a `range` sum
    have hmass : (atomic P m).toMeasure A
        = ∑ i ∈ Finset.range l.length,
            ENNReal.ofReal ((atomWt l i : ℚ) : ℝ) *
              Set.indicator A 1 (P.dense (l.getD i (0, 0)).1) := by
      rw [show (atomic P m) = atomicOfList P l from rfl,
        toMeasure_atomicOfList_of_ne_zero P hne, Measure.finsetSum_apply]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => ENNReal.ofReal ((atomWt l i : ℚ) : ℝ) *
          Set.indicator A 1 (P.dense (l.getD i (0, 0)).1)) l.length]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA, atomWt, if_neg hne,
        List.getD_eq_getElem _ _ i.2]
      rfl
    rw [hmass, ratOfCode_maskWtSumCode]
    have hnn : ∀ i ∈ Finset.range l.length,
        (0 : ℝ) ≤ ((if mask.testBit i = true then atomWt l i else 0 : ℚ) : ℝ) := by
      intro i _
      by_cases hb : mask.testBit i = true
      · rw [if_pos hb]; exact_mod_cast atomWt_nonneg l i
      · rw [if_neg hb]; norm_num
    rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg hnn]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases hb : mask.testBit i = true
    · have hmem : P.dense (l.getD i (0, 0)).1 ∈ A := hcert i (Finset.mem_range.mp hi) hb
      rw [if_pos hb, Set.indicator_of_mem hmem]
      simp
    · rw [if_neg hb]
      simp
  · rw [if_neg hdeg, ratOfCode_zeroCode]
    simp

/-! ### The uniform normalized atom list, and a complete-mask accumulator

`certWtCode` above accumulates over the *raw* decoded list, which on the degenerate branch
names atoms the measure does not charge; a lower bound is therefore the most it can give. The
package below accumulates over the list the uniform layer indexes instead, which makes the
same accumulator exact as soon as the mask is complete. -/

/-- The **uniform normalized atom list** of a coded atomic: the `(dense index, weight code)`
pairs at the positions the uniform layer indexes, with weights already normalized.

This is *not* a support. On the nondegenerate branch it keeps every position of the raw
decoded list, so zero-weight entries survive and a dense-point index may repeat. Neither
matters for the accumulator below: a zero-weight entry contributes nothing to either side of
the sum, and repeated indices are summed on both sides alike, which is why the exactness
proof needs no positivity or injectivity hypothesis.

On the degenerate branch — zero total raw weight — `atomic P m` is the point mass at
`P.dense 0` whatever the raw list holds, and this list is correspondingly the singleton
`[(0, oneCode)]`. Naming the default atom explicitly is what lets the accumulator below be
exact rather than merely a lower bound. -/
private def certifiedAtoms (m : ℕ) : List (ℕ × ℕ) :=
  (List.range (natAtomCount m)).map fun i => (natAtomIdx m i, natAtomWtCode m i)

private theorem primrec_certifiedAtoms : Primrec certifiedAtoms :=
  Primrec.list_map (Primrec.list_range.comp primrec_natAtomCount)
    ((primrec_natAtomIdx.comp Primrec.fst Primrec.snd).pair
      (primrec_natAtomWtCode.comp Primrec.fst Primrec.snd))

private theorem length_certifiedAtoms (m : ℕ) : (certifiedAtoms m).length = natAtomCount m := by
  rw [certifiedAtoms, List.length_map, List.length_range]

private theorem fst_getD_certifiedAtoms {m i : ℕ} (h : i < natAtomCount m) :
    ((certifiedAtoms m).getD i (0, 0)).1 = natAtomIdx m i := by
  have hlen : i < ((List.range (natAtomCount m)).map
      fun k => (natAtomIdx m k, natAtomWtCode m k)).length := by simpa using h
  rw [certifiedAtoms, List.getD_eq_getElem _ _ hlen]
  simp

/-- The accumulator of `certifiedAtoms`: the masked weight sum taken to the *full* atom count,
so that a complete mask sums every atom the measure charges. This is the existing masked-sum
layer at a different bound, not a new one — `maskWtSumCode` already takes its bound
independently of the atom index. -/
private def completeCertWtCode (m mask : ℕ) : RatCode :=
  maskWtSumCode m (natAtomCount m) mask

private theorem primrec_completeCertWtCode : Primrec₂ completeCertWtCode :=
  primrec_maskWtSumCode.comp
    (Primrec.fst.pair ((primrec_natAtomCount.comp Primrec.fst).pair Primrec.snd))

private theorem ratOfCode_completeCertWtCode (m mask : ℕ) :
    ratOfCode (completeCertWtCode m mask)
      = ∑ i ∈ Finset.range (natAtomCount m),
          if mask.testBit i = true then atomWt (atomList m) i else 0 := by
  rw [completeCertWtCode, ratOfCode_maskWtSumCode]

/-- The accumulator never denotes a negative rational: it is a sum of masked atom weights, and
`atomWt` is nonnegative on both branches. Needed at the *use* site rather than internally —
`ENNReal.ofReal` truncates, so the exactness equation alone leaves the value unpinned when the
mass is zero. -/
private theorem nonneg_ratOfCode_completeCertWtCode (m mask : ℕ) :
    0 ≤ ratOfCode (completeCertWtCode m mask) := by
  rw [ratOfCode_completeCertWtCode]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hb : mask.testBit i = true
  · rw [if_pos hb]; exact atomWt_nonneg _ i
  · rw [if_neg hb]

private theorem nonneg_maskedWt (m mask : ℕ) :
    ∀ i ∈ Finset.range (natAtomCount m),
      (0 : ℝ) ≤ ((if mask.testBit i = true then atomWt (atomList m) i else 0 : ℚ) : ℝ) := by
  intro i _
  by_cases hb : mask.testBit i = true
  · rw [if_pos hb]; exact_mod_cast atomWt_nonneg (atomList m) i
  · rw [if_neg hb]; norm_num

omit [BorelSpace X] in
/-- The decoded atomic mass of a measurable set, as one `Finset.range` sum over the uniform
atom layer — the same shape on both branches, which is what removes the degenerate case from
every proof below. -/
private theorem toMeasure_atomic_eq_range_sum (m : ℕ) {A : Set X} (hA : MeasurableSet A) :
    (atomic P m).toMeasure A
      = ∑ i ∈ Finset.range (natAtomCount m),
          ENNReal.ofReal ((atomWt (atomList m) i : ℚ) : ℝ) *
            Set.indicator A 1 (P.dense (natAtomIdx m i)) := by
  simp only [natAtomCount_eq, natAtomIdx_eq]
  rw [show (atomic P m) = atomicOfList P (atomList m) from rfl,
    toMeasure_atomic_eq_sum P (atomList m), Measure.finsetSum_apply,
    ← Fin.sum_univ_eq_sum_range
      (fun i => ENNReal.ofReal ((atomWt (atomList m) i : ℚ) : ℝ) *
        Set.indicator A 1 (P.dense (atomIdx (atomList m) i))) (atomCount (atomList m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]

omit [BorelSpace X] in
/-- **A certified-weight accumulator that is exact on complete masks.**

One primitive recursive atom list and one primitive recursive accumulator over bitmasks of
that list, such that for every coded atomic `m` and every measurable `A`:

* *nonnegativity* — the accumulator never denotes a negative rational, unconditionally;
* *soundness* — if every bit set in `mask` marks an entry whose point lies in `A`, the
  accumulator is a lower bound for the mass `atomic P m` gives `A`; and
* *exactness* — if `mask` marks the entries whose points lie in `A` and **no others**, the
  accumulator is that mass exactly.

Nonnegativity is load-bearing, not decoration. `ENNReal.ofReal` truncates at zero, so from the
exactness equation alone the accumulator's value is unpinned whenever the mass is zero — it
could be any negative rational. With this clause a consumer recovers the real equation:

    have := congrArg ENNReal.toReal hexact
    simpa [ENNReal.toReal_ofReal (hnonneg m mask)] using this

It belongs inside the package so that it holds of the **same** chosen accumulator; deriving it
externally would mean unfolding an implementation this interface deliberately hides.

The second clause is what `exists_certifiedWeightCode` cannot provide. That interface
accumulates over the raw decoded list, whose entries need not be atoms of the measure at all,
so completing its mask does not account for the measure's mass. Here the list is the uniform
normalized one, so a complete mask leaves nothing out — including on the degenerate branch,
where the default atom appears in the list like any other and needs no separate case.

The list is indexed positionally, not by point: it may carry zero-weight entries and repeat a
dense-point index, and the mask is read at positions accordingly. Both clauses quantify over
positions `i < (atoms m).length` for exactly that reason.

Soundness is stated for the same accumulator, so a realizer that can only semidecide atom
membership keeps the old lower-bound reading while a realizer that eventually decides it gets
convergence to the true mass from the same code. -/
theorem exists_completeCertifiedWeightCode :
    ∃ (atoms : ℕ → List (ℕ × ℕ)) (acc : ℕ → ℕ → RatCode),
      Primrec atoms ∧ Primrec₂ acc ∧
      (∀ m mask : ℕ, (0 : ℝ) ≤ ((ratOfCode (acc m mask) : ℚ) : ℝ)) ∧
      (∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
        (∀ i, i < (atoms m).length → mask.testBit i = true →
          P.dense ((atoms m).getD i (0, 0)).1 ∈ A) →
        ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) ≤ (atomic P m).toMeasure A) ∧
      (∀ (m mask : ℕ) (A : Set X), MeasurableSet A →
        (∀ i, i < (atoms m).length →
          (mask.testBit i = true ↔ P.dense ((atoms m).getD i (0, 0)).1 ∈ A)) →
        ENNReal.ofReal ((ratOfCode (acc m mask) : ℚ) : ℝ) = (atomic P m).toMeasure A) := by
  classical
  refine ⟨certifiedAtoms, completeCertWtCode, primrec_certifiedAtoms,
    primrec_completeCertWtCode,
    fun m mask => by exact_mod_cast nonneg_ratOfCode_completeCertWtCode m mask, ?_, ?_⟩
  · intro m mask A hA hcert
    rw [toMeasure_atomic_eq_range_sum P m hA, ratOfCode_completeCertWtCode, Rat.cast_sum,
      ENNReal.ofReal_sum_of_nonneg (nonneg_maskedWt m mask)]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i < natAtomCount m := Finset.mem_range.mp hi
    by_cases hb : mask.testBit i = true
    · have hmem : P.dense (natAtomIdx m i) ∈ A := by
        have h := hcert i (by rw [length_certifiedAtoms]; exact hi') hb
        rwa [fst_getD_certifiedAtoms hi'] at h
      rw [if_pos hb, Set.indicator_of_mem hmem]
      simp
    · rw [if_neg hb]
      simp
  · intro m mask A hA hcert
    rw [toMeasure_atomic_eq_range_sum P m hA, ratOfCode_completeCertWtCode, Rat.cast_sum,
      ENNReal.ofReal_sum_of_nonneg (nonneg_maskedWt m mask)]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < natAtomCount m := Finset.mem_range.mp hi
    have hiff := hcert i (by rw [length_certifiedAtoms]; exact hi')
    rw [fst_getD_certifiedAtoms hi'] at hiff
    by_cases hb : mask.testBit i = true
    · rw [if_pos hb, Set.indicator_of_mem (hiff.mp hb)]
      simp
    · rw [if_neg hb, Set.indicator_of_notMem (fun hmem => by simp [hiff.mpr hmem] at hb)]
      simp

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The fully coded form of the witnessed strict finite condition** between two
decoded atomics at a coded threshold: subset tables as bounded bitmasks, rational-sum
comparisons on codes, and `P.dense`-indexed strict distance atoms. -/
private theorem strictFinCond_atomic_iff_coded (m₁ m₂ : ℕ) (d : RatCode) :
    (∀ tT < 2 ^ natAtomCount m₁, ∃ tS < 2 ^ natAtomCount m₂,
        (¬ ratOfCode (ratAddCode (maskWtSumCode m₂ (natAtomCount m₂) tS) d)
            < ratOfCode (maskWtSumCode m₁ (natAtomCount m₁) tT))
          ∧ ∀ j < natAtomCount m₂, tS.testBit j = true →
              ∃ i < natAtomCount m₁, tT.testBit i = true ∧
                dist (P.dense (natAtomIdx m₂ j)) (P.dense (natAtomIdx m₁ i))
                  < (ratOfCode d : ℝ)) ↔
      strictFinCond (fun i => atomPt P m₁ i) (fun j => atomPt P m₂ j)
        (fun i : Fin (atomCount (atomList m₁)) => atomWtR m₁ i)
        (fun j : Fin (atomCount (atomList m₂)) => atomWtR m₂ j) ((ratOfCode d : ℝ)) := by
  rw [strictFinCond_iff_witness _ _ _ _ (fun j => atomWtR_nonneg m₂ j)]
  simp only [natAtomCount_eq, natAtomIdx_eq]
  constructor
  · -- coded → witnessed
    intro h T
    obtain ⟨tT, htT, hTbits⟩ := exists_finset_mask T
    obtain ⟨tS, htS, hA, hB⟩ := h tT htT
    refine ⟨Finset.univ.filter
      fun j : Fin (atomCount (atomList m₂)) => tS.testBit (j : ℕ) = true, ?_, ?_⟩
    · intro j hjS
      obtain ⟨i, hik, htTi, hdist⟩ := hB (j : ℕ) j.isLt (Finset.mem_filter.mp hjS).2
      exact ⟨⟨i, hik⟩, (hTbits i hik).mp htTi, hdist⟩
    · have h' := not_lt.mp hA
      rw [ratOfCode_ratAddCode,
        ratOfCode_maskWtSumCode_eq_sum m₂ tS _ (filter_mask_interface _),
        ratOfCode_maskWtSumCode_eq_sum m₁ tT T hTbits] at h'
      simp only [atomWtR]
      exact_mod_cast h'
  · -- witnessed → coded
    intro h tT htT
    obtain ⟨S, hS1, hS2⟩ :=
      h (Finset.univ.filter
        fun i : Fin (atomCount (atomList m₁)) => tT.testBit (i : ℕ) = true)
    obtain ⟨tS, htS, hSbits⟩ := exists_finset_mask S
    refine ⟨tS, htS, ?_, ?_⟩
    · rw [not_lt, ratOfCode_ratAddCode,
        ratOfCode_maskWtSumCode_eq_sum m₂ tS S hSbits,
        ratOfCode_maskWtSumCode_eq_sum m₁ tT _ (filter_mask_interface _)]
      have h2 := hS2
      simp only [atomWtR] at h2
      exact_mod_cast h2
    · intro j hj htSj
      obtain ⟨i, hiT, hdist⟩ := hS1 ⟨j, hj⟩ ((hSbits j hj).mp htSj)
      exact ⟨(i : ℕ), i.isLt, (Finset.mem_filter.mp hiT).2, hdist⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- **`REPred` of the strict finite condition between decoded atomics**, uniformly in
the two atomic indices and the coded threshold: the full Σ₁ assembly through the
bounded-quantifier closure riders of `ForMathlib/REPredClosure.lean`. -/
private theorem repred_strictFinCondAtomic :
    REPred fun v : ℕ × ℕ × RatCode =>
      strictFinCond (fun i => atomPt P v.1 i) (fun j => atomPt P v.2.1 j)
        (fun i : Fin (atomCount (atomList v.1)) => atomWtR v.1 i)
        (fun j : Fin (atomCount (atomList v.2.1)) => atomWtR v.2.1 j)
        ((ratOfCode v.2.2 : ℝ)) := by
  -- level-4 input: ((((v, tT), tS), j), i)
  have hproj_v : Primrec fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ => u.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hg : Computable fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
      ((natAtomIdx u.1.1.1.1.2.1 u.1.2, natAtomIdx u.1.1.1.1.1 u.2, u.1.1.1.1.2.2) :
        ℕ × ℕ × RatCode) :=
    ((primrec_natAtomIdx.comp (Primrec.fst.comp (Primrec.snd.comp hproj_v))
        (Primrec.snd.comp Primrec.fst)).pair
      ((primrec_natAtomIdx.comp (Primrec.fst.comp hproj_v) Primrec.snd).pair
        (Primrec.snd.comp (Primrec.snd.comp hproj_v)))).to_comp
  have hguard_i : PrimrecPred fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
      u.1.1.1.2.testBit u.2 = true :=
    Primrec.eq.comp
      (primrec_testBit.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
      (Primrec.const true)
  have hatom : REPred fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
      u.1.1.1.2.testBit u.2 = true ∧
        dist (P.dense (natAtomIdx u.1.1.1.1.2.1 u.1.2)) (P.dense (natAtomIdx u.1.1.1.1.1 u.2))
          < (ratOfCode u.1.1.1.1.2.2 : ℝ) :=
    repred_and (repred_of_primrecPred hguard_i) (repred_comp P.ltSemidec hg)
  -- level 3: bounded ∃ i < k₁
  have hex_i := repred_exists_lt hatom
    (primrec_natAtomCount.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  -- level 3 guard: testBit tS j = true → ...
  have hguard_j : PrimrecPred fun u₃ : (((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ =>
      ¬ u₃.1.2.testBit u₃.2 = true :=
    (Primrec.eq.comp
      (primrec_testBit.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const true)).not
  have himp_j := (repred_or (repred_of_primrecPred hguard_j) hex_i).of_eq
    fun u₃ => (imp_iff_not_or).symm
  -- level 2: bounded ∀ j < k₂
  have hforall_j := repred_forall_lt himp_j
    (primrec_natAtomCount.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  -- level 2 decidable sum condition
  have hm₁' : Primrec fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ => u₂.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm₂' : Primrec fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ => u₂.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hd' : Primrec fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ => u₂.1.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hA : PrimrecPred fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ =>
      ¬ ratOfCode (ratAddCode (maskWtSumCode u₂.1.1.2.1 (natAtomCount u₂.1.1.2.1) u₂.2)
            u₂.1.1.2.2)
          < ratOfCode (maskWtSumCode u₂.1.1.1 (natAtomCount u₂.1.1.1) u₂.1.2) :=
    (primrecPred_ratLt
      (primrec_ratAddCode.comp
        (primrec_maskWtSumCode.comp
          (hm₂'.pair ((primrec_natAtomCount.comp hm₂').pair Primrec.snd)))
        hd')
      (primrec_maskWtSumCode.comp
        (hm₁'.pair ((primrec_natAtomCount.comp hm₁').pair (Primrec.snd.comp Primrec.fst))))).not
  have hbody2 := repred_and (repred_of_primrecPred hA) hforall_j
  -- level 1: bounded ∃ tS < 2 ^ k₂
  have hex_tS := repred_exists_lt hbody2
    (primrec_pow2.comp
      (primrec_natAtomCount.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  -- level 0: bounded ∀ tT < 2 ^ k₁
  have hforall_tT := repred_forall_lt hex_tS
    (primrec_pow2.comp (primrec_natAtomCount.comp Primrec.fst))
  exact hforall_tT.of_eq fun v => strictFinCond_atomic_iff_coded P v.1 v.2.1 v.2.2

omit [MeasurableSpace X] [BorelSpace X] in
/-- **The fully coded form of the `gtSemidec` violation certificate** between two
decoded atomics: subset tables as bounded bitmasks, coded rational sums, and
`P.dense`-indexed strict distance atoms. -/
private theorem gtCert_atomic_iff_coded (m₁ m₂ : ℕ) (c : RatCode) :
    (∃ tT < 2 ^ natAtomCount m₁, ∃ tS < 2 ^ natAtomCount m₂,
      (ratOfCode (ratAddCode (maskWtSumCode m₂ (natAtomCount m₂) tS) c)
          < ratOfCode (maskWtSumCode m₁ (natAtomCount m₁) tT))
        ∧ ∀ j < natAtomCount m₂, tS.testBit j = false →
            ∀ i < natAtomCount m₁, tT.testBit i = true →
              (ratOfCode c : ℝ)
                < dist (P.dense (natAtomIdx m₂ j)) (P.dense (natAtomIdx m₁ i))) ↔
      (∃ T : Finset (Fin (atomCount (atomList m₁))),
       ∃ S : Finset (Fin (atomCount (atomList m₂))),
        (∀ j, j ∉ S → ∀ i ∈ T, (ratOfCode c : ℝ) < dist (atomPt P m₂ j) (atomPt P m₁ i))
          ∧ (∑ j ∈ S, atomWtR m₂ j) + (ratOfCode c : ℝ) < ∑ i ∈ T, atomWtR m₁ i) := by
  simp only [natAtomCount_eq, natAtomIdx_eq]
  constructor
  · rintro ⟨tT, htT, tS, htS, hA, hB⟩
    refine ⟨Finset.univ.filter
        (fun i : Fin (atomCount (atomList m₁)) => tT.testBit (i : ℕ) = true),
      Finset.univ.filter
        (fun j : Fin (atomCount (atomList m₂)) => tS.testBit (j : ℕ) = true),
      ?_, ?_⟩
    · intro j hjS i hiT
      have htb : tS.testBit (j : ℕ) = false := by
        cases htb : tS.testBit (j : ℕ) with
        | false => rfl
        | true => exact (hjS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htb⟩)).elim
      exact hB (j : ℕ) j.isLt htb (i : ℕ) i.isLt (Finset.mem_filter.mp hiT).2
    · have h' := hA
      rw [ratOfCode_ratAddCode,
        ratOfCode_maskWtSumCode_eq_sum m₂ tS _ (filter_mask_interface _),
        ratOfCode_maskWtSumCode_eq_sum m₁ tT _ (filter_mask_interface _)] at h'
      simp only [atomWtR]
      exact_mod_cast h'
  · rintro ⟨T, S, hout, hlt⟩
    obtain ⟨tT, htT, hTbits⟩ := exists_finset_mask T
    obtain ⟨tS, htS, hSbits⟩ := exists_finset_mask S
    refine ⟨tT, htT, tS, htS, ?_, ?_⟩
    · rw [ratOfCode_ratAddCode,
        ratOfCode_maskWtSumCode_eq_sum m₂ tS S hSbits,
        ratOfCode_maskWtSumCode_eq_sum m₁ tT T hTbits]
      have h2 := hlt
      simp only [atomWtR] at h2
      exact_mod_cast h2
    · intro j hj htSj i hi htTi
      refine hout ⟨j, hj⟩ ?_ ⟨i, hi⟩ ((hTbits i hi).mp htTi)
      intro hmem
      rw [(hSbits j hj).mpr hmem] at htSj
      exact Bool.noConfusion htSj

omit [MeasurableSpace X] [BorelSpace X] in
/-- **`REPred` of the one-sided `gtSemidec` certificate** between decoded atomics,
uniformly in the two atomic indices and the coded threshold. -/
private theorem repred_gtCert :
    REPred fun v : ℕ × ℕ × RatCode =>
      ∃ T : Finset (Fin (atomCount (atomList v.1))),
      ∃ S : Finset (Fin (atomCount (atomList v.2.1))),
        (∀ j, j ∉ S → ∀ i ∈ T,
          (ratOfCode v.2.2 : ℝ) < dist (atomPt P v.2.1 j) (atomPt P v.1 i))
          ∧ (∑ j ∈ S, atomWtR v.2.1 j) + (ratOfCode v.2.2 : ℝ) < ∑ i ∈ T, atomWtR v.1 i := by
  -- level-4 input: ((((v, tT), tS), j), i), exactly as in `repred_strictFinCondAtomic`
  have hproj_v : Primrec fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ => u.1.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  have hg : Computable fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
      ((natAtomIdx u.1.1.1.1.2.1 u.1.2, natAtomIdx u.1.1.1.1.1 u.2, u.1.1.1.1.2.2) :
        ℕ × ℕ × RatCode) :=
    ((primrec_natAtomIdx.comp (Primrec.fst.comp (Primrec.snd.comp hproj_v))
        (Primrec.snd.comp Primrec.fst)).pair
      ((primrec_natAtomIdx.comp (Primrec.fst.comp hproj_v) Primrec.snd).pair
        (Primrec.snd.comp (Primrec.snd.comp hproj_v)))).to_comp
  -- NOTE: `g` is passed explicitly — with `g` a metavariable the unifier guesses the
  -- spurious projection solution `g := fun u => u.1.1.1.1` from the cast component and
  -- then storms on backtracking (whnf timeout).
  have hatom : REPred fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
      (ratOfCode u.1.1.1.1.2.2 : ℝ)
        < dist (P.dense (natAtomIdx u.1.1.1.1.2.1 u.1.2))
            (P.dense (natAtomIdx u.1.1.1.1.1 u.2)) :=
    repred_comp
      (g := fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
        (natAtomIdx u.1.1.1.1.2.1 u.1.2, natAtomIdx u.1.1.1.1.1 u.2, u.1.1.1.1.2.2))
      P.gtSemidec hg
  have hguard_i : PrimrecPred fun u : ((((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ) × ℕ =>
      ¬ u.1.1.1.2.testBit u.2 = true :=
    (Primrec.eq.comp
      (primrec_testBit.comp
        (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
      (Primrec.const true)).not
  have himp_i := (repred_or (repred_of_primrecPred hguard_i) hatom).of_eq
    fun u => (imp_iff_not_or).symm
  -- bounded ∀ i < k₁
  have hforall_i := repred_forall_lt himp_i
    (primrec_natAtomCount.comp
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))
  -- guard: testBit tS j = false → ...
  have hguard_j : PrimrecPred fun u₃ : (((ℕ × ℕ × RatCode) × ℕ) × ℕ) × ℕ =>
      ¬ u₃.1.2.testBit u₃.2 = false :=
    (Primrec.eq.comp
      (primrec_testBit.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const false)).not
  have himp_j := (repred_or (repred_of_primrecPred hguard_j) hforall_i).of_eq
    fun u₃ => (imp_iff_not_or).symm
  -- bounded ∀ j < k₂
  have hforall_j := repred_forall_lt himp_j
    (primrec_natAtomCount.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
  -- the decidable strict sum condition over ((v, tT), tS)
  have hm₁' : Primrec fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ => u₂.1.1.1 :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hm₂' : Primrec fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ => u₂.1.1.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hc' : Primrec fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ => u₂.1.1.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hA : PrimrecPred fun u₂ : ((ℕ × ℕ × RatCode) × ℕ) × ℕ =>
      ratOfCode (ratAddCode (maskWtSumCode u₂.1.1.2.1 (natAtomCount u₂.1.1.2.1) u₂.2)
          u₂.1.1.2.2)
        < ratOfCode (maskWtSumCode u₂.1.1.1 (natAtomCount u₂.1.1.1) u₂.1.2) :=
    primrecPred_ratLt
      (primrec_ratAddCode.comp
        (primrec_maskWtSumCode.comp
          (hm₂'.pair ((primrec_natAtomCount.comp hm₂').pair Primrec.snd)))
        hc')
      (primrec_maskWtSumCode.comp
        (hm₁'.pair ((primrec_natAtomCount.comp hm₁').pair (Primrec.snd.comp Primrec.fst))))
  have hbody := repred_and (repred_of_primrecPred hA) hforall_j
  -- bounded ∃ tS < 2 ^ k₂, then bounded ∃ tT < 2 ^ k₁
  have hex_tS := repred_exists_lt hbody
    (primrec_pow2.comp
      (primrec_natAtomCount.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  have hex_tT := repred_exists_lt hex_tS
    (primrec_pow2.comp (primrec_natAtomCount.comp Primrec.fst))
  exact hex_tT.of_eq fun v => gtCert_atomic_iff_coded P v.1 v.2.1 v.2.2

/-- **Semidecidability of `dist < q` on decoded atomics.**  By `dist_atomic_lt_iff`,
the comparison is an `∃ δ' : ℚ` search over the two strict finite conditions;
`ratOfCode` surjectivity turns the rational search into an ℕ-code search
(`repred_exists_nat`), the threshold comparisons are decidable cross-multiplication
`PrimrecPred`s, and each strict finite condition is Σ₁ by
`repred_strictFinCondAtomic`. -/
private theorem ltSemidec_atomic : REPred fun w : ℕ × ℕ × RatCode =>
    dist (LevyProkhorov.ofMeasure (atomic P w.1) : LevyProkhorov (ProbabilityMeasure X))
      (LevyProkhorov.ofMeasure (atomic P w.2.1)) < (ratOfCode w.2.2 : ℝ) := by
  have hd : REPred fun u : (ℕ × ℕ × RatCode) × ℕ =>
      0 ≤ ratOfCode u.2 ∧ ratOfCode u.2 < ratOfCode u.1.2.2 :=
    repred_of_primrecPred
      (PrimrecPred.and
        (((primrecPred_ratLt Primrec.snd (Primrec.const zeroCode)).not).of_eq fun u => by
          rw [ratOfCode_zeroCode, not_lt])
        (primrecPred_ratLt Primrec.snd (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hg₁₂ : Computable fun u : (ℕ × ℕ × RatCode) × ℕ =>
      ((u.1.1, u.1.2.1, u.2) : ℕ × ℕ × RatCode) :=
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to_comp
  have hg₂₁ : Computable fun u : (ℕ × ℕ × RatCode) × ℕ =>
      ((u.1.2.1, u.1.1, u.2) : ℕ × ℕ × RatCode) :=
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to_comp
  have h₁₂ := repred_comp (repred_strictFinCondAtomic P) hg₁₂
  have h₂₁ := repred_comp (repred_strictFinCondAtomic P) hg₂₁
  refine (repred_exists_nat (repred_and hd (repred_and h₁₂ h₂₁))).of_eq fun w => ?_
  rw [dist_atomic_lt_iff]
  constructor
  · rintro ⟨d, ⟨hd0, hdt⟩, hf1, hf2⟩
    exact ⟨ratOfCode d, hd0, by exact_mod_cast hdt, hf1, hf2⟩
  · rintro ⟨δ', hδ0, hδt, hf1, hf2⟩
    obtain ⟨d, rfl⟩ := ratOfCode_surjective δ'
    exact ⟨d, ⟨hδ0, by exact_mod_cast hδt⟩, hf1, hf2⟩

/-- **Semidecidability of `q < dist` on decoded atomics.**  By `lt_dist_atomic_iff`,
the comparison is a two-sided finite violation certificate.  Generically each
`t < dist` atom is only semidecidable (unlike Cantor space's exact dyadic distance
codes), so the certificate is Σ₁, not decidable.  Each side is Σ₁ by `repred_gtCert`;
the two sides are exchanged by the computable swap of the atomic indices. -/
private theorem gtSemidec_atomic : REPred fun w : ℕ × ℕ × RatCode =>
    (ratOfCode w.2.2 : ℝ)
      < dist (LevyProkhorov.ofMeasure (atomic P w.1) : LevyProkhorov (ProbabilityMeasure X))
          (LevyProkhorov.ofMeasure (atomic P w.2.1)) := by
  have hswap : Computable fun w : ℕ × ℕ × RatCode =>
      ((w.2.1, w.1, w.2.2) : ℕ × ℕ × RatCode) :=
    ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).to_comp
  exact (repred_or (repred_gtCert P) (repred_comp (repred_gtCert P) hswap)).of_eq
    fun w => (lt_dist_atomic_iff P w.1 w.2.1 _).symm

/-- **The effective Lévy–Prokhorov presentation** of the weak topology, over the
generic contract `[MetricSpace X] [MeasurableSpace X] [BorelSpace X]` +
`ComputableMetricPresentation X`: dense sequence the decoded rational-atomic measures
(direct Dirac sums); semidecisions through the strict finite Σ₁ characterizations. -/
noncomputable def prokhorovPresentation :
    ComputableMetricPresentation (LevyProkhorov (ProbabilityMeasure X)) where
  dense m := LevyProkhorov.ofMeasure (atomic P m)
  denseRange := denseRange_atomic P
  ltSemidec := ltSemidec_atomic P
  gtSemidec := gtSemidec_atomic P

end Presentation

end ComputableAnalysis
