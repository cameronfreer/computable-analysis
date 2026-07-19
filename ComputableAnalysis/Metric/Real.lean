/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.CauchyRepresentation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.GetD
import Mathlib.Topology.Instances.Rat

/-!
# Represented reals over the coded rationals

The unit 14 presentations instantiated at `ℚ` (the worked incomplete example) and `ℝ`,
both with dense sequence the total surjective decode `ratOfCode`; `realRep` is the fast
Cauchy representation of `ℝ` and `unitIntervalRep` its `[0,1]` subtype restriction.

First-order arithmetic is computable on names: addition, negation, multiplication, and
distance as `ComputableMap`s, plus the `[0,1]` complement `unitSymm`. All realizers are
assembled through `OracleCode.exists_prefixPostCode` from *coded rational arithmetic* —
`Nat.pair` arithmetic on unnormalized fractions `(a - b)/(c + 1)`, never mathlib's
`Encodable`/`Primcodable ℚ` numberings. Multiplication is head-adaptive: the realizer
reads both packed heads to bound the input magnitudes, then bumps the working precision.

The units 22–23 consumers are the two **uniform variable-length folds**: a single total
oracle code realizing finite sums of `Packs`-packed families of real names, and one
realizing finite products of `[0,1]`-valued families (approximants are clamped into
`[0,1]`, where the telescoping estimate `|∏a - ∏b| ≤ ∑|aᵢ - bᵢ|` gives the same
precision bump `n + k` from `k < 2 ^ k`).
-/

namespace ComputableAnalysis

open OracleCode Encodable Denumerable

/-! ### Coded rational arithmetic

Code-level arithmetic on unnormalized fractions: `Nat.pair (Nat.pair a b) c` codes
`(a - b)/(c + 1)`, so every operation is plain `Nat.pair` arithmetic, fully covered by
mathlib's `Primrec` lemmas. -/

section CodedRationalArithmetic

/-- The canonical code of `1` (fraction `(1 - 0)/(0 + 1)`). -/
private def oneCode : ℕ := Nat.pair (Nat.pair 1 0) 0

private theorem ratOfCode_oneCode : ratOfCode oneCode = 1 := by
  simp [ratOfCode, oneCode]

/-- Addition of rational codes: fraction arithmetic without normalization. -/
private def addCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.1 * (m₁.unpair.2 + 1))
      (m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.2 * (m₁.unpair.2 + 1)))
    ((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1)

private theorem ratOfCode_addCode (m₁ m₂ : ℕ) :
    ratOfCode (addCode m₁ m₂) = ratOfCode m₁ + ratOfCode m₂ := by
  have hden : (((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1 : ℕ) : ℚ) + 1
      = ((m₁.unpair.2 : ℚ) + 1) * ((m₂.unpair.2 : ℚ) + 1) := by
    have h1 : 1 ≤ (m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    push_cast [h1]
    ring
  have h₁ : ((m₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((m₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  simp only [ratOfCode, addCode, Nat.unpair_pair, hden]
  field_simp
  push_cast
  ring

/-- Negation of a rational code: swap the numerator slots. -/
private def negCode (m : ℕ) : ℕ :=
  Nat.pair (Nat.pair m.unpair.1.unpair.2 m.unpair.1.unpair.1) m.unpair.2

private theorem ratOfCode_negCode (m : ℕ) : ratOfCode (negCode m) = -ratOfCode m := by
  simp only [ratOfCode, negCode, Nat.unpair_pair]
  rw [← neg_div, neg_sub]

/-- Subtraction of rational codes. -/
private def subCode (m₁ m₂ : ℕ) : ℕ := addCode m₁ (negCode m₂)

private theorem ratOfCode_subCode (m₁ m₂ : ℕ) :
    ratOfCode (subCode m₁ m₂) = ratOfCode m₁ - ratOfCode m₂ := by
  rw [subCode, ratOfCode_addCode, ratOfCode_negCode, sub_eq_add_neg]

/-- Multiplication of rational codes: unnormalized signed-fraction arithmetic,
`(a₁-b₁)(a₂-b₂) = (a₁a₂ + b₁b₂) - (a₁b₂ + a₂b₁)`; no gcd. -/
private def mulCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (m₁.unpair.1.unpair.1 * m₂.unpair.1.unpair.1
        + m₁.unpair.1.unpair.2 * m₂.unpair.1.unpair.2)
      (m₁.unpair.1.unpair.1 * m₂.unpair.1.unpair.2
        + m₁.unpair.1.unpair.2 * m₂.unpair.1.unpair.1))
    ((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1)

private theorem ratOfCode_mulCode (m₁ m₂ : ℕ) :
    ratOfCode (mulCode m₁ m₂) = ratOfCode m₁ * ratOfCode m₂ := by
  have hden : (((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1 : ℕ) : ℚ) + 1
      = ((m₁.unpair.2 : ℚ) + 1) * ((m₂.unpair.2 : ℚ) + 1) := by
    have h1 : 1 ≤ (m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) :=
      Nat.one_le_iff_ne_zero.mpr (by positivity)
    push_cast [h1]
    ring
  have h₁ : ((m₁.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  have h₂ : ((m₂.unpair.2 : ℚ) + 1) ≠ 0 := by positivity
  simp only [ratOfCode, mulCode, Nat.unpair_pair, hden]
  field_simp
  push_cast
  ring

/-- Absolute value of a rational code: negate exactly when the numerator is nonpositive
(the ℕ test `a ≤ b`, since the denominator is positive). -/
private def absCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 then negCode m else m

private theorem ratOfCode_absCode (m : ℕ) : ratOfCode (absCode m) = |ratOfCode m| := by
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  by_cases h : m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2
  · have hab : (m.unpair.1.unpair.1 : ℚ) ≤ (m.unpair.1.unpair.2 : ℚ) := by exact_mod_cast h
    have hq : ratOfCode m ≤ 0 := by
      rw [ratOfCode]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    rw [absCode, if_pos h, ratOfCode_negCode, abs_of_nonpos hq]
  · have hba : (m.unpair.1.unpair.2 : ℚ) ≤ (m.unpair.1.unpair.1 : ℚ) := by
      exact_mod_cast (Nat.lt_of_not_le h).le
    have hq : 0 ≤ ratOfCode m := by
      rw [ratOfCode]
      exact div_nonneg (by linarith) hden.le
    rw [absCode, if_neg h, abs_of_nonneg hq]

/-- Sum of a list of rational codes. -/
private def sumCode (l : List ℕ) : ℕ :=
  l.foldr addCode 0

private theorem ratOfCode_sumCode (l : List ℕ) :
    ratOfCode (sumCode l) = (l.map ratOfCode).sum := by
  induction l with
  | nil =>
    simp only [sumCode, List.foldr_nil, List.map_nil, List.sum_nil]
    simp [ratOfCode]
  | cons a l ih =>
    simp only [sumCode, List.foldr_cons, List.map_cons, List.sum_cons, ratOfCode_addCode]
    rw [← ih]
    rfl

/-- Product of a list of rational codes. -/
private def prodCode (l : List ℕ) : ℕ :=
  l.foldr mulCode oneCode

private theorem ratOfCode_prodCode (l : List ℕ) :
    ratOfCode (prodCode l) = (l.map ratOfCode).prod := by
  induction l with
  | nil =>
    simp only [prodCode, List.foldr_nil, List.map_nil, List.prod_nil]
    exact ratOfCode_oneCode
  | cons a l ih =>
    simp only [prodCode, List.foldr_cons, List.map_cons, List.prod_cons, ratOfCode_mulCode]
    rw [← ih]
    rfl

private theorem primrec_unpairFst : Primrec fun m : ℕ => m.unpair.1 :=
  Primrec.fst.comp Primrec.unpair

private theorem primrec_unpairSnd : Primrec fun m : ℕ => m.unpair.2 :=
  Primrec.snd.comp Primrec.unpair

section PrimrecFacts

open Primrec

private theorem primrec₂_addCode : Primrec₂ addCode := by
  have a₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp fst
  have b₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp fst
  have a₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp snd
  have b₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp snd
  have d₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp fst)
  have d₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp snd)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (nat_add.comp (nat_mul.comp a₁ d₂) (nat_mul.comp a₂ d₁))
      (nat_add.comp (nat_mul.comp b₁ d₂) (nat_mul.comp b₂ d₁)))
    (nat_sub.comp (nat_mul.comp d₁ d₂) (const 1))

private theorem primrec_negCode : Primrec negCode :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (primrec_unpairSnd.comp primrec_unpairFst)
      (primrec_unpairFst.comp primrec_unpairFst))
    primrec_unpairSnd

private theorem primrec₂_subCode : Primrec₂ subCode :=
  primrec₂_addCode.comp fst (primrec_negCode.comp snd)

private theorem primrec₂_mulCode : Primrec₂ mulCode := by
  have a₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp fst
  have b₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp fst
  have a₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.1 :=
    (primrec_unpairFst.comp primrec_unpairFst).comp snd
  have b₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.1.unpair.2 :=
    (primrec_unpairSnd.comp primrec_unpairFst).comp snd
  have d₁ : Primrec fun p : ℕ × ℕ => p.1.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp fst)
  have d₂ : Primrec fun p : ℕ × ℕ => p.2.unpair.2 + 1 :=
    succ.comp (primrec_unpairSnd.comp snd)
  exact Primrec₂.natPair.comp
    (Primrec₂.natPair.comp
      (nat_add.comp (nat_mul.comp a₁ a₂) (nat_mul.comp b₁ b₂))
      (nat_add.comp (nat_mul.comp a₁ b₂) (nat_mul.comp b₁ a₂)))
    (nat_sub.comp (nat_mul.comp d₁ d₂) (const 1))

private theorem primrec_absCode : Primrec absCode := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  exact Primrec.ite (Primrec.nat_le.comp ha hb) primrec_negCode Primrec.id

private theorem primrec_sumCode : Primrec sumCode :=
  (list_foldr Primrec.id (const 0)
    (primrec₂_addCode.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun _ => rfl

private theorem primrec_prodCode : Primrec prodCode :=
  (list_foldr Primrec.id (const oneCode)
    (primrec₂_mulCode.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun _ => rfl

end PrimrecFacts

end CodedRationalArithmetic

/-! ### Semidecidable code comparisons

Strict comparison of coded rationals is a *decidable* ℕ comparison of cross-multiplied
unnormalized fractions (denominators are positive), hence primitive recursive, hence
recursively enumerable — the uniform semidecisions demanded by convention 7. -/

section SemidecidableComparisons

end SemidecidableComparisons

/-! ### The presentations and representations -/

/-- The rationals presented over the coded rationals: the dense sequence is the total
surjective decode `ratOfCode`, and both threshold comparisons are semidecided through
the decidable ℕ cross-multiplication comparison. The worked *incomplete* example. -/
def rationalPresentation : ComputableMetricPresentation ℚ where
  dense := ratOfCode
  denseRange := ratOfCode_surjective.denseRange
  ltSemidec := repred_of_ratLt
    (primrec_absCode.comp (primrec₂_subCode.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)
    fun w => by
      rw [Rat.dist_eq, ratOfCode_absCode, ratOfCode_subCode]
      exact_mod_cast Iff.rfl
  gtSemidec := repred_of_ratLt (Primrec.snd.comp Primrec.snd)
    (primrec_absCode.comp (primrec₂_subCode.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    fun w => by
      rw [Rat.dist_eq, ratOfCode_absCode, ratOfCode_subCode]
      exact_mod_cast Iff.rfl

/-- The reals presented over the coded rationals: the dense sequence is the cast of
`ratOfCode`, dense by `Rat.denseRange_cast`; the semidecisions are the same decidable
rational comparisons as for `rationalPresentation`, dropped from `ℝ` to `ℚ` by
cast strict monotonicity. -/
def realPresentation : ComputableMetricPresentation ℝ where
  dense := fun m => ((ratOfCode m : ℚ) : ℝ)
  denseRange := by
    unfold DenseRange
    rw [Set.range_comp' ((↑) : ℚ → ℝ) ratOfCode, ratOfCode_surjective.range_eq,
      Set.image_univ]
    exact Rat.denseRange_cast
  ltSemidec := repred_of_ratLt
    (primrec_absCode.comp (primrec₂_subCode.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)
    fun w => by
      rw [Real.dist_eq, ratOfCode_absCode, ratOfCode_subCode]
      exact_mod_cast Iff.rfl
  gtSemidec := repred_of_ratLt (Primrec.snd.comp Primrec.snd)
    (primrec_absCode.comp (primrec₂_subCode.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
    fun w => by
      rw [Real.dist_eq, ratOfCode_absCode, ratOfCode_subCode]
      exact_mod_cast Iff.rfl

/-- The represented reals: the fast Cauchy representation over `realPresentation`. -/
noncomputable def realRep : Representation ℝ := realPresentation.cauchyRep

/-- The represented unit interval: `realRep` restricted to `[0,1]` — the value space of
units 20–23. No totalization: a name of a real outside `[0,1]` denotes nothing here. -/
noncomputable def unitIntervalRep : Representation (Set.Icc (0 : ℝ) 1) :=
  realRep.subtype _

/-! ### Names bridge

`realRep`-names unpacked once into the concrete rational-approximation form used by all
the realizer estimates below. -/

section NamesBridge

/-- Names of `realRep` are exactly the fast rational approximation streams. -/
private theorem realRep_names_iff {p : Baire} {x : ℝ} :
    realRep.Names p x ↔
      ∀ n : ℕ, |((ratOfCode (p n) : ℚ) : ℝ) - x| ≤ (2 : ℝ)⁻¹ ^ n := by
  refine Iff.trans realPresentation.cauchyRep_names_iff ?_
  constructor
  · intro h n
    have hn := h n
    rw [Real.dist_eq] at hn
    exact hn
  · intro h n
    rw [Real.dist_eq]
    exact h n

/-- Names of `unitIntervalRep` are exactly the `realRep`-names of the underlying real. -/
private theorem unitIntervalRep_names_iff {p : Baire} {s : Set.Icc (0 : ℝ) 1} :
    unitIntervalRep.Names p s ↔ realRep.Names p s.val :=
  Representation.subtype_names_iff

/-- Extracting a coordinate from a decoded stream prefix. -/
private theorem streamTake_getD (p : Baire) {j m : ℕ} (h : j < m) :
    (streamTake p m).getD j 0 = p j := by
  rw [List.getD_eq_getElem _ _ (by rw [length_streamTake]; exact h), getElem_streamTake]

end NamesBridge

/-! ### Computable points -/

/-- `0` is a computable point of the represented reals: the constant stream at the
canonical zero code `Nat.pair (Nat.pair 0 0) 0` is a computable name. -/
theorem computablePoint_realZero : realRep.ComputablePoint 0 := by
  refine ⟨fun _ => zeroCode, Computable.const zeroCode, realRep_names_iff.mpr fun n => ?_⟩
  rw [ratOfCode_zeroCode]
  simp

/-- `1` is a computable point of the represented reals: the constant stream at the
canonical one code `Nat.pair (Nat.pair 1 0) 0` is a computable name. -/
theorem computablePoint_realOne : realRep.ComputablePoint 1 := by
  refine ⟨fun _ => oneCode, Computable.const oneCode, realRep_names_iff.mpr fun n => ?_⟩
  rw [ratOfCode_oneCode]
  simp

/-! ### Realizer assembly

Coordinatewise and pairwise code-level operations lift to total stream operators through
`OracleCode.exists_prefixPostCode`. -/

section RealizerAssembly

/-- A primrec unary code operation applied coordinatewise is a total computed stream
operator. -/
private theorem computes_unaryOp {op : ℕ → ℕ} (hop : Primrec op) :
    ∃ c : OracleCode, c.Computes fun p n => op (p n) := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode (b := fun n _ => n + 1)
    (g := fun w => op ((ofNat (List ℕ) w.unpair.2).getD w.unpair.1 0))
    (Primrec.succ.comp Primrec.fst)
    (hop.comp ((Primrec.list_getD 0).comp
      ((Primrec.ofNat (List ℕ)).comp (primrec_unpairSnd))
      (primrec_unpairFst)))
  refine ⟨c, fun p n => ?_⟩
  rw [hc p n]
  simp only [Nat.unpair_pair, ofNat_encode, streamTake_getD p (Nat.lt_succ_self n)]

/-- A primrec binary code operation applied to the interleaved coordinates at bumped
precision `n + 1` is a total computed stream operator. -/
private theorem computes_binaryOp {op : ℕ → ℕ → ℕ} (hop : Primrec₂ op) :
    ∃ c : OracleCode,
      c.Computes fun p n => op (p (2 * (n + 1))) (p (2 * (n + 1) + 1)) := by
  have hL : Primrec fun w : ℕ => ofNat (List ℕ) w.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd
  have hidx : Primrec fun w : ℕ => 2 * (w.unpair.1 + 1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp primrec_unpairFst)
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode (b := fun n _ => 2 * n + 4)
    (g := fun w => op ((ofNat (List ℕ) w.unpair.2).getD (2 * (w.unpair.1 + 1)) 0)
      ((ofNat (List ℕ) w.unpair.2).getD (2 * (w.unpair.1 + 1) + 1) 0))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
      (Primrec.const 4))
    (hop.comp ((Primrec.list_getD 0).comp hL hidx)
      ((Primrec.list_getD 0).comp hL (Primrec.succ.comp hidx)))
  refine ⟨c, fun p n => ?_⟩
  rw [hc p n]
  simp only [Nat.unpair_pair, ofNat_encode,
    streamTake_getD p (by omega : 2 * (n + 1) < 2 * n + 4),
    streamTake_getD p (by omega : 2 * (n + 1) + 1 < 2 * n + 4)]

end RealizerAssembly

/-! ### Clamped approximation lemmas

The `[0,1]` fold machinery — kept separate from arbitrary-real multiplication. Also home
of the shared precision bump `k · 2⁻⁽ⁿ⁺ᵏ⁾ ≤ 2⁻ⁿ` and the list/`Fin` fold bridges. -/

section ClampedApproximation

/-- Clamp a rational code into `[0,1]`: the sign/threshold tests on the unnormalized
fraction `(a - b)/(c + 1)` are the ℕ comparisons `a ≤ b` (value `≤ 0`) and
`b + c + 1 ≤ a` (value `≥ 1`), since `c + 1 > 0`. -/
private def clampCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 then zeroCode
  else if m.unpair.1.unpair.2 + m.unpair.2 + 1 ≤ m.unpair.1.unpair.1 then oneCode
  else m

private theorem ratOfCode_clampCode (m : ℕ) :
    ratOfCode (clampCode m) = max 0 (min 1 (ratOfCode m)) := by
  have hden : (0 : ℚ) < (m.unpair.2 : ℚ) + 1 := by positivity
  by_cases h1 : m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2
  · have hab : (m.unpair.1.unpair.1 : ℚ) ≤ (m.unpair.1.unpair.2 : ℚ) := by exact_mod_cast h1
    have hr : ratOfCode m ≤ 0 := by
      unfold ratOfCode
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    rw [clampCode, if_pos h1, ratOfCode_zeroCode, eq_comm,
      max_eq_left ((min_le_right _ _).trans hr)]
  · by_cases h2 : m.unpair.1.unpair.2 + m.unpair.2 + 1 ≤ m.unpair.1.unpair.1
    · have hcast : (m.unpair.1.unpair.2 : ℚ) + (m.unpair.2 : ℚ) + 1
          ≤ (m.unpair.1.unpair.1 : ℚ) := by exact_mod_cast h2
      have hr : 1 ≤ ratOfCode m := by
        unfold ratOfCode
        rw [le_div_iff₀ hden]
        linarith
      rw [clampCode, if_neg h1, if_pos h2, ratOfCode_oneCode, eq_comm,
        min_eq_left hr, max_eq_right zero_le_one]
    · have hba : (m.unpair.1.unpair.2 : ℚ) ≤ (m.unpair.1.unpair.1 : ℚ) := by
        exact_mod_cast (Nat.lt_of_not_le h1).le
      have hac : (m.unpair.1.unpair.1 : ℚ)
          ≤ (m.unpair.1.unpair.2 : ℚ) + (m.unpair.2 : ℚ) := by
        exact_mod_cast Nat.lt_succ_iff.mp (Nat.lt_of_not_le h2)
      have hr0 : 0 ≤ ratOfCode m := by
        unfold ratOfCode
        exact div_nonneg (by linarith) hden.le
      have hr1 : ratOfCode m ≤ 1 := by
        unfold ratOfCode
        rw [div_le_one hden]
        linarith
      rw [clampCode, if_neg h1, if_neg h2, eq_comm, min_eq_right hr1, max_eq_right hr0]

private theorem primrec_clampCode : Primrec clampCode := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  exact Primrec.ite (Primrec.nat_le.comp ha hb) (Primrec.const zeroCode)
    (Primrec.ite
      (Primrec.nat_le.comp
        (Primrec.succ.comp (Primrec.nat_add.comp hb primrec_unpairSnd)) ha)
      (Primrec.const oneCode) Primrec.id)

/-- The clamped value lies in `[0,1]`. -/
private theorem clamp_mem_Icc (r : ℝ) : max 0 (min 1 r) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

/-- Clamping fixes points of `[0,1]`. -/
private theorem clamp_eq_self {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    max 0 (min 1 x) = x := by
  rw [min_eq_right hx.2, max_eq_right hx.1]

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

/-- Products of `[0,1]`-families stay in `[0,1]`. -/
private theorem prod_mem_Icc {k : ℕ} (a : Fin k → ℝ)
    (ha : ∀ i, a i ∈ Set.Icc (0 : ℝ) 1) : (∏ i, a i) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Finset.prod_nonneg fun i _ => (ha i).1,
    Finset.prod_le_one (fun i _ => (ha i).1) fun i _ => (ha i).2⟩

/-- **Telescoping product estimate** (not in mathlib as of this pin): for families in
`[0,1]`, `|∏aᵢ - ∏bᵢ| ≤ ∑|aᵢ - bᵢ|`. -/
private theorem abs_prod_sub_prod_le :
    ∀ {k : ℕ} (a b : Fin k → ℝ), (∀ i, a i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, b i ∈ Set.Icc (0 : ℝ) 1) → |∏ i, a i - ∏ i, b i| ≤ ∑ i, |a i - b i| := by
  intro k
  induction k with
  | zero => intro a b _ _; simp
  | succ k ih =>
    intro a b ha hb
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.sum_univ_succ]
    have hBm : (∏ i : Fin k, b i.succ) ∈ Set.Icc (0 : ℝ) 1 :=
      prod_mem_Icc _ fun i => hb i.succ
    have ha0 : |a 0| ≤ 1 := abs_le.mpr ⟨by linarith [(ha 0).1], (ha 0).2⟩
    have hBabs : |∏ i : Fin k, b i.succ| ≤ 1 := abs_le.mpr ⟨by linarith [hBm.1], hBm.2⟩
    have hihs : |∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ|
        ≤ ∑ i : Fin k, |a i.succ - b i.succ| :=
      ih _ _ (fun i => ha i.succ) fun i => hb i.succ
    calc |a 0 * ∏ i : Fin k, a i.succ - b 0 * ∏ i : Fin k, b i.succ|
        = |a 0 * (∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ)
            + (a 0 - b 0) * ∏ i : Fin k, b i.succ| := by
          congr 1
          ring
      _ ≤ |a 0 * (∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ)|
            + |(a 0 - b 0) * ∏ i : Fin k, b i.succ| := abs_add_le _ _
      _ = |a 0| * |∏ i : Fin k, a i.succ - ∏ i : Fin k, b i.succ|
            + |a 0 - b 0| * |∏ i : Fin k, b i.succ| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (∑ i : Fin k, |a i.succ - b i.succ|) + |a 0 - b 0| * 1 := by
          gcongr
      _ = |a 0 - b 0| + ∑ i : Fin k, |a i.succ - b i.succ| := by ring

/-- The precision bump: `k · 2⁻⁽ⁿ⁺ᵏ⁾ ≤ 2⁻ⁿ`, from `k < 2 ^ k`. -/
private theorem bump (k n : ℕ) : (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) ≤ (2 : ℝ)⁻¹ ^ n := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have h1 : (k : ℝ) * (2 : ℝ)⁻¹ ^ k ≤ 1 := by
    rw [inv_pow, ← div_eq_mul_inv, div_le_one (by positivity)]
    exact hk
  calc (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k)
      = ((k : ℝ) * (2 : ℝ)⁻¹ ^ k) * (2 : ℝ)⁻¹ ^ n := by rw [pow_add]; ring
    _ ≤ 1 * (2 : ℝ)⁻¹ ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 : ℝ)⁻¹ ^ n := one_mul _

/-- List sum over `List.range` as a `Fin` sum. -/
private theorem listSum_range_map {M : Type*} [AddCommMonoid M] (f : ℕ → M) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i : Fin k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, Fin.sum_univ_castSucc, ih]
    simp

/-- List product over `List.range` as a `Fin` product. -/
private theorem listProd_range_map {M : Type*} [CommMonoid M] (f : ℕ → M) (k : ℕ) :
    ((List.range k).map f).prod = ∏ i : Fin k, f i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, Fin.prod_univ_castSucc, ih]
    simp

end ClampedApproximation

/-! ### Arithmetic on represented reals -/

section Arithmetic

/-- Addition of represented reals is computable: add the rational codes at precision
`n + 1`, so the two `2⁻⁽ⁿ⁺¹⁾` errors sum to `2⁻ⁿ`. -/
theorem computableMap_realAdd :
    ComputableMap (realRep.prod realRep) realRep fun p => p.1 + p.2 := by
  obtain ⟨c, hc⟩ := computes_binaryOp primrec₂_addCode
  refine ⟨c, .of_computes hc fun p ab hab => ?_⟩
  obtain ⟨hx, hy⟩ := Representation.prod_names_iff.mp hab
  rw [realRep_names_iff] at hx hy
  simp only [Baire.evenPart_apply] at hx
  simp only [Baire.oddPart_apply] at hy
  refine realRep_names_iff.mpr fun n => ?_
  have hcast : ((ratOfCode (addCode (p (2 * (n + 1))) (p (2 * (n + 1) + 1))) : ℚ) : ℝ)
      = ((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ)
        + ((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ) := by
    rw [ratOfCode_addCode]
    push_cast
    ring
  simp only [hcast]
  calc |((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ)
        + ((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ) - (ab.1 + ab.2)|
      = |(((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ) - ab.1)
          + (((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ) - ab.2)| := by
        congr 1
        ring
    _ ≤ |((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ) - ab.1|
          + |((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ) - ab.2| := abs_add_le _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (n + 1) + (2 : ℝ)⁻¹ ^ (n + 1) := add_le_add (hx (n + 1)) (hy (n + 1))
    _ = (2 : ℝ)⁻¹ ^ n := by
        rw [pow_succ]
        ring

/-- Negation of represented reals is computable: negate each rational code (an isometry,
so the precision is unchanged). -/
theorem computableMap_realNeg : ComputableMap realRep realRep Neg.neg := by
  obtain ⟨c, hc⟩ := computes_unaryOp primrec_negCode
  refine ⟨c, .of_computes hc fun p x hpx => ?_⟩
  rw [realRep_names_iff] at hpx
  refine realRep_names_iff.mpr fun n => ?_
  have hcast : ((ratOfCode (negCode (p n)) : ℚ) : ℝ) = -((ratOfCode (p n) : ℚ) : ℝ) := by
    rw [ratOfCode_negCode]
    push_cast
    ring
  simp only [hcast]
  have hsplit : -((ratOfCode (p n) : ℚ) : ℝ) - -x
      = -(((ratOfCode (p n) : ℚ) : ℝ) - x) := by ring
  rw [hsplit, abs_neg]
  exact hpx n

/-! #### Head-adaptive multiplication

Multiplication needs magnitude bounds on *both* inputs before the working precision can
be chosen. The realizer therefore precomposes a reindexing code packing both heads into
coordinate `0`, reads the packed heads to compute the precision bump, and multiplies the
rational codes of the original streams at the bumped precision. This section never
mentions clamping — a deliberate guardrail separating it from the `[0,1]` fold. -/

/-- Nat-level magnitude bound of a code: `|ratOfCode m| + 1 ≤ magCode m`. -/
private def magCode (m : ℕ) : ℕ := m.unpair.1.unpair.1 + m.unpair.1.unpair.2 + 1

private theorem primrec_magCode : Primrec magCode :=
  Primrec.succ.comp (Primrec.nat_add.comp (primrec_unpairFst.comp primrec_unpairFst)
    (primrec_unpairSnd.comp primrec_unpairFst))

/-- Any real within `1` of the rational coded by `m` has magnitude at most `magCode m`. -/
private theorem abs_le_magCode {m : ℕ} {x : ℝ}
    (h : |((ratOfCode m : ℚ) : ℝ) - x| ≤ 1) : |x| ≤ (magCode m : ℝ) := by
  have hq : |(ratOfCode m : ℚ)|
      ≤ (m.unpair.1.unpair.1 : ℚ) + (m.unpair.1.unpair.2 : ℚ) := by
    rw [ratOfCode, abs_div, abs_of_pos (by positivity : (0 : ℚ) < (m.unpair.2 : ℚ) + 1)]
    refine (div_le_self (abs_nonneg _) ?_).trans ?_
    · have : (0 : ℚ) ≤ (m.unpair.2 : ℚ) := Nat.cast_nonneg _
      linarith
    · calc |(m.unpair.1.unpair.1 : ℚ) - (m.unpair.1.unpair.2 : ℚ)|
          ≤ |(m.unpair.1.unpair.1 : ℚ)| + |(m.unpair.1.unpair.2 : ℚ)| := abs_sub _ _
        _ = (m.unpair.1.unpair.1 : ℚ) + (m.unpair.1.unpair.2 : ℚ) := by
            rw [Nat.abs_cast, Nat.abs_cast]
  have hqR : |((ratOfCode m : ℚ) : ℝ)|
      ≤ (m.unpair.1.unpair.1 : ℝ) + (m.unpair.1.unpair.2 : ℝ) := by
    rw [← Rat.cast_abs]
    exact_mod_cast hq
  have hx : |x| - |((ratOfCode m : ℚ) : ℝ)| ≤ |x - ((ratOfCode m : ℚ) : ℝ)| :=
    abs_sub_abs_le_abs_sub _ _
  rw [abs_sub_comm] at hx
  unfold magCode
  push_cast
  linarith

/-- The product estimate: approximants within `ε ≤ 1` of magnitude-bounded reals multiply
to within `(Mx + My + 2) · ε`. -/
private theorem abs_mul_sub_mul_le {q₁ q₂ x y ε Mx My : ℝ} (hε1 : ε ≤ 1)
    (h₁ : |q₁ - x| ≤ ε) (h₂ : |q₂ - y| ≤ ε) (hx : |x| ≤ Mx) (hy : |y| ≤ My) :
    |q₁ * q₂ - x * y| ≤ (Mx + My + 2) * ε := by
  have hε0 : (0 : ℝ) ≤ ε := (abs_nonneg _).trans h₁
  have hMy : (0 : ℝ) ≤ My := (abs_nonneg _).trans hy
  have hq₁ : |q₁| ≤ Mx + 1 := by
    calc |q₁| = |x + (q₁ - x)| := by
          congr 1
          ring
      _ ≤ |x| + |q₁ - x| := abs_add_le _ _
      _ ≤ Mx + 1 := add_le_add hx (h₁.trans hε1)
  calc |q₁ * q₂ - x * y|
      = |q₁ * (q₂ - y) + (q₁ - x) * y| := by
        congr 1
        ring
    _ ≤ |q₁ * (q₂ - y)| + |(q₁ - x) * y| := abs_add_le _ _
    _ = |q₁| * |q₂ - y| + |q₁ - x| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ (Mx + 1) * ε + ε * My := by
        have hMx : (0 : ℝ) ≤ Mx := (abs_nonneg x).trans hx
        exact add_le_add (mul_le_mul hq₁ h₂ (abs_nonneg _) (by linarith))
          (mul_le_mul h₁ hy (abs_nonneg _) hε0)
    _ ≤ (Mx + My + 2) * ε := by nlinarith

/-- The precision bump for multiplication, computed from the packed heads. -/
private def mulPrec (n h : ℕ) : ℕ := n + (magCode h.unpair.1 + magCode h.unpair.2 + 2)

private theorem primrec₂_mulPrec : Primrec₂ mulPrec :=
  Primrec.nat_add.comp Primrec.fst
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp (primrec_magCode.comp (primrec_unpairFst.comp Primrec.snd))
        (primrec_magCode.comp (primrec_unpairSnd.comp Primrec.snd)))
      (Primrec.const 2))

/-- The head-packing stream operator: coordinate `0` carries both original heads,
coordinate `m + 1` carries the original coordinate `m`. -/
private def mulHeads (p : Baire) : Baire := fun m =>
  if m = 0 then Nat.pair (p 0) (p 1) else p (m - 1)

private theorem mulHeads_apply_ne_zero (p : Baire) {j : ℕ} (h : j ≠ 0) :
    mulHeads p j = p (j - 1) := by
  unfold mulHeads
  rw [if_neg h]

/-- Oracle-free postprocessor for the head-packing reindexer. -/
private def mulReindexPost (w : ℕ) : ℕ :=
  if w.unpair.1 = 0 then
    Nat.pair ((ofNat (List ℕ) w.unpair.2).getD 0 0) ((ofNat (List ℕ) w.unpair.2).getD 1 0)
  else (ofNat (List ℕ) w.unpair.2).getD (w.unpair.1 - 1) 0

private theorem primrec_mulReindexPost : Primrec mulReindexPost := by
  have hL : Primrec fun w : ℕ => ofNat (List ℕ) w.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd
  exact Primrec.ite (Primrec.eq.comp primrec_unpairFst (Primrec.const 0))
    (Primrec₂.natPair.comp ((Primrec.list_getD 0).comp hL (Primrec.const 0))
      ((Primrec.list_getD 0).comp hL (Primrec.const 1)))
    ((Primrec.list_getD 0).comp hL
      (Primrec.nat_sub.comp primrec_unpairFst (Primrec.const 1)))

/-- The head-packing reindexer is a total computed stream operator. -/
private theorem exists_mulHeadsCode : ∃ R : OracleCode, R.Computes mulHeads := by
  obtain ⟨R, hR⟩ := OracleCode.exists_prefixPostCode (b := fun n _ => n + 2)
    (g := mulReindexPost)
    (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)) primrec_mulReindexPost
  refine ⟨R, fun p n => ?_⟩
  rw [hR p n]
  unfold mulReindexPost mulHeads
  simp only [Nat.unpair_pair, ofNat_encode]
  by_cases h : n = 0
  · subst h
    rw [if_pos rfl, if_pos rfl, streamTake_getD p (by omega : (0 : ℕ) < 0 + 2),
      streamTake_getD p (by omega : (1 : ℕ) < 0 + 2)]
  · have hlt : n - 1 < n + 2 := by omega
    rw [if_neg h, if_neg h, streamTake_getD p hlt]

/-- Oracle-free postprocessor for multiplication over the head-packed stream. -/
private def mulPost (w : ℕ) : ℕ :=
  mulCode
    ((ofNat (List ℕ) w.unpair.2).getD
      (2 * mulPrec w.unpair.1 ((ofNat (List ℕ) w.unpair.2).getD 0 0) + 1) 0)
    ((ofNat (List ℕ) w.unpair.2).getD
      (2 * mulPrec w.unpair.1 ((ofNat (List ℕ) w.unpair.2).getD 0 0) + 2) 0)

private theorem primrec_mulPost : Primrec mulPost := by
  have hL : Primrec fun w : ℕ => ofNat (List ℕ) w.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd
  have hi1 : Primrec fun w : ℕ =>
      2 * mulPrec w.unpair.1 ((ofNat (List ℕ) w.unpair.2).getD 0 0) + 1 :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (primrec₂_mulPrec.comp primrec_unpairFst
        ((Primrec.list_getD 0).comp hL (Primrec.const 0))))
  exact primrec₂_mulCode.comp ((Primrec.list_getD 0).comp hL hi1)
    ((Primrec.list_getD 0).comp hL (Primrec.succ.comp hi1))

/-- Multiplication of represented reals is computable. The realizer is head-adaptive: a
reindexing code packs both heads into coordinate `0`, the main code reads them to bound
the input magnitudes and bump the working precision, and the composite (by oracle
substitution) stays total on all streams. -/
theorem computableMap_realMul :
    ComputableMap (realRep.prod realRep) realRep fun p => p.1 * p.2 := by
  obtain ⟨R, hR⟩ := exists_mulHeadsCode
  obtain ⟨Mc, hMc⟩ := OracleCode.exists_prefixPostCode
    (b := fun n h => 2 * mulPrec n h + 3) (g := mulPost)
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) primrec₂_mulPrec) (Primrec.const 3))
    primrec_mulPost
  have hcomp : (Mc.subst R).Computes fun p n =>
      mulPost (Nat.pair n (encode (streamTake (mulHeads p)
        (2 * mulPrec n (mulHeads p 0) + 3)))) := by
    intro p n
    rw [OracleCode.eval_subst hR Mc p]
    exact hMc (mulHeads p) n
  refine ⟨Mc.subst R, .of_computes hcomp fun p ab hab => ?_⟩
  obtain ⟨hx, hy⟩ := Representation.prod_names_iff.mp hab
  rw [realRep_names_iff] at hx hy
  simp only [Baire.evenPart_apply] at hx
  simp only [Baire.oddPart_apply] at hy
  have hmagx : |ab.1| ≤ (magCode (p 0) : ℝ) := by
    have h0 := hx 0
    rw [Nat.mul_zero, pow_zero] at h0
    exact abs_le_magCode h0
  have hmagy : |ab.2| ≤ (magCode (p 1) : ℝ) := by
    have h0 := hy 0
    rw [Nat.mul_zero, Nat.zero_add, pow_zero] at h0
    exact abs_le_magCode h0
  refine realRep_names_iff.mpr fun n => ?_
  have hs0 : mulHeads p 0 = Nat.pair (p 0) (p 1) := rfl
  have hval : mulPost (Nat.pair n (encode (streamTake (mulHeads p)
        (2 * mulPrec n (mulHeads p 0) + 3))))
      = mulCode (p (2 * mulPrec n (Nat.pair (p 0) (p 1))))
          (p (2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1)) := by
    unfold mulPost
    simp only [Nat.unpair_pair, ofNat_encode]
    rw [streamTake_getD (mulHeads p)
      (by omega : (0 : ℕ) < 2 * mulPrec n (mulHeads p 0) + 3)]
    rw [hs0]
    have hlt1 : 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1
        < 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 3 := by omega
    have hlt2 : 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 2
        < 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 3 := by omega
    rw [streamTake_getD (mulHeads p) hlt1, streamTake_getD (mulHeads p) hlt2]
    have hne1 : 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1 ≠ 0 := by omega
    have hne2 : 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 2 ≠ 0 := by omega
    rw [mulHeads_apply_ne_zero p hne1, mulHeads_apply_ne_zero p hne2]
    have he1 : 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1 - 1
        = 2 * mulPrec n (Nat.pair (p 0) (p 1)) := by omega
    have he2 : 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 2 - 1
        = 2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1 := by omega
    rw [he1, he2]
  have hcast : ((ratOfCode (mulCode (p (2 * mulPrec n (Nat.pair (p 0) (p 1))))
        (p (2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1))) : ℚ) : ℝ)
      = ((ratOfCode (p (2 * mulPrec n (Nat.pair (p 0) (p 1)))) : ℚ) : ℝ)
        * ((ratOfCode (p (2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1)) : ℚ) : ℝ) := by
    rw [ratOfCode_mulCode]
    push_cast
    ring
  simp only [hval, hcast]
  have hK : mulPrec n (Nat.pair (p 0) (p 1))
      = n + (magCode (p 0) + magCode (p 1) + 2) := by
    unfold mulPrec
    rw [Nat.unpair_pair]
  calc |((ratOfCode (p (2 * mulPrec n (Nat.pair (p 0) (p 1)))) : ℚ) : ℝ)
        * ((ratOfCode (p (2 * mulPrec n (Nat.pair (p 0) (p 1)) + 1)) : ℚ) : ℝ)
        - ab.1 * ab.2|
      ≤ ((magCode (p 0) : ℝ) + (magCode (p 1) : ℝ) + 2)
          * (2 : ℝ)⁻¹ ^ mulPrec n (Nat.pair (p 0) (p 1)) :=
        abs_mul_sub_mul_le (pow_le_one₀ (by norm_num) (by norm_num))
          (hx (mulPrec n (Nat.pair (p 0) (p 1)))) (hy (mulPrec n (Nat.pair (p 0) (p 1))))
          hmagx hmagy
    _ = ((magCode (p 0) + magCode (p 1) + 2 : ℕ) : ℝ)
          * (2 : ℝ)⁻¹ ^ (n + (magCode (p 0) + magCode (p 1) + 2)) := by
        rw [hK]
        push_cast
        ring
    _ ≤ (2 : ℝ)⁻¹ ^ n := bump _ n

/-- Rational-code distance: `|q₁ - q₂|` on unnormalized fractions. -/
private def distCode (m₁ m₂ : ℕ) : ℕ := absCode (subCode m₁ m₂)

private theorem primrec₂_distCode : Primrec₂ distCode :=
  primrec_absCode.comp primrec₂_subCode

/-- Distance of represented reals is computable: `|q₁ - q₂|` on codes at precision
`n + 1`, since `x ↦ |x|` is 1-Lipschitz. -/
theorem computableMap_realDist :
    ComputableMap (realRep.prod realRep) realRep fun p => |p.1 - p.2| := by
  obtain ⟨c, hc⟩ := computes_binaryOp primrec₂_distCode
  refine ⟨c, .of_computes hc fun p ab hab => ?_⟩
  obtain ⟨hx, hy⟩ := Representation.prod_names_iff.mp hab
  rw [realRep_names_iff] at hx hy
  simp only [Baire.evenPart_apply] at hx
  simp only [Baire.oddPart_apply] at hy
  refine realRep_names_iff.mpr fun n => ?_
  have hcast : ((ratOfCode (distCode (p (2 * (n + 1)))
        (p (2 * (n + 1) + 1))) : ℚ) : ℝ)
      = |((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ)
          - ((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ)| := by
    unfold distCode
    rw [ratOfCode_absCode, ratOfCode_subCode]
    push_cast
    ring_nf
  simp only [hcast]
  refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
  calc |(((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ)
          - ((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ)) - (ab.1 - ab.2)|
      = |(((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ) - ab.1)
          - (((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ) - ab.2)| := by
        congr 1
        ring
    _ ≤ |((ratOfCode (p (2 * (n + 1))) : ℚ) : ℝ) - ab.1|
          + |((ratOfCode (p (2 * (n + 1) + 1)) : ℚ) : ℝ) - ab.2| := abs_sub _ _
    _ ≤ (2 : ℝ)⁻¹ ^ (n + 1) + (2 : ℝ)⁻¹ ^ (n + 1) := add_le_add (hx (n + 1)) (hy (n + 1))
    _ = (2 : ℝ)⁻¹ ^ n := by
        rw [pow_succ]
        ring

end Arithmetic

/-! ### The unit-interval complement -/

/-- The complement map `x ↦ 1 - x` on the represented unit interval. -/
def unitSymm (x : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - x.val, ⟨by linarith [x.property.2], by linarith [x.property.1]⟩⟩

/-- Rational-code unit complement: `1 - q` on unnormalized fractions. -/
private def symmCode (m : ℕ) : ℕ := addCode oneCode (negCode m)

private theorem primrec_symmCode : Primrec symmCode :=
  primrec₂_addCode.comp (Primrec.const oneCode) primrec_negCode

/-- The unit-interval complement is computable: `1 - q` on codes at unchanged precision
(the map is an isometry). -/
theorem computableMap_unitSymm : ComputableMap unitIntervalRep unitIntervalRep unitSymm := by
  obtain ⟨c, hc⟩ := computes_unaryOp primrec_symmCode
  refine ⟨c, .of_computes hc fun p s hps => ?_⟩
  have hx := realRep_names_iff.mp (unitIntervalRep_names_iff.mp hps)
  refine unitIntervalRep_names_iff.mpr (realRep_names_iff.mpr fun n => ?_)
  have hval : (unitSymm s).val = 1 - s.val := rfl
  have hcast : ((ratOfCode (symmCode (p n)) : ℚ) : ℝ)
      = 1 - ((ratOfCode (p n) : ℚ) : ℝ) := by
    unfold symmCode
    rw [ratOfCode_addCode, ratOfCode_oneCode, ratOfCode_negCode]
    push_cast
    ring
  simp only [hcast, hval]
  have hsplit : 1 - ((ratOfCode (p n) : ℚ) : ℝ) - (1 - s.val)
      = -(((ratOfCode (p n) : ℚ) : ℝ) - s.val) := by ring
  rw [hsplit, abs_neg]
  exact hx n

/-! ### Uniform variable-length folds

One oracle code, independent of the length `k`, total on all streams, realizing the sum
(resp. the `[0,1]`-restricted product) of a packed family of real names. -/

section UniformFolds

/-- `F` packs the `k` names `p₀, …, p_{k-1}` of `x 0, …, x (k-1)`:
`F 0 = k` and `pᵢ = fun n => F (1 + Nat.pair i n)`. -/
def Packs (F : Baire) (k : ℕ) (x : Fin k → ℝ) : Prop :=
  F 0 = k ∧ ∀ i : Fin k, realRep.Names (fun n => F (1 + Nat.pair i n)) (x i)

/-- Oracle-free postprocessor for the uniform sum: from `Nat.pair n (encode L)` (where
`L` is the oracle prefix), read `k = L[0]`, then sum the rational codes
`L[1 + Nat.pair i (n + k)]` for `i < k`. -/
private def sumPost (w : ℕ) : ℕ :=
  sumCode ((List.range ((ofNat (List ℕ) w.unpair.2).getD 0 0)).map fun i =>
    (ofNat (List ℕ) w.unpair.2).getD
      (1 + Nat.pair i (w.unpair.1 + (ofNat (List ℕ) w.unpair.2).getD 0 0)) 0)

/-- Oracle-free postprocessor for the uniform product: as `sumPost`, but multiply the
**clamped** rational codes. -/
private def prodPost (w : ℕ) : ℕ :=
  prodCode ((List.range ((ofNat (List ℕ) w.unpair.2).getD 0 0)).map fun i =>
    clampCode ((ofNat (List ℕ) w.unpair.2).getD
      (1 + Nat.pair i (w.unpair.1 + (ofNat (List ℕ) w.unpair.2).getD 0 0)) 0))

section PostPrimrec

open Primrec

private theorem primrec_sumPost : Primrec sumPost := by
  have hL : Primrec fun w : ℕ => ofNat (List ℕ) w.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd
  have hk : Primrec fun w : ℕ => (ofNat (List ℕ) w.unpair.2).getD 0 0 :=
    (list_getD 0).comp hL (const 0)
  have hidx : Primrec fun p : ℕ × ℕ =>
      1 + Nat.pair p.2 (p.1.unpair.1 + (ofNat (List ℕ) p.1.unpair.2).getD 0 0) :=
    nat_add.comp (const 1)
      (Primrec₂.natPair.comp snd (nat_add.comp (primrec_unpairFst.comp fst) (hk.comp fst)))
  have hmap : Primrec fun w : ℕ =>
      (List.range ((ofNat (List ℕ) w.unpair.2).getD 0 0)).map fun i =>
        (ofNat (List ℕ) w.unpair.2).getD
          (1 + Nat.pair i (w.unpair.1 + (ofNat (List ℕ) w.unpair.2).getD 0 0)) 0 :=
    list_map (list_range.comp hk) ((list_getD 0).comp (hL.comp fst) hidx).to₂
  exact primrec_sumCode.comp hmap

private theorem primrec_prodPost : Primrec prodPost := by
  have hL : Primrec fun w : ℕ => ofNat (List ℕ) w.unpair.2 :=
    (Primrec.ofNat (List ℕ)).comp primrec_unpairSnd
  have hk : Primrec fun w : ℕ => (ofNat (List ℕ) w.unpair.2).getD 0 0 :=
    (list_getD 0).comp hL (const 0)
  have hidx : Primrec fun p : ℕ × ℕ =>
      1 + Nat.pair p.2 (p.1.unpair.1 + (ofNat (List ℕ) p.1.unpair.2).getD 0 0) :=
    nat_add.comp (const 1)
      (Primrec₂.natPair.comp snd (nat_add.comp (primrec_unpairFst.comp fst) (hk.comp fst)))
  have hmap : Primrec fun w : ℕ =>
      (List.range ((ofNat (List ℕ) w.unpair.2).getD 0 0)).map fun i =>
        clampCode ((ofNat (List ℕ) w.unpair.2).getD
          (1 + Nat.pair i (w.unpair.1 + (ofNat (List ℕ) w.unpair.2).getD 0 0)) 0) :=
    list_map (list_range.comp hk)
      (primrec_clampCode.comp ((list_getD 0).comp (hL.comp fst) hidx)).to₂
  exact primrec_prodCode.comp hmap

end PostPrimrec

/-- **A single total oracle code uniformly realizes finite sums of packed real names.**
The code is independent of `k`, `F`, and `x`, and is total on all streams and inputs;
coordinate `n` sums the coordinate-`(n + k)` approximants, and `k · 2⁻⁽ⁿ⁺ᵏ⁾ ≤ 2⁻ⁿ`. -/
theorem exists_uniform_sum_realizer :
    ∃ c : OracleCode, (∀ (F : Baire) (n : ℕ), (c.eval F n).Dom) ∧
      ∀ (k : ℕ) (F : Baire) (x : Fin k → ℝ), Packs F k x →
        ∃ q ∈ c.evalStream F, realRep.Names q (∑ i, x i) := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode
    (b := fun n k => 1 + Nat.pair k (n + k)) (g := sumPost)
    (Primrec.nat_add.comp (Primrec.const 1)
      (Primrec₂.natPair.comp Primrec.snd
        (Primrec.nat_add.comp Primrec.fst Primrec.snd)))
    primrec_sumPost
  refine ⟨c, fun F n => by rw [hc F n]; trivial, fun k F x hFx => ?_⟩
  obtain ⟨hF0, hnames⟩ := hFx
  have hnames' : ∀ i : Fin k, ∀ m : ℕ,
      |((ratOfCode (F (1 + Nat.pair i m)) : ℚ) : ℝ) - x i| ≤ (2 : ℝ)⁻¹ ^ m :=
    fun i => realRep_names_iff.mp (hnames i)
  set Q : Baire := fun n =>
    sumPost (Nat.pair n (encode (streamTake F (1 + Nat.pair (F 0) (n + F 0))))) with hQ
  have hQmem : Q ∈ c.evalStream F :=
    mem_evalStream.mpr fun n => by rw [hc F n]; exact Part.mem_some _
  refine ⟨Q, hQmem, realRep_names_iff.mpr fun n => ?_⟩
  have hblen : (streamTake F (1 + Nat.pair (F 0) (n + F 0))).length
      = 1 + Nat.pair k (n + k) := by
    rw [length_streamTake, hF0]
  have hgetD : ∀ j, j < 1 + Nat.pair k (n + k) →
      (streamTake F (1 + Nat.pair (F 0) (n + F 0))).getD j 0 = F j := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [hblen]; exact hj), getElem_streamTake]
  have hk0 : (streamTake F (1 + Nat.pair (F 0) (n + F 0))).getD 0 0 = k := by
    rw [hgetD 0 (by omega), hF0]
  have hQn : ratOfCode (Q n)
      = ∑ i : Fin k, ratOfCode (F (1 + Nat.pair i (n + k))) := by
    simp only [hQ]
    simp only [sumPost, Nat.unpair_pair, ofNat_encode]
    rw [hk0, ratOfCode_sumCode, List.map_map, listSum_range_map (M := ℚ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hilt : 1 + Nat.pair (i : ℕ) (n + k) < 1 + Nat.pair k (n + k) :=
      Nat.add_lt_add_left (Nat.pair_lt_pair_left (n + k) i.isLt) 1
    simp only [Function.comp_apply]
    rw [hgetD _ hilt]
  calc |((ratOfCode (Q n) : ℚ) : ℝ) - ∑ i, x i|
      = |∑ i : Fin k, (((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ) - x i)| := by
        rw [hQn, Finset.sum_sub_distrib]
        push_cast
        ring_nf
    _ ≤ ∑ i : Fin k, |((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ) - x i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin k, (2 : ℝ)⁻¹ ^ (n + k) :=
        Finset.sum_le_sum fun i _ => hnames' i (n + k)
    _ = (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (2 : ℝ)⁻¹ ^ n := bump k n

/-- **A single total oracle code uniformly realizes finite products of packed
`[0,1]`-real names.** Each approximant is clamped into `[0,1]` (1-Lipschitz, identity on
`[0,1]`), where the telescoping estimate `|∏a - ∏b| ≤ ∑|aᵢ - bᵢ|` gives the same
precision bump `n + k` as the sum. -/
theorem exists_uniform_unitProd_realizer :
    ∃ c : OracleCode, (∀ (F : Baire) (n : ℕ), (c.eval F n).Dom) ∧
      ∀ (k : ℕ) (F : Baire) (x : Fin k → ℝ), Packs F k x →
        (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) →
        ∃ q ∈ c.evalStream F, realRep.Names q (∏ i, x i) := by
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode
    (b := fun n k => 1 + Nat.pair k (n + k)) (g := prodPost)
    (Primrec.nat_add.comp (Primrec.const 1)
      (Primrec₂.natPair.comp Primrec.snd
        (Primrec.nat_add.comp Primrec.fst Primrec.snd)))
    primrec_prodPost
  refine ⟨c, fun F n => by rw [hc F n]; trivial, fun k F x hFx hx => ?_⟩
  obtain ⟨hF0, hnames⟩ := hFx
  have hnames' : ∀ i : Fin k, ∀ m : ℕ,
      |((ratOfCode (F (1 + Nat.pair i m)) : ℚ) : ℝ) - x i| ≤ (2 : ℝ)⁻¹ ^ m :=
    fun i => realRep_names_iff.mp (hnames i)
  set Q : Baire := fun n =>
    prodPost (Nat.pair n (encode (streamTake F (1 + Nat.pair (F 0) (n + F 0))))) with hQ
  have hQmem : Q ∈ c.evalStream F :=
    mem_evalStream.mpr fun n => by rw [hc F n]; exact Part.mem_some _
  refine ⟨Q, hQmem, realRep_names_iff.mpr fun n => ?_⟩
  have hblen : (streamTake F (1 + Nat.pair (F 0) (n + F 0))).length
      = 1 + Nat.pair k (n + k) := by
    rw [length_streamTake, hF0]
  have hgetD : ∀ j, j < 1 + Nat.pair k (n + k) →
      (streamTake F (1 + Nat.pair (F 0) (n + F 0))).getD j 0 = F j := by
    intro j hj
    rw [List.getD_eq_getElem _ _ (by rw [hblen]; exact hj), getElem_streamTake]
  have hk0 : (streamTake F (1 + Nat.pair (F 0) (n + F 0))).getD 0 0 = k := by
    rw [hgetD 0 (by omega), hF0]
  have hQn : ratOfCode (Q n)
      = ∏ i : Fin k, ratOfCode (clampCode (F (1 + Nat.pair i (n + k)))) := by
    simp only [hQ]
    simp only [prodPost, Nat.unpair_pair, ofNat_encode]
    rw [hk0, ratOfCode_prodCode, List.map_map, listProd_range_map (M := ℚ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hilt : 1 + Nat.pair (i : ℕ) (n + k) < 1 + Nat.pair k (n + k) :=
      Nat.add_lt_add_left (Nat.pair_lt_pair_left (n + k) i.isLt) 1
    simp only [Function.comp_apply]
    rw [hgetD _ hilt]
  have hcast : ((ratOfCode (Q n) : ℚ) : ℝ)
      = ∏ i : Fin k,
          max 0 (min 1 ((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ)) := by
    rw [hQn, Rat.cast_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ratOfCode_clampCode]
    push_cast
    rfl
  calc |((ratOfCode (Q n) : ℚ) : ℝ) - ∏ i, x i|
      = |∏ i : Fin k, max 0 (min 1 ((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ))
          - ∏ i, x i| := by rw [hcast]
    _ ≤ ∑ i : Fin k,
          |max 0 (min 1 ((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ)) - x i| :=
        abs_prod_sub_prod_le _ _ (fun i => clamp_mem_Icc _) hx
    _ ≤ ∑ _i : Fin k, (2 : ℝ)⁻¹ ^ (n + k) := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc |max 0 (min 1 ((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ)) - x i|
            = |max 0 (min 1 ((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ))
                - max 0 (min 1 (x i))| := by rw [clamp_eq_self (hx i)]
          _ ≤ |((ratOfCode (F (1 + Nat.pair i (n + k))) : ℚ) : ℝ) - x i| :=
              abs_clamp_sub_clamp_le _ _
          _ ≤ (2 : ℝ)⁻¹ ^ (n + k) := hnames' i (n + k)
    _ = (k : ℝ) * (2 : ℝ)⁻¹ ^ (n + k) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ (2 : ℝ)⁻¹ ^ n := bump k n

end UniformFolds

end ComputableAnalysis
