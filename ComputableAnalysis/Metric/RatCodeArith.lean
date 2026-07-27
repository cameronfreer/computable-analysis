/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Metric.Presentation

/-!
# Arithmetic on rational codes

The public arithmetic layer over `RatCode`. `Metric/Presentation.lean` fixes the coding
`ratOfCode (Nat.pair (Nat.pair a b) c) = (a - b) / (c + 1)` and the two primitives
`ratOfCode`/`zeroCode`; this file adds the combinators every realizer in the library
actually computes with, each with its `ratOfCode` **value spec** and its
`Primrec`/`Primrec₂` **computability proof**:

* the constant `oneCode`;
* the coded naturals `natCode` and the coded positive fractions `fracCode`;
* the ring operations `addCode`, `negCode`, `subCode`, `mulCode`;
* the variable-length folds `sumCode`, `prodCode`;
* the order-flavoured `absCode`, `distCode`, `clampCode`, `symmCode`.

Because the fractions are *unnormalized* — no gcd is ever taken — every operation is
plain `Nat.pair` arithmetic on the three slots, so all of them are primitive recursive by
mathlib's `Primrec` lemmas. The denominator slot holds `c` for the denominator `c + 1`,
which is why the products of denominators appear as `(c₁ + 1) * (c₂ + 1) - 1`; the
truncated subtraction is exact there since the product is positive.

The sign and threshold tests are ℕ comparisons of the numerator slots, again because the
denominator is positive: `a ≤ b` says the decoded value is `≤ 0`, and `b + c + 1 ≤ a`
says it is `≥ 1`.

The companion `Primrec` projections out of the coding, `primrec_unpairFst` and
`primrec_unpairSnd`, are public in `Metric/Presentation.lean` (they are used there, so
they cannot live downstream of it).
-/

namespace ComputableAnalysis

/-! ### The coded one -/

/-- The canonical code of `1`: the unnormalized fraction `(1 - 0) / (0 + 1)`. -/
def oneCode : RatCode := Nat.pair (Nat.pair 1 0) 0

/-- `oneCode` decodes to `1`. -/
theorem ratOfCode_oneCode : ratOfCode oneCode = 1 := by
  simp [ratOfCode, oneCode]

/-! ### Coded naturals and coded positive fractions -/

/-- The canonical code of a natural number `a`: the unnormalized fraction
`(a - 0) / (0 + 1)`. -/
def natCode (a : ℕ) : RatCode := Nat.pair (Nat.pair a 0) 0

/-- `natCode` decodes to the natural number it codes. -/
theorem ratOfCode_natCode (a : ℕ) : ratOfCode (natCode a) = a := by
  simp [ratOfCode, natCode]

/-- The canonical code of the fraction `a / b` with natural numerator and **positive**
natural denominator: the unnormalized fraction `(a - 0) / ((b - 1) + 1)`. The truncated
subtraction in the denominator slot is exact whenever `b ≠ 0`, which is the hypothesis of
`ratOfCode_fracCode`; at `b = 0` the code decodes to `a` instead. -/
def fracCode (a b : ℕ) : RatCode := Nat.pair (Nat.pair a 0) (b - 1)

/-- `fracCode a b` decodes to the rational `a / b`, for `b ≠ 0`. -/
theorem ratOfCode_fracCode {b : ℕ} (hb : b ≠ 0) (a : ℕ) :
    ratOfCode (fracCode a b) = (a : ℚ) / b := by
  have hcast : ((b - 1 : ℕ) : ℚ) + 1 = (b : ℚ) := by
    have h1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    push_cast [h1]
    ring
  simp only [ratOfCode, fracCode, Nat.unpair_pair, hcast]
  norm_num

/-! ### Additive arithmetic -/

/-- Addition of rational codes: fraction arithmetic without normalization. -/
def addCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (m₁.unpair.1.unpair.1 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.1 * (m₁.unpair.2 + 1))
      (m₁.unpair.1.unpair.2 * (m₂.unpair.2 + 1) + m₂.unpair.1.unpair.2 * (m₁.unpair.2 + 1)))
    ((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1)

/-- `addCode` decodes to the sum of the decoded rationals. -/
theorem ratOfCode_addCode (m₁ m₂ : ℕ) :
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
def negCode (m : ℕ) : ℕ :=
  Nat.pair (Nat.pair m.unpair.1.unpair.2 m.unpair.1.unpair.1) m.unpair.2

/-- `negCode` decodes to the negation of the decoded rational. -/
theorem ratOfCode_negCode (m : ℕ) : ratOfCode (negCode m) = -ratOfCode m := by
  simp only [ratOfCode, negCode, Nat.unpair_pair]
  rw [← neg_div, neg_sub]

/-- Subtraction of rational codes. -/
def subCode (m₁ m₂ : ℕ) : ℕ := addCode m₁ (negCode m₂)

/-- `subCode` decodes to the difference of the decoded rationals. -/
theorem ratOfCode_subCode (m₁ m₂ : ℕ) :
    ratOfCode (subCode m₁ m₂) = ratOfCode m₁ - ratOfCode m₂ := by
  rw [subCode, ratOfCode_addCode, ratOfCode_negCode, sub_eq_add_neg]

/-! ### Multiplicative arithmetic -/

/-- Multiplication of rational codes: unnormalized signed-fraction arithmetic,
`(a₁-b₁)(a₂-b₂) = (a₁a₂ + b₁b₂) - (a₁b₂ + a₂b₁)`; no gcd. -/
def mulCode (m₁ m₂ : ℕ) : ℕ :=
  Nat.pair
    (Nat.pair
      (m₁.unpair.1.unpair.1 * m₂.unpair.1.unpair.1
        + m₁.unpair.1.unpair.2 * m₂.unpair.1.unpair.2)
      (m₁.unpair.1.unpair.1 * m₂.unpair.1.unpair.2
        + m₁.unpair.1.unpair.2 * m₂.unpair.1.unpair.1))
    ((m₁.unpair.2 + 1) * (m₂.unpair.2 + 1) - 1)

/-- `mulCode` decodes to the product of the decoded rationals. -/
theorem ratOfCode_mulCode (m₁ m₂ : ℕ) :
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

/-! ### Variable-length folds -/

/-- Sum of a list of rational codes. -/
def sumCode (l : List ℕ) : ℕ :=
  l.foldr addCode 0

/-- `sumCode` decodes to the sum of the decoded rationals. -/
theorem ratOfCode_sumCode (l : List ℕ) :
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
def prodCode (l : List ℕ) : ℕ :=
  l.foldr mulCode oneCode

/-- `prodCode` decodes to the product of the decoded rationals. -/
theorem ratOfCode_prodCode (l : List ℕ) :
    ratOfCode (prodCode l) = (l.map ratOfCode).prod := by
  induction l with
  | nil =>
    simp only [prodCode, List.foldr_nil, List.map_nil, List.prod_nil]
    exact ratOfCode_oneCode
  | cons a l ih =>
    simp only [prodCode, List.foldr_cons, List.map_cons, List.prod_cons, ratOfCode_mulCode]
    rw [← ih]
    rfl

/-! ### Absolute value, distance, clamping and the unit complement -/

/-- Absolute value of a rational code: negate exactly when the numerator is nonpositive
(the ℕ test `a ≤ b`, since the denominator is positive). -/
def absCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 then negCode m else m

/-- `absCode` decodes to the absolute value of the decoded rational. -/
theorem ratOfCode_absCode (m : ℕ) : ratOfCode (absCode m) = |ratOfCode m| := by
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

/-- Rational-code distance: `|q₁ - q₂|` on unnormalized fractions. -/
def distCode (m₁ m₂ : ℕ) : ℕ := absCode (subCode m₁ m₂)

/-- `distCode` decodes to the distance between the decoded rationals. -/
theorem ratOfCode_distCode (m₁ m₂ : ℕ) :
    ratOfCode (distCode m₁ m₂) = |ratOfCode m₁ - ratOfCode m₂| := by
  rw [distCode, ratOfCode_absCode, ratOfCode_subCode]

/-- Clamp a rational code into `[0,1]`: the sign/threshold tests on the unnormalized
fraction `(a - b)/(c + 1)` are the ℕ comparisons `a ≤ b` (value `≤ 0`) and
`b + c + 1 ≤ a` (value `≥ 1`), since `c + 1 > 0`. -/
def clampCode (m : ℕ) : ℕ :=
  if m.unpair.1.unpair.1 ≤ m.unpair.1.unpair.2 then zeroCode
  else if m.unpair.1.unpair.2 + m.unpair.2 + 1 ≤ m.unpair.1.unpair.1 then oneCode
  else m

/-- `clampCode` decodes to the clamp of the decoded rational into `[0,1]`. -/
theorem ratOfCode_clampCode (m : ℕ) :
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

/-- Rational-code unit complement: `1 - q` on unnormalized fractions. -/
def symmCode (m : ℕ) : ℕ := addCode oneCode (negCode m)

/-- `symmCode` decodes to the unit complement of the decoded rational. -/
theorem ratOfCode_symmCode (m : ℕ) : ratOfCode (symmCode m) = 1 - ratOfCode m := by
  rw [symmCode, ratOfCode_addCode, ratOfCode_oneCode, ratOfCode_negCode, sub_eq_add_neg]

/-! ### Computability

Every combinator above is built from `Nat.pair`, `Nat.unpair`, `+`, `*`, truncated
subtraction and decidable ℕ comparisons, so all of them are primitive recursive. -/

section PrimrecFacts

open Primrec

/-- `natCode` is primitive recursive. -/
theorem primrec_natCode : Primrec natCode :=
  Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.id (const 0)) (const 0)

/-- `fracCode` is primitive recursive in both arguments. -/
theorem primrec₂_fracCode : Primrec₂ fracCode :=
  Primrec₂.natPair.comp (Primrec₂.natPair.comp fst (const 0))
    (nat_sub.comp snd (const 1))

/-- `addCode` is primitive recursive in both arguments. -/
theorem primrec₂_addCode : Primrec₂ addCode := by
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

/-- `negCode` is primitive recursive. -/
theorem primrec_negCode : Primrec negCode :=
  Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (primrec_unpairSnd.comp primrec_unpairFst)
      (primrec_unpairFst.comp primrec_unpairFst))
    primrec_unpairSnd

/-- `subCode` is primitive recursive in both arguments. -/
theorem primrec₂_subCode : Primrec₂ subCode :=
  primrec₂_addCode.comp fst (primrec_negCode.comp snd)

/-- `mulCode` is primitive recursive in both arguments. -/
theorem primrec₂_mulCode : Primrec₂ mulCode := by
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

/-- `sumCode` is primitive recursive. -/
theorem primrec_sumCode : Primrec sumCode :=
  (list_foldr Primrec.id (const 0)
    (primrec₂_addCode.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun _ => rfl

/-- `prodCode` is primitive recursive. -/
theorem primrec_prodCode : Primrec prodCode :=
  (list_foldr Primrec.id (const oneCode)
    (primrec₂_mulCode.comp (fst.comp snd) (snd.comp snd)).to₂).of_eq fun _ => rfl

/-- `absCode` is primitive recursive. -/
theorem primrec_absCode : Primrec absCode := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  exact Primrec.ite (Primrec.nat_le.comp ha hb) primrec_negCode Primrec.id

/-- `distCode` is primitive recursive in both arguments. -/
theorem primrec₂_distCode : Primrec₂ distCode :=
  primrec_absCode.comp primrec₂_subCode

/-- `clampCode` is primitive recursive. -/
theorem primrec_clampCode : Primrec clampCode := by
  have ha : Primrec fun m : ℕ => m.unpair.1.unpair.1 :=
    primrec_unpairFst.comp primrec_unpairFst
  have hb : Primrec fun m : ℕ => m.unpair.1.unpair.2 :=
    primrec_unpairSnd.comp primrec_unpairFst
  exact Primrec.ite (Primrec.nat_le.comp ha hb) (Primrec.const zeroCode)
    (Primrec.ite
      (Primrec.nat_le.comp
        (Primrec.succ.comp (Primrec.nat_add.comp hb primrec_unpairSnd)) ha)
      (Primrec.const oneCode) Primrec.id)

/-- `symmCode` is primitive recursive. -/
theorem primrec_symmCode : Primrec symmCode :=
  primrec₂_addCode.comp (Primrec.const oneCode) primrec_negCode

end PrimrecFacts

end ComputableAnalysis
