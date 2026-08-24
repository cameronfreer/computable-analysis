/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.Integration
import ComputableAnalysis.Measure.UnitInterval
import ComputableAnalysis.Metric.RatCodeArith
import ComputableAnalysis.RepresentedSpace.ComputableMap
import ComputableAnalysis.TypeTwo.Universal

/-!
# The Bernstein integrand, uniformly in the word

For a Boolean word `s` the *Bernstein basis function* of `s` is the map

  `p ↦ p ^ (s.count true) * (1 - p) ^ (s.count false)`

on `[0, 1]`.  It is bounded by `1` and Lipschitz with constant `s.length`, so it is a
`BoundedLipschitzFun (Set.Icc (0 : ℝ) 1)` — a legitimate integrand for the frozen
bounded-Lipschitz integration operation of `ComputableAnalysis.Measure.Integration`.

The main results are:

* `bernsteinBL` — the bundled bounded-Lipschitz function, with `bernsteinBL_apply`;
* `bernsteinName` — an explicit `IntegrandName` layout over `unitIntervalPresentation`
  (`integrandName_bernsteinName`);
* `computableMap_bernsteinBL` — the family is computable **uniformly in the word**, as a
  map `discreteRep (List Bool) ⟶ blRep unitIntervalPresentation`;
* `monomialBL` / `monomialName` — the monomials `p ↦ p ^ n`, obtained as the special case
  of the all-ones word, and their fixed packed integrand stream `monomialStreamFn`.

**The approximation streams are exact.**  The dense points of `unitIntervalPresentation`
are the clamped rationals `unitClamp (ratOfCode m)`, whose values are *rational*, so the
Bernstein value at a dense point is an exactly representable rational: the `approx` field
of `IntegrandName` is satisfied with error `0`.
-/

namespace ComputableAnalysis

open scoped NNReal

/-! ### The Bernstein basis function -/

/-- The **Bernstein basis function** of a word `s`, as a plain real-valued function on the
unit interval: `p ↦ p ^ (s.count true) * (1 - p) ^ (s.count false)`. -/
noncomputable def bernsteinFun (s : List Bool) (p : Set.Icc (0 : ℝ) 1) : ℝ :=
  (p : ℝ) ^ s.count true * (1 - (p : ℝ)) ^ s.count false

/-- The two bit counts of a word add up to its length. -/
private theorem count_true_add_count_false (s : List Bool) :
    s.count true + s.count false = s.length := by
  induction s with
  | nil => rfl
  | cons c t ih => cases c <;> simp <;> omega

/-- On `[0, 1]` the `n`-th power map is `n`-Lipschitz: `|x ^ n - y ^ n| ≤ n |x - y|`. -/
private theorem abs_pow_sub_pow_le_nat {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) : |x ^ n - y ^ n| ≤ (n : ℝ) * |x - y| := by
  obtain ⟨hx0, hx1⟩ := hx
  obtain ⟨hy0, hy1⟩ := hy
  have h0 : (0 : ℝ) ≤ max |x| |y| := le_trans (abs_nonneg x) (le_max_left _ _)
  have h1 : max |x| |y| ≤ 1 :=
    max_le (abs_le.mpr ⟨by linarith, hx1⟩) (abs_le.mpr ⟨by linarith, hy1⟩)
  calc |x ^ n - y ^ n| ≤ |x - y| * n * max |x| |y| ^ (n - 1) := abs_pow_sub_pow_le x y n
    _ ≤ |x - y| * n * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (by positivity)
    _ = (n : ℝ) * |x - y| := by ring

/-- The Bernstein basis function is bounded by `1`. -/
private theorem abs_bernsteinFun_le (s : List Bool) (p : Set.Icc (0 : ℝ) 1) :
    |bernsteinFun s p| ≤ 1 := by
  obtain ⟨hp0, hp1⟩ := p.2
  have h1 : |(p : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, hp1⟩
  have h2 : |1 - (p : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [bernsteinFun, abs_mul, abs_pow, abs_pow]
  calc |(p : ℝ)| ^ s.count true * |1 - (p : ℝ)| ^ s.count false ≤ 1 * 1 :=
        mul_le_mul (pow_le_one₀ (abs_nonneg _) h1) (pow_le_one₀ (abs_nonneg _) h2)
          (by positivity) zero_le_one
    _ = 1 := one_mul 1

/-- The Bernstein basis function of `s` is Lipschitz with constant `s.length`: the two
factors are bounded by `1` and Lipschitz with the respective bit counts. -/
private theorem lipschitzWith_bernsteinFun (s : List Bool) :
    LipschitzWith (s.length : ℝ≥0) (bernsteinFun s) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  obtain ⟨hx0, hx1⟩ := x.2
  obtain ⟨hy0, hy1⟩ := y.2
  have hX : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
  have hY : (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hy0, hy1⟩
  have hX' : 1 - (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hY' : 1 - (y : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hpowT : |(x : ℝ) ^ s.count true - (y : ℝ) ^ s.count true|
      ≤ (s.count true : ℝ) * |(x : ℝ) - (y : ℝ)| := abs_pow_sub_pow_le_nat hX hY _
  have hpowF : |(1 - (x : ℝ)) ^ s.count false - (1 - (y : ℝ)) ^ s.count false|
      ≤ (s.count false : ℝ) * |(x : ℝ) - (y : ℝ)| := by
    have h := abs_pow_sub_pow_le_nat hX' hY' (s.count false)
    rwa [show (1 - (x : ℝ)) - (1 - (y : ℝ)) = -((x : ℝ) - (y : ℝ)) by ring, abs_neg] at h
  have hbT : |(x : ℝ) ^ s.count true| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, hx1⟩)
  have hbF : |(1 - (y : ℝ)) ^ s.count false| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hsplit : bernsteinFun s x - bernsteinFun s y
      = (x : ℝ) ^ s.count true
          * ((1 - (x : ℝ)) ^ s.count false - (1 - (y : ℝ)) ^ s.count false)
        + (1 - (y : ℝ)) ^ s.count false
          * ((x : ℝ) ^ s.count true - (y : ℝ) ^ s.count true) := by
    simp only [bernsteinFun]; ring
  have hlen : ((s.count true : ℝ)) + (s.count false : ℝ) = (s.length : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (count_true_add_count_false s)
  rw [Real.dist_eq, Subtype.dist_eq, Real.dist_eq, NNReal.coe_natCast, hsplit]
  calc |(x : ℝ) ^ s.count true
          * ((1 - (x : ℝ)) ^ s.count false - (1 - (y : ℝ)) ^ s.count false)
        + (1 - (y : ℝ)) ^ s.count false
          * ((x : ℝ) ^ s.count true - (y : ℝ) ^ s.count true)|
      ≤ |(x : ℝ) ^ s.count true
          * ((1 - (x : ℝ)) ^ s.count false - (1 - (y : ℝ)) ^ s.count false)|
        + |(1 - (y : ℝ)) ^ s.count false
          * ((x : ℝ) ^ s.count true - (y : ℝ) ^ s.count true)| := abs_add_le _ _
    _ ≤ 1 * ((s.count false : ℝ) * |(x : ℝ) - (y : ℝ)|)
        + 1 * ((s.count true : ℝ) * |(x : ℝ) - (y : ℝ)|) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul hbT hpowF (abs_nonneg _) zero_le_one)
          (mul_le_mul hbF hpowT (abs_nonneg _) zero_le_one)
    _ = (s.length : ℝ) * |(x : ℝ) - (y : ℝ)| := by rw [← hlen]; ring

/-- The **Bernstein basis function of a word**, bundled as a bounded Lipschitz function on
`[0, 1]`: Lipschitz constant `s.length`, uniform bound `1`. -/
noncomputable def bernsteinBL (s : List Bool) : BoundedLipschitzFun (Set.Icc (0 : ℝ) 1) where
  toFun := bernsteinFun s
  exists_bounds := ⟨s.length, 1, lipschitzWith_bernsteinFun s, fun p ↦ by
    simpa using abs_bernsteinFun_le s p⟩

/-- The value of `bernsteinBL`. -/
@[simp]
theorem bernsteinBL_apply (s : List Bool) (p : Set.Icc (0 : ℝ) 1) :
    bernsteinBL s p = (p : ℝ) ^ s.count true * (1 - (p : ℝ)) ^ s.count false := rfl

/-! ### The value codes

The dense points of `unitIntervalPresentation` are the clamped rationals, so every
Bernstein value at a dense point is itself a rational and is coded exactly. -/

/-- A word-indexed product of two values collapses to a product of powers, the exponents
being the bit counts of the word. -/
private theorem prod_map_cond {M : Type*} [CommMonoid M] (a b : M) (s : List Bool) :
    (s.map fun c ↦ cond c a b).prod = a ^ s.count true * b ^ s.count false := by
  induction s with
  | nil => simp
  | cons c t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.count_cons, List.count_cons]
    cases c <;> simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- The **value code** of the Bernstein basis function of `s` at the dense point of index
`m`: the coded product of one factor per bit of `s`, `clampCode m` for `true` and its unit
complement for `false`. -/
def bernsteinCode (s : List Bool) (m : ℕ) : ℕ :=
  prodCode (s.map fun b ↦ cond b (clampCode m) (symmCode (clampCode m)))

/-- `bernsteinCode` decodes to the Bernstein expression in the clamped rational. -/
theorem ratOfCode_bernsteinCode (s : List Bool) (m : ℕ) :
    ratOfCode (bernsteinCode s m)
      = ratOfCode (clampCode m) ^ s.count true
        * (1 - ratOfCode (clampCode m)) ^ s.count false := by
  rw [bernsteinCode, ratOfCode_prodCode, List.map_map]
  have hmap : (ratOfCode ∘ fun b ↦ cond b (clampCode m) (symmCode (clampCode m)))
      = fun b ↦ cond b (ratOfCode (clampCode m)) (1 - ratOfCode (clampCode m)) := by
    funext b
    cases b <;> simp [ratOfCode_symmCode]
  rw [hmap, prod_map_cond]

/-- The decoded value of `bernsteinCode s m` is **exactly** the Bernstein value at the
dense point of index `m`. -/
theorem cast_ratOfCode_bernsteinCode (s : List Bool) (m : ℕ) :
    ((ratOfCode (bernsteinCode s m) : ℚ) : ℝ)
      = bernsteinFun s (unitClamp (ratOfCode m)) := by
  rw [ratOfCode_bernsteinCode, ratOfCode_clampCode, bernsteinFun]
  push_cast
  rfl

/-! ### The integrand-name stream -/

/-- The **integrand-name stream** of a word `s` over `unitIntervalPresentation`: the head
coordinates carry the Lipschitz constant `s.length` and the uniform bound `1`, and the
coordinate `2 + Nat.pair m n` carries the exact value code at the dense point `m`. -/
def bernsteinName (s : List Bool) : Baire := fun j ↦
  if j = 0 then s.length else if j = 1 then 1 else bernsteinCode s (j - 2).unpair.1

/-- The first head coordinate of `bernsteinName` is the Lipschitz constant. -/
@[simp]
theorem bernsteinName_zero (s : List Bool) : bernsteinName s 0 = s.length := rfl

/-- The second head coordinate of `bernsteinName` is the uniform bound. -/
@[simp]
theorem bernsteinName_one (s : List Bool) : bernsteinName s 1 = 1 := rfl

/-- The value coordinates of `bernsteinName` are the value codes. -/
theorem bernsteinName_pair (s : List Bool) (m n : ℕ) :
    bernsteinName s (2 + Nat.pair m n) = bernsteinCode s m := by
  have h2 : 2 + Nat.pair m n - 2 = Nat.pair m n := by omega
  simp only [bernsteinName]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), h2, Nat.unpair_pair]

/-- **`bernsteinName s` is an integrand layout for `bernsteinBL s`**, with heads
`L = s.length` and `B = 1`; the approximation streams are exact. -/
theorem integrandName_bernsteinName (s : List Bool) :
    IntegrandName unitIntervalPresentation (bernsteinName s) s.length 1
      (bernsteinBL s).toFun where
  headL := rfl
  headB := rfl
  lip := lipschitzWith_bernsteinFun s
  bound := fun p ↦ by
    rw [Nat.cast_one]
    exact abs_bernsteinFun_le s p
  approx := fun m n ↦ by
    rw [bernsteinName_pair, cast_ratOfCode_bernsteinCode]
    change |bernsteinFun s (unitClamp (ratOfCode m))
      - bernsteinFun s (unitClamp (ratOfCode m))| ≤ _
    rw [sub_self, abs_zero]
    positivity

/-! ### The uniform realizer -/

/-- The Bernstein integrand streams as a single numeric function: the argument codes the
pair of the `Encodable` code of the word and the stream coordinate. -/
def bernsteinStreamFn (v : ℕ) : ℕ :=
  bernsteinName ((Encodable.decode (α := List Bool) v.unpair.1).getD []) v.unpair.2

/-- The integrand-name stream is primitive recursive in the word and the coordinate. -/
private theorem primrec₂_bernsteinName :
    Primrec₂ fun (s : List Bool) (j : ℕ) ↦ bernsteinName s j := by
  have hm : Primrec fun w : List Bool × ℕ ↦ clampCode (w.2 - 2).unpair.1 :=
    primrec_clampCode.comp (primrec_unpairFst.comp
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 2)))
  have hcode : Primrec fun w : List Bool × ℕ ↦ bernsteinCode w.1 (w.2 - 2).unpair.1 :=
    primrec_prodCode.comp (Primrec.list_map Primrec.fst
      (Primrec.cond Primrec.snd (hm.comp Primrec.fst)
        ((primrec_symmCode.comp hm).comp Primrec.fst)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.list_length.comp Primrec.fst)
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 1)) (Primrec.const 1) hcode)

/-- `bernsteinStreamFn` is primitive recursive. Public so that it can be fed to
`type2Computable_const_stream` as a fixed computable integrand stream. -/
theorem primrec_bernsteinStreamFn : Primrec bernsteinStreamFn :=
  primrec₂_bernsteinName.comp
    (Primrec.option_getD.comp (Primrec.decode.comp primrec_unpairFst) (Primrec.const []))
    primrec_unpairSnd

/-- Reading the head of the input stream and applying `bernsteinStreamFn` is a total
computed stream operator. -/
private theorem exists_bernsteinStreamCode :
    ∃ c : OracleCode, c.Computes fun p n ↦ bernsteinStreamFn (Nat.pair (p 0) n) := by
  obtain ⟨G, hG⟩ := OracleCode.exists_ofNatFnCode primrec_bernsteinStreamFn.to_comp
  refine ⟨OracleCode.comp G (.pair (.comp .query .zero) .id), fun p n ↦ ?_⟩
  have h0 : (OracleCode.comp .query .zero).eval p n = Part.some (p 0) :=
    (OracleCode.eval_comp_some rfl).trans (OracleCode.eval_query p 0)
  rw [OracleCode.eval_comp_some (OracleCode.eval_pair_some h0 (OracleCode.eval_id p n)), hG]

/-- **The Bernstein family is computable, uniformly in the word**: the map
`s ↦ bernsteinBL s` from the discretely represented `List Bool` to the bounded-Lipschitz
representation over `unitIntervalPresentation` is a `ComputableMap`. -/
theorem computableMap_bernsteinBL :
    ComputableMap discreteRep (blRep unitIntervalPresentation) bernsteinBL := by
  obtain ⟨c, hc⟩ := exists_bernsteinStreamCode
  refine ⟨c, Realizes.of_computes hc fun p s hps ↦ ?_⟩
  have hdec : Encodable.decode (α := List Bool) (p 0) = some s :=
    discreteRep_names_iff.mp hps
  have hstream : (fun n ↦ bernsteinStreamFn (Nat.pair (p 0) n)) = bernsteinName s := by
    funext n
    simp [bernsteinStreamFn, hdec]
  rw [hstream]
  exact (blRep_names_iff _).mpr (integrandName_bernsteinName s)

/-! ### The monomials

The monomial `p ↦ p ^ n` is the Bernstein basis function of the all-ones word of length
`n`: `List.count true (List.replicate n true) = n` and `List.count false ... = 0`, so the
second factor is an empty power.  Everything analytic — the Lipschitz constant, the
uniform bound, the exactness of the approximation stream — is therefore inherited from
`integrandName_bernsteinName`; nothing below reproves any of it. -/

/-- The **monomial** `p ↦ p ^ n` on `[0, 1]`, bundled as a bounded Lipschitz function: the
Bernstein basis function of the all-ones word `List.replicate n true`, whose Lipschitz
constant is `n` and whose uniform bound is `1`. -/
noncomputable def monomialBL (n : ℕ) : BoundedLipschitzFun (Set.Icc (0 : ℝ) 1) :=
  bernsteinBL (List.replicate n true)

/-- The value of `monomialBL n` is the monomial `p ^ n`: the all-ones word has `n`
occurrences of `true` and none of `false`, so the `1 - p` factor is an empty power. -/
@[simp]
theorem monomialBL_apply (n : ℕ) (p : Set.Icc (0 : ℝ) 1) :
    monomialBL n p = (p : ℝ) ^ n := by
  simp [monomialBL, List.count_replicate]

/-- The **integrand-name stream of the monomial** `p ↦ p ^ n`: the Bernstein layout of the
all-ones word of length `n`. -/
def monomialName (n : ℕ) : Baire := bernsteinName (List.replicate n true)

/-- **`monomialName n` is an integrand layout for `monomialBL n`**, with heads `L = n` and
`B = 1`; the approximation streams are exact.  A specialisation of
`integrandName_bernsteinName`, using `List.length_replicate` to read the Lipschitz head. -/
theorem integrandName_monomialName (n : ℕ) :
    IntegrandName unitIntervalPresentation (monomialName n) n 1 (monomialBL n).toFun := by
  have h := integrandName_bernsteinName (List.replicate n true)
  rw [List.length_replicate] at h
  exact h

-- Kept private pending upstreaming to mathlib, where `Primrec (List.replicate · a)` belongs:
-- the constant-`true` map over `List.range n` is the workaround used until then.
/-- The all-ones words form a primitive recursive family: `List.replicate n true` is the
constant-`true` map over `List.range n`. -/
private theorem primrec_replicateTrue : Primrec fun n : ℕ ↦ List.replicate n true :=
  (Primrec.list_map Primrec.list_range (Primrec.const true).to₂).of_eq fun n ↦ by
    simp [List.map_const', List.length_range]

/-- The monomial integrand streams as a single numeric function: the argument codes the
pair of the exponent and the stream coordinate. -/
def monomialStreamFn (v : ℕ) : ℕ :=
  bernsteinName (List.replicate v.unpair.1 true) v.unpair.2

/-- `monomialStreamFn` is primitive recursive. Public so that it can be fed to
`type2Computable_const_stream` as a fixed computable integrand stream. -/
theorem primrec_monomialStreamFn : Primrec monomialStreamFn :=
  primrec₂_bernsteinName.comp (primrec_replicateTrue.comp primrec_unpairFst) primrec_unpairSnd

/-- The slice of `monomialStreamFn` at exponent `n` is the monomial integrand name. Note
that `unpair (pair n j)` does not collapse definitionally; this is the rewrite. -/
theorem monomialStreamFn_slice (n : ℕ) :
    (fun j ↦ monomialStreamFn (Nat.pair n j)) = monomialName n := by
  funext j
  simp [monomialStreamFn, monomialName]

end ComputableAnalysis
