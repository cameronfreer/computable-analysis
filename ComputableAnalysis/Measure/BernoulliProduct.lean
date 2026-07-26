/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.Constructors
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.ProductMeasure

/-!
# The Bernoulli product as an infinite product measure

`bernoulliProduct p` is defined through its cylinder masses, via the existence theorem for
consistent cylinder-mass functions. That presentation is what a realizer needs, but it is
inconvenient for measure-theoretic work: it says what the measure does to words, not how it
relates to mathlib's product constructions.

This module identifies it with mathlib's infinite product of the one-bit Bernoulli
distribution `Ber(true, false, p)`, which opens mathlib's product API to it — including
`Measure.infinitePi_pi` for boxes — and records the measurability of the family in its
parameter, which is what forming Giry kernels over the parameter requires.

Main results:

* `cylinder_eq_pi`: a word cylinder is the product box constraining the coordinates below the
  word's length.
* `bernoulliProduct_toMeasure`: the identification itself.
* `measurable_bernoulliProduct_toMeasure`: measurability of the family in `p`.
* `cylMass_bernoulliProduct_eq_pow`: cylinder masses depend only on the bit counts of the word.

Everything here is classical measure theory about `bernoulliProduct`; no computability content
enters.
-/

namespace ComputableAnalysis

open MeasureTheory ProbabilityTheory

/-- The constraint the word `s` places on coordinate `i`: the singleton `{s[i]}` inside the
word, and no constraint beyond it. -/
def cylinderCoord (s : List Bool) (i : ℕ) : Set Bool :=
  if h : i < s.length then {s[i]} else Set.univ

theorem measurableSet_cylinderCoord (s : List Bool) (i : ℕ) :
    MeasurableSet (cylinderCoord s i) := by
  unfold cylinderCoord; split <;> simp

/-- A word cylinder is the product box constraining the coordinates below `s.length`. -/
theorem cylinder_eq_pi (s : List Bool) :
    (cylinder s : Set Cantor) = Set.pi ↑(Finset.range s.length) (cylinderCoord s) := by
  ext x
  simp only [Set.mem_pi, Finset.coe_range, Set.mem_Iio, cylinderCoord]
  refine ⟨fun hx i hi => ?_, fun hx i hi => ?_⟩
  · rw [dif_pos hi]
    exact Set.mem_singleton_iff.mpr (hx i hi)
  · have h := hx i hi
    rw [dif_pos hi, Set.mem_singleton_iff] at h
    exact h

/-- The one-bit Bernoulli measure of the constraint at coordinate `i`. -/
theorem bernoulliMeasure_cylinderCoord (p : Set.Icc (0 : ℝ) 1) {s : List Bool} {i : ℕ}
    (hi : i < s.length) :
    bernoulliMeasure true false p (cylinderCoord s i)
      = ENNReal.ofReal (cond s[i] p.1 (1 - p.1)) := by
  classical
  rw [cylinderCoord, dif_pos hi, bernoulliMeasure_apply p (by simp)]
  cases hb : s[i] <;>
    simp [unitInterval.toNNReal, ENNReal.ofReal, Real.toNNReal_of_nonneg, p.2.1,
      sub_nonneg.mpr p.2.2] <;>
    rfl

/-- **The Bernoulli product is the infinite product of one-bit Bernoulli measures.** Both sides
are probability measures on Cantor space, so it suffices to compare cylinder masses. -/
theorem bernoulliProduct_toMeasure (p : Set.Icc (0 : ℝ) 1) :
    (bernoulliProduct p).toMeasure
      = Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p := by
  have hprob : IsProbabilityMeasure
      (Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p) := inferInstance
  suffices h : bernoulliProduct p = (⟨_, hprob⟩ : ProbabilityMeasure Cantor) from congrArg _ h
  refine cylMass_injective (funext fun s => ?_)
  have hfac : ∀ i : Fin s.length, (0 : ℝ) ≤ cond s[i] p.1 (1 - p.1) := fun i => by
    cases s[(i : ℕ)] <;> simp [p.2.1, sub_nonneg.mpr p.2.2]
  have hbox : (∏ i ∈ Finset.range s.length, bernoulliMeasure true false p (cylinderCoord s i))
      = ENNReal.ofReal (∏ i : Fin s.length, cond s[i] p.1 (1 - p.1)) := by
    rw [← Fin.prod_univ_eq_prod_range
        (fun i => bernoulliMeasure true false p (cylinderCoord s i)) s.length,
      ENNReal.ofReal_prod_of_nonneg fun i _ => hfac i]
    exact Finset.prod_congr rfl fun i _ => bernoulliMeasure_cylinderCoord p i.2
  change cylMass (bernoulliProduct p) s
    = ((Measure.infinitePi fun _ : ℕ => bernoulliMeasure true false p) (cylinder s)).toReal
  rw [cylMass_bernoulliProduct, cylinder_eq_pi,
    Measure.infinitePi_pi _ (fun i _ => measurableSet_cylinderCoord s i), hbox,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hfac i)]

/-- The Bernoulli family is measurable in its parameter — the measurability needed to form
Giry kernels over the parameter. -/
theorem measurable_bernoulliProduct_toMeasure :
    Measurable fun p : Set.Icc (0 : ℝ) 1 => (bernoulliProduct p).toMeasure := by
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_cantorCylinders.symm isPiSystem_cantorCylinders ?_
  rintro _ ⟨w, rfl⟩
  have hval : ∀ p : Set.Icc (0 : ℝ) 1, (bernoulliProduct p).toMeasure (cylinder w)
      = ENNReal.ofReal (∏ i : Fin w.length, cond w[i] p.1 (1 - p.1)) := fun p => by
    rw [← cylMass_bernoulliProduct p w, cylMass, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [hval]
  refine ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)
  refine continuous_finsetProd _ fun i _ => ?_
  cases w[(i : ℕ)] <;> simp only [Bool.cond_false, Bool.cond_true] <;> fun_prop

/-- A word-indexed product of two-valued weights collapses to powers, the exponents being the
bit counts of the word. -/
private theorem prod_cond_eq_pow_count {M : Type*} [CommMonoid M] (a b : M) (s : List Bool) :
    ∏ i : Fin s.length, cond s[i] a b = a ^ s.count true * b ^ s.count false := by
  simp only [Fin.getElem_fin]
  rw [← List.prod_ofFn (f := fun i : Fin s.length => cond s[(i : ℕ)] a b),
    List.ofFn_getElem_eq_map s fun c => cond c a b]
  induction s with
  | nil => simp
  | cons c t ih =>
    rw [List.map_cons, List.prod_cons, ih, List.count_cons, List.count_cons]
    cases c <;> simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- Cylinder masses of the Bernoulli product in terms of bit counts: only how many `true` and
`false` bits the word has matters, not their order. -/
theorem cylMass_bernoulliProduct_eq_pow (p : Set.Icc (0 : ℝ) 1) (s : List Bool) :
    cylMass (bernoulliProduct p) s = p.1 ^ s.count true * (1 - p.1) ^ s.count false := by
  rw [cylMass_bernoulliProduct, prod_cond_eq_pow_count]

end ComputableAnalysis
