/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.CylinderMass
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Existence: a probability measure from consistent cylinder masses

**Route B (Ionescu–Tulcea), pinned at the measure-existence feasibility review.** Given a
consistent cylinder-mass function `m`, the candidate measure is the trajectory measure
(`Kernel.trajMeasure`) of the history-dependent next-bit Bernoulli chain whose transition
parameter after the prefix `s` is `m (s ++ [true]) / m s` (an arbitrary default on
zero-mass prefixes, where consistency forces all extensions to mass zero anyway). The
prefix-mass equation `routeBMeasure hm (cylinder s) = ENNReal.ofReal (m s)` is proved by
induction on the word, through a one-step singleton recursion for `Kernel.partialTraj`
(`oneStep`/`comp_step` — private here; candidates for mathlib).

The construction is entirely private: the public statement is the frozen headline
`existsUnique_probabilityMeasure_of_isConsistent`, whose uniqueness half is
`cylMass_injective` from `CylinderMass.lean`.

Implementation note: the Ionescu–Tulcea API (`partialTraj`, `frestrictLe`, `IicProdIoc`,
`piSingleton`) carries an implicit family `X : ℕ → Type`, and `Π i : Iic n, ?X i` does
not pattern-unify with `↥(Iic n) → Bool`; the constant family `B` pins it down explicitly
at every fresh statement.
-/

open MeasureTheory ProbabilityTheory Finset Preorder unitInterval
open scoped NNReal ENNReal

namespace ComputableAnalysis

/-- The constant-`Bool` factor family, pinning down the higher-order implicit arguments of
`partialTraj` / `frestrictLe` / `IicProdIoc`. -/
private abbrev B : ℕ → Type := fun _ => Bool

variable {m : List Bool → ℝ}

/-- Next-bit Bernoulli parameter: conditional probability of `true` after the prefix
`s`. -/
private noncomputable def nextP (m : List Bool → ℝ) (s : List Bool) : ℝ≥0 :=
  (if m s = 0 then 0 else m (s ++ [true]) / m s).toNNReal

private theorem nextP_le_one (hm : IsConsistentCylinderMass m) (s : List Bool) :
    nextP m s ≤ 1 := by
  unfold nextP
  split
  · simp
  · rename_i h
    have h0 : 0 < m s := lt_of_le_of_ne (hm.2.1 s) (Ne.symm h)
    have h1 : m (s ++ [true]) ≤ m s := IsConsistentCylinderMass.append_le hm s true
    exact Real.toNNReal_le_one.mpr ((div_le_one h0).mpr h1)

/-- The word (of length `n + 1`) read off a history point. -/
private def word {n : ℕ} (x : ∀ _ : Iic n, Bool) : List Bool :=
  List.ofFn fun j : Fin (n + 1) => x ⟨j.1, mem_Iic.mpr (Nat.lt_succ_iff.mp j.2)⟩

/-- The next-bit parameter as a point of the unit interval. -/
private noncomputable def nextPI (hm : IsConsistentCylinderMass m) (s : List Bool) : I :=
  ⟨(nextP m s : ℝ), ⟨(nextP m s).coe_nonneg, by exact_mod_cast nextP_le_one hm s⟩⟩

/-- The history-dependent next-bit Bernoulli transition kernels. -/
private noncomputable def kernels (hm : IsConsistentCylinderMass m) (n : ℕ) :
    Kernel (∀ _ : Iic n, Bool) Bool :=
  Kernel.ofFunOfCountable fun x => bernoulliMeasure true false (nextPI hm (word x))

private lemma kernels_apply (hm : IsConsistentCylinderMass m) (n : ℕ)
    (x : ∀ _ : Iic n, Bool) :
    kernels hm n x = bernoulliMeasure true false (nextPI hm (word x)) := rfl

private instance (hm : IsConsistentCylinderMass m) (n : ℕ) : IsMarkovKernel (kernels hm n) :=
  ⟨fun x => by rw [kernels_apply]; infer_instance⟩

/-- Initial distribution of bit 0. -/
private noncomputable def init (hm : IsConsistentCylinderMass m) : Measure Bool :=
  bernoulliMeasure true false (nextPI hm [])

private instance (hm : IsConsistentCylinderMass m) : IsProbabilityMeasure (init hm) := by
  rw [init]; infer_instance

/-- The route B candidate: the Ionescu–Tulcea trajectory measure. -/
private noncomputable def routeBMeasure (hm : IsConsistentCylinderMass m) : Measure Cantor :=
  Kernel.trajMeasure (X := B) (init hm) (kernels hm)

private instance (hm : IsConsistentCylinderMass m) :
    IsProbabilityMeasure (routeBMeasure hm) := by
  rw [routeBMeasure]; infer_instance

/-- The history point of a word of length `n + 1`. -/
private def hist (s : List Bool) {n : ℕ} (hn : s.length = n + 1) : ∀ _ : Iic n, Bool :=
  fun i => s[i.1]'(by have := mem_Iic.mp i.2; omega)

private theorem word_hist (s : List Bool) {n : ℕ} (hn : s.length = n + 1) :
    word (hist s hn) = s := by
  refine List.ext_getElem (by simp [word, hn]) fun i h1 h2 => ?_
  simp only [word, List.getElem_ofFn]
  rfl

private theorem cylinder_eq_preimage_frestrictLe {s : List Bool} {n : ℕ}
    (hn : s.length = n + 1) :
    (cylinder s : Set Cantor) = Preorder.frestrictLe (π := B) n ⁻¹' {hist s hn} := by
  ext p
  simp only [cylinder, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hp
    funext i
    exact hp i.1 (by have := mem_Iic.mp i.2; omega)
  · intro hp i hi
    exact congrFun hp ⟨i, mem_Iic.mpr (by omega)⟩

/-! ### Bernoulli singleton masses and the mass-step arithmetic -/

private lemma mequiv_preimage_singleton {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (y : β) : ⇑e ⁻¹' ({y} : Set β) = {e.symm y} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  exact ⟨fun h => by rw [← h, MeasurableEquiv.symm_apply_apply],
    fun h => by rw [h, MeasurableEquiv.apply_symm_apply]⟩

private lemma toNNReal_coe_ennreal (p : I) :
    ((toNNReal p : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (p : ℝ) := by
  rw [← coe_toNNReal p, ENNReal.ofReal_coe_nnreal]

private lemma bernoulliMeasure_singleton (p : I) (b : Bool) :
    bernoulliMeasure true false p ({b} : Set Bool) =
      ENNReal.ofReal (cond b (p : ℝ) (1 - (p : ℝ))) := by
  cases b
  · rw [Bool.cond_false,
      bernoulliMeasure_apply_of_notMem_of_mem p (measurableSet_singleton _) (by simp) rfl,
      toNNReal_coe_ennreal, coe_symm_eq]
  · rw [Bool.cond_true,
      bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton _) rfl (by simp),
      toNNReal_coe_ennreal]

/-- The mass-step arithmetic: extending a prefix by one bit multiplies its mass by the
corresponding Bernoulli singleton mass (degenerate `m t = 0` case included). -/
private lemma bernoulliStep (hm : IsConsistentCylinderMass m) (t : List Bool) (b : Bool) :
    ENNReal.ofReal (m t) * bernoulliMeasure true false (nextPI hm t) ({b} : Set Bool) =
      ENNReal.ofReal (m (t ++ [b])) := by
  rw [bernoulliMeasure_singleton]
  rcases eq_or_lt_of_le (hm.2.1 t) with h0 | h0
  · have hb : m (t ++ [b]) = 0 :=
      le_antisymm ((IsConsistentCylinderMass.append_le hm t b).trans h0.ge) (hm.2.1 _)
    rw [hb, ← h0]
    simp
  · have hne : m t ≠ 0 := ne_of_gt h0
    have hq : ((nextPI hm t : ℝ)) = m (t ++ [true]) / m t := by
      change ((nextP m t : ℝ)) = _
      unfold nextP
      rw [ite_eq_right hne]
      exact Real.coe_toNNReal _ (div_nonneg (hm.2.1 _) h0.le)
    have hsplit := hm.2.2 t
    rw [← ENNReal.ofReal_mul (hm.2.1 t)]
    congr 1
    cases b
    · rw [Bool.cond_false, hq]
      have hexp : m t * (1 - m (t ++ [true]) / m t) = m t - m (t ++ [true]) := by
        field_simp
      rw [hexp]
      linarith
    · rw [Bool.cond_true, hq, mul_comm, div_mul_cancel₀ _ hne]

/-! ### The one-step singleton recursion for `partialTraj` -/

private lemma oneStep (hm : IsConsistentCylinderMass m) {n : ℕ}
    (x : ∀ _ : Iic n, Bool) (y : ∀ _ : Iic (n + 1), Bool) :
    Kernel.partialTraj (X := B) (kernels hm) n (n + 1) x {y} =
      Measure.dirac x {frestrictLe₂ (π := B) (Nat.le_succ n) y} *
        kernels hm n (frestrictLe₂ (π := B) (Nat.le_succ n) y)
          ({y ⟨n + 1, mem_Iic.mpr le_rfl⟩} : Set Bool) := by
  rw [Kernel.partialTraj_succ_self,
    Kernel.map_apply' _ (measurable_IicProdIoc (X := B)) _ (measurableSet_singleton y)]
  have hpre : IicProdIoc (X := B) n (n + 1) ⁻¹' ({y} : Set _) =
      ({frestrictLe₂ (π := B) (Nat.le_succ n) y} : Set _) ×ˢ
        ({restrict₂ (π := B) Ioc_subset_Iic_self y} : Set _) := by
    rw [← MeasurableEquiv.coe_IicProdIoc (X := B) (Nat.le_succ n),
      mequiv_preimage_singleton, Set.singleton_prod_singleton]
    rfl
  rw [hpre, Kernel.prod_apply, Measure.prod_prod, Kernel.id_apply]
  by_cases hx : x = frestrictLe₂ (π := B) (Nat.le_succ n) y
  · subst hx
    congr 1
    rw [Kernel.map_apply' _ (MeasurableEquiv.piSingleton (X := B) n).measurable _
      (measurableSet_singleton _), mequiv_preimage_singleton]
    rfl
  · rw [Measure.dirac_apply' _ (measurableSet_singleton _),
      Set.indicator_of_notMem (by simpa using hx), zero_mul, zero_mul]

private lemma comp_step (hm : IsConsistentCylinderMass m) {n : ℕ}
    (ρ : Measure (∀ _ : Iic n, Bool)) (y : ∀ _ : Iic (n + 1), Bool) :
    (Kernel.partialTraj (X := B) (kernels hm) n (n + 1) ∘ₘ ρ) {y} =
      ρ {frestrictLe₂ (π := B) (Nat.le_succ n) y} *
        kernels hm n (frestrictLe₂ (π := B) (Nat.le_succ n) y)
          ({y ⟨n + 1, mem_Iic.mpr le_rfl⟩} : Set Bool) := by
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _)]
  have hcong : ∀ x, Kernel.partialTraj (X := B) (kernels hm) n (n + 1) x {y} =
      ({frestrictLe₂ (π := B) (Nat.le_succ n) y} : Set _).indicator
        (fun z => kernels hm n z ({y ⟨n + 1, mem_Iic.mpr le_rfl⟩} : Set Bool)) x := by
    intro x
    rw [oneStep hm x y]
    by_cases hx : x = frestrictLe₂ (π := B) (Nat.le_succ n) y
    · rw [hx, Set.indicator_of_mem (Set.mem_singleton _),
        Measure.dirac_apply_of_mem (Set.mem_singleton _), one_mul]
    · rw [Set.indicator_of_notMem (by simpa using hx),
        Measure.dirac_apply' _ (measurableSet_singleton _),
        Set.indicator_of_notMem (by simpa using hx), zero_mul]
  rw [lintegral_congr hcong, lintegral_indicator (measurableSet_singleton _),
    lintegral_singleton, mul_comm]

/-! ### Marginals of the trajectory measure -/

private lemma routeB_preimage (hm : IsConsistentCylinderMass m) (n : ℕ)
    (y : ∀ _ : Iic n, Bool) :
    routeBMeasure hm (Preorder.frestrictLe (π := B) n ⁻¹' {y}) =
      (Kernel.partialTraj (X := B) (kernels hm) 0 n ∘ₘ
        ((init hm).map (MeasurableEquiv.piUnique (fun _ : Iic 0 => Bool)).symm)) {y} := by
  rw [routeBMeasure, Kernel.trajMeasure,
    ← Measure.map_apply (measurable_frestrictLe n) (measurableSet_singleton y),
    Measure.map_comp _ _ (measurable_frestrictLe n), Kernel.traj_map_frestrictLe]

/-- Prefix masses of the composed marginal measures, by induction on the length. -/
private lemma partialTraj_comp_singleton (hm : IsConsistentCylinderMass m) :
    ∀ (n : ℕ) (s : List Bool) (hn : s.length = n + 1),
      (Kernel.partialTraj (X := B) (kernels hm) 0 n ∘ₘ
        ((init hm).map (MeasurableEquiv.piUnique (fun _ : Iic 0 => Bool)).symm))
        {hist s hn} = ENNReal.ofReal (m s) := by
  intro n
  induction n with
  | zero =>
    intro s hn
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hn
    rw [Kernel.partialTraj_self, Measure.id_comp,
      Measure.map_apply (MeasurableEquiv.measurable _) (measurableSet_singleton _),
      mequiv_preimage_singleton, MeasurableEquiv.symm_symm]
    have hb : (MeasurableEquiv.piUnique (fun _ : Iic 0 => Bool)) (hist [b] hn) = b := by
      have hd : ((default : Iic 0) : ℕ) = 0 :=
        Nat.le_zero.mp (mem_Iic.mp (default : Iic 0).2)
      change hist [b] hn default = b
      simp [hist, hd]
    rw [hb]
    change bernoulliMeasure true false (nextPI hm []) ({b} : Set Bool) = ENNReal.ofReal (m [b])
    have hstep := bernoulliStep hm [] b
    rw [hm.1, ENNReal.ofReal_one, one_mul, List.nil_append] at hstep
    exact hstep
  | succ n ih =>
    intro s hn
    have hs0 : s ≠ [] := by
      intro h
      rw [h] at hn
      simp at hn
    obtain ⟨t, b, rfl⟩ : ∃ t b, s = t ++ [b] :=
      ⟨s.dropLast, s.getLast hs0, (List.dropLast_append_getLast hs0).symm⟩
    have ht : t.length = n + 1 := by simpa using hn
    rw [Kernel.partialTraj_succ_eq_comp (Nat.zero_le n), ← Measure.comp_assoc,
      comp_step hm]
    have h1 : frestrictLe₂ (π := B) (Nat.le_succ n) (hist (t ++ [b]) hn) = hist t ht := by
      funext i
      have hi : i.1 < t.length := by have := mem_Iic.mp i.2; omega
      exact List.getElem_append_left hi
    have h2 : hist (t ++ [b]) hn ⟨n + 1, mem_Iic.mpr le_rfl⟩ = b := by
      simp only [hist]
      rw [List.getElem_append_right (by omega)]
      simp [ht]
    rw [h1, h2, ih t ht, kernels_apply, word_hist]
    exact bernoulliStep hm t b

/-- The prefix-mass equation for the route B measure. -/
private theorem routeBMeasure_cylinder (hm : IsConsistentCylinderMass m) (s : List Bool) :
    routeBMeasure hm (cylinder s) = ENNReal.ofReal (m s) := by
  cases s with
  | nil =>
    rw [cylinder_nil, measure_univ, hm.1, ENNReal.ofReal_one]
  | cons a t =>
    have hn : (a :: t).length = t.length + 1 := by simp
    rw [cylinder_eq_preimage_frestrictLe hn, routeB_preimage hm t.length _,
      partialTraj_comp_singleton hm t.length _ hn]

/-! ### The frozen headline -/

/-- **Existence and uniqueness** (unit 19 headline). Every consistent cylinder-mass
function is the cylinder-mass function of exactly one probability measure on Cantor
space. Existence is route B (Ionescu–Tulcea, pinned at the measure-existence feasibility
review); uniqueness is `cylMass_injective` from unit 18. -/
theorem existsUnique_probabilityMeasure_of_isConsistent {m : List Bool → ℝ}
    (hm : IsConsistentCylinderMass m) :
    ∃! μ : ProbabilityMeasure Cantor, ∀ s, cylMass μ s = m s := by
  have hμ₀ : ∀ s, cylMass ⟨routeBMeasure hm, inferInstance⟩ s = m s := fun s => by
    change ((routeBMeasure hm) (cylinder s)).toReal = m s
    rw [routeBMeasure_cylinder hm s, ENNReal.toReal_ofReal (hm.2.1 s)]
  exact ⟨_, hμ₀, fun ν hν => cylMass_injective (funext fun s => (hν s).trans (hμ₀ s).symm)⟩

end ComputableAnalysis
