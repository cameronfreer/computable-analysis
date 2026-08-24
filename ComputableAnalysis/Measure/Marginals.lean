/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.WeakRepresentation
import ComputableAnalysis.RepresentedSpace.ComputableMap
import ComputableAnalysis.TypeTwo.Universal
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Computable marginals of a joint law

Both marginals of a joint probability law are computable from its weak name: project every
decoded atom to the corresponding dense index, coordinatewise on the name. The pinned
Lévy–Prokhorov rate survives because each projection is `1`-Lipschitz for the max product metric,
hence LP nonexpansive.

## Main definitions and results

* `ComputableMetricPresentation.borelSpace_prod` — the product-Borel structure of a pair of
  presentations, always DERIVED and never a hypothesis.  It lives here because the marginal
  statements are the first to need it.
* `fstMarginal`, `sndMarginal` and their `toMeasure` specifications.
* `computableMap_fstMarginal`, `computableMap_sndMarginal`.

## Implementation notes

The list plumbing is shared — one `projListWith` and one weight lemma, since the normalizing
constant does not see the index component at all. The two *semantic* atomic lemmas are kept
concrete, because an arbitrary index map has no relationship to `P.dense` or `Q.dense`: only the
two projections do.

Everything is proved through the canonical weak-representation API (`atomicOfList`,
`toMeasure_atomicOfList_of_ne_zero`, `toMeasure_atomicOfList_of_eq_zero`,
`atomic_encode_eq_atomicOfList`, `clampedWeight`, `clampedWeightSum`), so this module introduces
no further private copy of the atomic-evaluation layer.
-/

open MeasureTheory Metric Encodable Denumerable

namespace ComputableAnalysis

open OracleCode

section Marginals

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-! ### The derived product-Borel structure -/

section ProductBorel

variable (P : ComputableMetricPresentation X)

include P in
/-- The Borel structure of the presented product: second countability of the first
factor comes from its dense sequence, so `Prod.borelSpace` applies. Always derived,
never a hypothesis. -/
theorem ComputableMetricPresentation.borelSpace_prod : BorelSpace (X × Y) := by
  have := P.separableSpace
  have : SecondCountableTopology X := UniformSpace.secondCountable_of_separable X
  exact Prod.borelSpace

end ProductBorel

/-! ### The bundled marginals -/

/-- The first marginal of a joint probability law, bundled. -/
noncomputable def fstMarginal (μ : ProbabilityMeasure (X × Y)) :
    ProbabilityMeasure X := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  exact ⟨μ.toMeasure.fst, inferInstance⟩

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The bundled first marginal is `Measure.fst`. -/
@[simp]
theorem fstMarginal_toMeasure (μ : ProbabilityMeasure (X × Y)) :
    (fstMarginal μ).toMeasure = μ.toMeasure.fst := rfl

/-- The second marginal of a joint probability law, bundled. -/
noncomputable def sndMarginal (μ : ProbabilityMeasure (X × Y)) :
    ProbabilityMeasure Y := by
  haveI : IsProbabilityMeasure μ.toMeasure := μ.prop
  exact ⟨μ.toMeasure.snd, inferInstance⟩

omit [MetricSpace X] [BorelSpace X] [MetricSpace Y] [BorelSpace Y] in
/-- The bundled second marginal is `Measure.snd`. -/
@[simp]
theorem sndMarginal_toMeasure (μ : ProbabilityMeasure (X × Y)) :
    (sndMarginal μ).toMeasure = μ.toMeasure.snd := rfl

/-! ### Lévy–Prokhorov nonexpansiveness of the two projections -/

omit [BorelSpace Y] in
/-- The first-marginal projection is Lévy–Prokhorov nonexpansive: `Prod.fst` is `1`-Lipschitz
for the max product metric, so thickenings of preimages land in preimages of thickenings. -/
private theorem levyProkhorovEDist_fst_le (μ ν : Measure (X × Y)) :
    levyProkhorovEDist μ.fst ν.fst ≤ levyProkhorovEDist μ ν := by
  apply sInf_le_sInf
  intro ε hε
  simp only [Set.mem_ofPred_eq] at hε ⊢
  intro A hA
  have step : ∀ ρ σ : Measure (X × Y),
      ρ (Prod.fst ⁻¹' A) ≤ σ (thickening ε.toReal (Prod.fst ⁻¹' A)) + ε →
      ρ.fst A ≤ σ.fst (thickening ε.toReal A) + ε := by
    intro ρ σ h
    rw [Measure.fst_apply hA, Measure.fst_apply isOpen_thickening.measurableSet]
    refine h.trans (add_le_add (measure_mono fun z hz => ?_) le_rfl)
    obtain ⟨w, hw, hdist⟩ := Metric.mem_thickening_iff.mp hz
    have hle : dist z.1 w.1 ≤ dist z w := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    exact Set.mem_preimage.mpr
      (Metric.mem_thickening_iff.mpr ⟨w.1, hw, lt_of_le_of_lt hle hdist⟩)
  obtain ⟨h₁, h₂⟩ := hε (Prod.fst ⁻¹' A) (measurable_fst hA)
  exact ⟨step μ ν h₁, step ν μ h₂⟩

omit [BorelSpace X] in
/-- The second-marginal projection is Lévy–Prokhorov nonexpansive. -/
private theorem levyProkhorovEDist_snd_le (μ ν : Measure (X × Y)) :
    levyProkhorovEDist μ.snd ν.snd ≤ levyProkhorovEDist μ ν := by
  apply sInf_le_sInf
  intro ε hε
  simp only [Set.mem_ofPred_eq] at hε ⊢
  intro A hA
  have step : ∀ ρ σ : Measure (X × Y),
      ρ (Prod.snd ⁻¹' A) ≤ σ (thickening ε.toReal (Prod.snd ⁻¹' A)) + ε →
      ρ.snd A ≤ σ.snd (thickening ε.toReal A) + ε := by
    intro ρ σ h
    rw [Measure.snd_apply hA, Measure.snd_apply isOpen_thickening.measurableSet]
    refine h.trans (add_le_add (measure_mono fun z hz => ?_) le_rfl)
    obtain ⟨w, hw, hdist⟩ := Metric.mem_thickening_iff.mp hz
    have hle : dist z.2 w.2 ≤ dist z w := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    exact Set.mem_preimage.mpr
      (Metric.mem_thickening_iff.mpr ⟨w.2, hw, lt_of_le_of_lt hle hdist⟩)
  obtain ⟨h₁, h₂⟩ := hε (Prod.snd ⁻¹' A) (measurable_snd hA)
  exact ⟨step μ ν h₁, step ν μ h₂⟩

omit [BorelSpace Y] in
/-- The metric form of the first-marginal LP nonexpansiveness. -/
private theorem levyProkhorovDist_fst_le (μ ν : Measure (X × Y)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    levyProkhorovDist μ.fst ν.fst ≤ levyProkhorovDist μ ν :=
  ENNReal.toReal_mono (levyProkhorovEDist_ne_top _ _) (levyProkhorovEDist_fst_le μ ν)

omit [BorelSpace X] in
/-- The metric form of the second-marginal LP nonexpansiveness. -/
private theorem levyProkhorovDist_snd_le (μ ν : Measure (X × Y)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    levyProkhorovDist μ.snd ν.snd ≤ levyProkhorovDist μ ν :=
  ENNReal.toReal_mono (levyProkhorovEDist_ne_top _ _) (levyProkhorovEDist_snd_le μ ν)

/-! ### Shared list plumbing

The normalizing constant never looks at the index component, so one weight lemma covers both
projections. -/

/-- Reindex a decoded atom list, keeping every weight code. -/
private def projListWith (f : ℕ → ℕ) (l : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  l.map fun pr => (f pr.1, pr.2)

private theorem length_projListWith (f : ℕ → ℕ) (l : List (ℕ × ℕ)) :
    (projListWith f l).length = l.length := List.length_map ..

private theorem clampedWeightSum_projListWith (f : ℕ → ℕ) (l : List (ℕ × ℕ)) :
    clampedWeightSum (projListWith f l) = clampedWeightSum l := by
  unfold clampedWeightSum projListWith
  rw [List.map_map]
  rfl

private theorem getElem_projListWith (f : ℕ → ℕ) (l : List (ℕ × ℕ)) (i : ℕ)
    (h : i < (projListWith f l).length) :
    (projListWith f l)[i]
      = (f (l[i]'(by rwa [length_projListWith] at h)).1,
          (l[i]'(by rwa [length_projListWith] at h)).2) :=
  List.getElem_map _

private theorem computable_projWithCode {f : ℕ → ℕ} (hf : Primrec f) :
    Computable fun v => Encodable.encode (projListWith f (ofNat (List (ℕ × ℕ)) v)) := by
  have hmap : Primrec fun v => projListWith f (ofNat (List (ℕ × ℕ)) v) :=
    Primrec.list_map ((Primrec.ofNat (List (ℕ × ℕ))).comp Primrec.id)
      (((hf.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)).to₂)
  exact (Primrec.encode.comp hmap).to_comp

/-! ### The two atomic projections

Each of these is concrete: an arbitrary index map has no relationship to `P.dense` or
`Q.dense`, so these identities hold for the two coordinate projections alone. -/

omit [BorelSpace X] [BorelSpace Y] in
/-- **The first marginal of a decoded atomic on the presented product** is the decoded
atomic of the first-index-projected list on the first factor. -/
private theorem fst_atomicOfList (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) (l : List (ℕ × ℕ)) :
    (atomicOfList (P.prod Q) l).toMeasure.fst
      = (atomicOfList P (projListWith (fun i => i.unpair.1) l)).toMeasure := by
  by_cases h0 : clampedWeightSum l = 0
  · rw [toMeasure_atomicOfList_of_eq_zero _ h0,
      toMeasure_atomicOfList_of_eq_zero _
        ((clampedWeightSum_projListWith _ l).trans h0),
      Measure.fst, Measure.map_dirac' measurable_fst]
    have hpt : ((P.prod Q).dense 0).1 = P.dense 0 := by
      change P.dense (Nat.unpair 0).1 = P.dense 0
      norm_num
    rw [hpt]
  · have h0' : clampedWeightSum (projListWith (fun i => i.unpair.1) l) ≠ 0 := by
      rw [clampedWeightSum_projListWith]; exact h0
    rw [toMeasure_atomicOfList_of_ne_zero _ h0, toMeasure_atomicOfList_of_ne_zero _ h0',
      ← Measure.sum_fintype, Measure.fst_sum, Measure.sum_fintype,
      ← Fin.sum_congr' _ (length_projListWith (fun i => i.unpair.1) l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.fst, Measure.map_smul, Measure.map_dirac' measurable_fst,
      clampedWeightSum_projListWith]
    simp only [Fin.getElem_fin, Fin.val_cast]
    rw [getElem_projListWith]
    rfl

omit [BorelSpace X] [BorelSpace Y] in
/-- **The second marginal of a decoded atomic on the presented product** is the decoded
atomic of the second-index-projected list on the second factor. -/
private theorem snd_atomicOfList (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) (l : List (ℕ × ℕ)) :
    (atomicOfList (P.prod Q) l).toMeasure.snd
      = (atomicOfList Q (projListWith (fun i => i.unpair.2) l)).toMeasure := by
  by_cases h0 : clampedWeightSum l = 0
  · rw [toMeasure_atomicOfList_of_eq_zero _ h0,
      toMeasure_atomicOfList_of_eq_zero _
        ((clampedWeightSum_projListWith _ l).trans h0),
      Measure.snd, Measure.map_dirac' measurable_snd]
    have hpt : ((P.prod Q).dense 0).2 = Q.dense 0 := by
      change Q.dense (Nat.unpair 0).2 = Q.dense 0
      norm_num
    rw [hpt]
  · have h0' : clampedWeightSum (projListWith (fun i => i.unpair.2) l) ≠ 0 := by
      rw [clampedWeightSum_projListWith]; exact h0
    rw [toMeasure_atomicOfList_of_ne_zero _ h0, toMeasure_atomicOfList_of_ne_zero _ h0',
      ← Measure.sum_fintype, Measure.snd_sum, Measure.sum_fintype,
      ← Fin.sum_congr' _ (length_projListWith (fun i => i.unpair.2) l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.snd, Measure.map_smul, Measure.map_dirac' measurable_snd,
      clampedWeightSum_projListWith]
    simp only [Fin.getElem_fin, Fin.val_cast]
    rw [getElem_projListWith]
    rfl

/-! ### The two computability theorems -/

/-- **The first marginal is computable** from the weak name of the joint law: project
every decoded atom to its first dense index (coordinatewise on the name); LP
nonexpansiveness of `Prod.fst` preserves the pinned rate. -/
theorem computableMap_fstMarginal (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    ComputableMap
      (haveI : BorelSpace (X × Y) := P.borelSpace_prod
       weakMeasureRep (P.prod Q))
      (weakMeasureRep P) fstMarginal := by
  have : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨gC, hgC⟩ := exists_ofNatFnCode (computable_projWithCode primrec_unpairFst)
  refine ⟨.comp gC .query, fun p μ hpμ => ?_⟩
  have hM := (weakMeasureRep_names_iff (P.prod Q)).mp hpμ
  refine ⟨fun n => Encodable.encode
      (projListWith (fun i => i.unpair.1) (ofNat (List (ℕ × ℕ)) (p n))),
    mem_evalStream.mpr fun n => ?_, ?_⟩
  · rw [eval_comp_some (eval_query p n), hgC]
    exact Part.mem_some _
  · refine (weakMeasureRep_names_iff P).mpr fun n => ?_
    have : IsProbabilityMeasure μ.toMeasure := μ.prop
    have : IsProbabilityMeasure (atomic (P.prod Q) (p n)).toMeasure :=
      (atomic (P.prod Q) (p n)).prop
    have hproj : (atomic P (Encodable.encode (projListWith (fun i => i.unpair.1)
        (ofNat (List (ℕ × ℕ)) (p n))))).toMeasure
          = (atomic (P.prod Q) (p n)).toMeasure.fst := by
      rw [atomic_encode_eq_atomicOfList, atomic, fst_atomicOfList P Q]
    rw [fstMarginal_toMeasure, hproj]
    calc levyProkhorovDist μ.toMeasure.fst (atomic (P.prod Q) (p n)).toMeasure.fst
        ≤ levyProkhorovDist μ.toMeasure (atomic (P.prod Q) (p n)).toMeasure :=
          levyProkhorovDist_fst_le _ _
      _ ≤ (2 : ℝ)⁻¹ ^ n := hM n

/-- **The second marginal is computable** from the weak name of the joint law: project
every decoded atom to its second dense index (coordinatewise on the name); LP
nonexpansiveness of `Prod.snd` preserves the pinned rate. -/
theorem computableMap_sndMarginal (P : ComputableMetricPresentation X)
    (Q : ComputableMetricPresentation Y) :
    ComputableMap
      (haveI : BorelSpace (X × Y) := P.borelSpace_prod
       weakMeasureRep (P.prod Q))
      (weakMeasureRep Q) sndMarginal := by
  have : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨gC, hgC⟩ := exists_ofNatFnCode (computable_projWithCode primrec_unpairSnd)
  refine ⟨.comp gC .query, fun p μ hpμ => ?_⟩
  have hM := (weakMeasureRep_names_iff (P.prod Q)).mp hpμ
  refine ⟨fun n => Encodable.encode
      (projListWith (fun i => i.unpair.2) (ofNat (List (ℕ × ℕ)) (p n))),
    mem_evalStream.mpr fun n => ?_, ?_⟩
  · rw [eval_comp_some (eval_query p n), hgC]
    exact Part.mem_some _
  · refine (weakMeasureRep_names_iff Q).mpr fun n => ?_
    have : IsProbabilityMeasure μ.toMeasure := μ.prop
    have : IsProbabilityMeasure (atomic (P.prod Q) (p n)).toMeasure :=
      (atomic (P.prod Q) (p n)).prop
    have hproj : (atomic Q (Encodable.encode (projListWith (fun i => i.unpair.2)
        (ofNat (List (ℕ × ℕ)) (p n))))).toMeasure
          = (atomic (P.prod Q) (p n)).toMeasure.snd := by
      rw [atomic_encode_eq_atomicOfList, atomic, snd_atomicOfList P Q]
    rw [sndMarginal_toMeasure, hproj]
    calc levyProkhorovDist μ.toMeasure.snd (atomic (P.prod Q) (p n)).toMeasure.snd
        ≤ levyProkhorovDist μ.toMeasure (atomic (P.prod Q) (p n)).toMeasure :=
          levyProkhorovDist_snd_le _ _
      _ ≤ (2 : ℝ)⁻¹ ^ n := hM n

end Marginals

end ComputableAnalysis
