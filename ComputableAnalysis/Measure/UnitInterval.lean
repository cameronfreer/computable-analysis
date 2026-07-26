/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.WeakRepresentation
import ComputableAnalysis.Metric.RatCodeArith
import ComputableAnalysis.Metric.Real
import ComputableAnalysis.RepresentedSpace.Equivalence

/-!
# A computable metric presentation of the unit interval

`unitIntervalRep` represents `[0, 1]` as a subtype of the represented reals, but a
`ComputableMetricPresentation` of the interval itself is a different object, and it is what
`weakMeasureRep` needs in order to represent `ProbabilityMeasure (Set.Icc (0 : ℝ) 1)`.

The presentation's dense sequence enumerates the rationals clamped into `[0, 1]`. Because
clamping is a retraction onto `[0, 1]` and 1-Lipschitz, density transfers from the rationals,
and because distances between clamped dense points are exactly distances between the
corresponding `realPresentation` dense points, both threshold semidecisions reduce to the
real presentation's own — no new coded-rational encoding is introduced, and the code-level
clamp comes from `Metric/RatCodeArith.lean`.

Main results:

* `unitIntervalPresentation`: the presentation itself.
* `unitIntervalMeasureRep`: the weak (Lévy–Prokhorov) representation it induces on
  probability measures.
* `unitIntervalPresentation_cauchyRep_equiv`: its Cauchy representation agrees with
  `unitIntervalRep`, so point names transfer between the two.
-/

namespace ComputableAnalysis

open MeasureTheory

/-- The rational `q`, clamped into the unit interval — the dense sequence of the
presentation. -/
noncomputable def unitClamp (q : ℚ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 (q : ℝ)), clamp_mem_Icc _⟩

/-- The value of `unitClamp q` is the clamped cast of `q`. -/
private theorem unitClamp_val (q : ℚ) : (unitClamp q : ℝ) = max 0 (min 1 (q : ℝ)) := rfl

/-- A clamped rational is at least as close to a point of `[0, 1]` as the rational is —
1-Lipschitzness of clamping, together with the fact that it fixes `[0, 1]`. -/
private theorem dist_unitClamp_le {q : ℚ} {x : Set.Icc (0 : ℝ) 1} :
    dist (unitClamp q) x ≤ |(q : ℝ) - x.val| := by
  have h := abs_clamp_sub_clamp_le (q : ℝ) x.val
  rw [clamp_eq_self x.property] at h
  rw [Subtype.dist_eq, Real.dist_eq, unitClamp_val]
  exact h

/-- The `realPresentation` dense point at a clamped code is the value of the corresponding
clamped rational in `[0, 1]`. -/
private theorem realPresentation_dense_clampCode (m : ℕ) :
    realPresentation.dense (clampCode m) = (unitClamp (ratOfCode m) : ℝ) := by
  change ((ratOfCode (clampCode m) : ℚ) : ℝ) = _
  rw [ratOfCode_clampCode, unitClamp_val]
  push_cast
  rfl

/-- Distances between clamped dense points are distances between the corresponding
`realPresentation` dense points — which is what makes both semidecisions inherited. -/
private theorem dist_unitClamp_eq (a b : ℕ) :
    dist (unitClamp (ratOfCode a)) (unitClamp (ratOfCode b))
      = dist (realPresentation.dense (clampCode a)) (realPresentation.dense (clampCode b)) := by
  rw [realPresentation_dense_clampCode, realPresentation_dense_clampCode, Subtype.dist_eq]

/-- Reindexing a threshold triple by `clampCode` in both point coordinates is computable. -/
private theorem computable_clampPair :
    Computable fun w : ℕ × ℕ × RatCode => (clampCode w.1, clampCode w.2.1, w.2.2) := by
  have hc : Computable clampCode := primrec_clampCode.to_comp
  exact (hc.comp Computable.fst).pair
    ((hc.comp (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.snd))

/-- **The computable metric presentation of `[0, 1]`**, with dense points the clamped
rationals. Both threshold semidecisions are the real presentation's own, reindexed by
`clampCode`. -/
noncomputable def unitIntervalPresentation :
    ComputableMetricPresentation (Set.Icc (0 : ℝ) 1) where
  dense m := unitClamp (ratOfCode m)
  denseRange := by
    refine Metric.denseRange_iff.mpr fun x ε hε => ?_
    obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn (show x.val - ε < x.val + ε by linarith)
    obtain ⟨m, rfl⟩ := ratOfCode_surjective q
    refine ⟨m, ?_⟩
    rw [dist_comm]
    refine lt_of_le_of_lt dist_unitClamp_le ?_
    rw [abs_lt]
    constructor <;> linarith
  ltSemidec :=
    (repred_comp realPresentation.ltSemidec computable_clampPair).of_eq fun w => by
      rw [dist_unitClamp_eq]
  gtSemidec :=
    (repred_comp realPresentation.gtSemidec computable_clampPair).of_eq fun w => by
      rw [dist_unitClamp_eq]

/-- The weak (Lévy–Prokhorov) representation of probability measures on the unit interval. -/
noncomputable def unitIntervalMeasureRep :
    Representation (ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :=
  weakMeasureRep unitIntervalPresentation

/-- Names of `unitIntervalPresentation.cauchyRep` are the clamped fast approximation
streams. -/
private theorem unitIntervalPresentation_names_iff {p : Baire} {x : Set.Icc (0 : ℝ) 1} :
    unitIntervalPresentation.cauchyRep.Names p x ↔
      ∀ n : ℕ, dist (unitClamp (ratOfCode (p n))) x ≤ ((2 : ℝ)⁻¹) ^ n :=
  unitIntervalPresentation.cauchyRep_names_iff

/-- Names of `unitIntervalRep` are the fast approximation streams of the underlying real. -/
private theorem unitIntervalRep_names_iff' {p : Baire} {x : Set.Icc (0 : ℝ) 1} :
    unitIntervalRep.Names p x ↔
      ∀ n : ℕ, dist (realPresentation.dense (p n)) x.val ≤ ((2 : ℝ)⁻¹) ^ n :=
  Iff.trans Representation.subtype_names_iff realPresentation.cauchyRep_names_iff

/-- Applying `clampCode` to every output coordinate is a total computed stream operator. -/
private theorem exists_clampStreamCode :
    ∃ c : OracleCode, c.Computes fun p n => clampCode (p n) := by
  obtain ⟨G, hG⟩ := OracleCode.exists_ofNatFnCode primrec_clampCode.to_comp
  exact ⟨OracleCode.comp G OracleCode.query,
    fun p n => (OracleCode.eval_comp_some (OracleCode.eval_query p n)).trans (hG p (p n))⟩

/-- **The two representations of `[0, 1]` agree.** The Cauchy representation induced by
`unitIntervalPresentation` is computably equivalent to `unitIntervalRep`, so point names
transfer between them. Both directions are the same coordinatewise `clampCode` realizer, at
the same rate: clamping only moves a point closer to a target already in `[0, 1]`, so no
precision shift is needed in either direction. -/
theorem unitIntervalPresentation_cauchyRep_equiv :
    unitIntervalPresentation.cauchyRep ≡c unitIntervalRep := by
  constructor
  · obtain ⟨c, hc⟩ := exists_clampStreamCode
    refine ⟨c, Realizes.of_computes hc fun p x hpx => ?_⟩
    refine unitIntervalRep_names_iff'.mpr fun n => ?_
    rw [realPresentation_dense_clampCode, ← Subtype.dist_eq]
    exact unitIntervalPresentation_names_iff.mp hpx n
  · refine ⟨.query, fun p x hpx => ⟨p, by simp, ?_⟩⟩
    refine unitIntervalPresentation_names_iff.mpr fun n => ?_
    have hn := unitIntervalRep_names_iff'.mp hpx n
    rw [Real.dist_eq] at hn
    exact dist_unitClamp_le.trans hn

end ComputableAnalysis
