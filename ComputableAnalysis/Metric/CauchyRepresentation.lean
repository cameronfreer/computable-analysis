/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.RepresentedSpace.Constructions
import ComputableAnalysis.Metric.Presentation

/-!
# The fast Cauchy representation

Convention 8's three notions over a presentation `P`, at the pinned rate `((2:ℝ)⁻¹)^n`:

* `P.NamesPoint p x` — *semantic*: the dense points indexed by `p` approximate the
  specified limit `x` at the pinned rate.
* `P.IsFastCauchy p` — *syntactic*: successive dense points are `((2:ℝ)⁻¹)^(n+1)`-close;
  no limit is mentioned.
* `P.cauchyRep` — the representation: `p` is valid **exactly when some named limit
  exists** (unique in a `MetricSpace`). No totalization: on an incomplete space a fast
  Cauchy stream with no limit is not a valid name, so ℚ is a legitimate incomplete
  example.

Name decoding happens in a `MetricSpace` context (limits unique); the presentation
structure itself lives over `PseudoMetricSpace`, reached through the instance path. In a
`CompleteSpace`, every syntactically fast Cauchy name is valid, with the *same* rate:
the geometric tail `∑_{k ≥ n} ((2:ℝ)⁻¹)^(k+1) = ((2:ℝ)⁻¹)^n`. There is no converse from
`NamesPoint` to `IsFastCauchy` at the pinned rates (the triangle inequality gives only
`3·((2:ℝ)⁻¹)^(n+1)` between successive approximants).
-/

namespace ComputableAnalysis

universe u

namespace ComputableMetricPresentation

variable {X : Type u} [MetricSpace X] (P : ComputableMetricPresentation X)

/-- `p` names `x`: the indexed dense points approximate `x` at the pinned rate. -/
def NamesPoint (p : Baire) (x : X) : Prop :=
  ∀ n, dist (P.dense (p n)) x ≤ ((2 : ℝ)⁻¹) ^ n

/-- Syntactic fast Cauchy: successive indexed dense points are `((2:ℝ)⁻¹)^(n+1)`-close.
No limit is mentioned. -/
def IsFastCauchy (p : Baire) : Prop :=
  ∀ n, dist (P.dense (p n)) (P.dense (p (n + 1))) ≤ ((2 : ℝ)⁻¹) ^ (n + 1)

variable {P}

/-- A name determines its point: two named limits of one stream coincide. -/
theorem namesPoint_unique {p : Baire} {x y : X} (hx : P.NamesPoint p x)
    (hy : P.NamesPoint p y) : x = y := by
  refine eq_of_dist_eq_zero (le_antisymm ?_ dist_nonneg)
  have hbound : ∀ n : ℕ, dist x y ≤ 2 * ((2 : ℝ)⁻¹) ^ n := fun n =>
    calc dist x y ≤ dist x (P.dense (p n)) + dist (P.dense (p n)) y :=
          dist_triangle x (P.dense (p n)) y
      _ ≤ ((2 : ℝ)⁻¹) ^ n + ((2 : ℝ)⁻¹) ^ n := by
          rw [dist_comm x (P.dense (p n))]
          exact add_le_add (hx n) (hy n)
      _ = 2 * ((2 : ℝ)⁻¹) ^ n := by ring
  have hlim : Filter.Tendsto (fun n : ℕ => 2 * ((2 : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num :
      ((2 : ℝ)⁻¹) < 1)).const_mul 2
  exact ge_of_tendsto' hlim hbound

variable (P)

/-- The fast Cauchy representation: `p` is valid exactly when some named limit exists —
no totalization on incomplete spaces. -/
noncomputable def cauchyRep : Representation X where
  rep p := ⟨∃ x, P.NamesPoint p x, fun h => h.choose⟩
  onto x := by
    classical
    have h : ∀ n : ℕ, ∃ i, dist (P.dense i) x ≤ ((2 : ℝ)⁻¹) ^ n := fun n => by
      obtain ⟨i, hi⟩ := P.denseRange.exists_dist_lt x (by positivity : (0:ℝ) < ((2:ℝ)⁻¹) ^ n)
      exact ⟨i, by rw [dist_comm]; exact hi.le⟩
    have hname : P.NamesPoint (fun n => (h n).choose) x := fun n => (h n).choose_spec
    exact ⟨fun n => (h n).choose, ⟨x, hname⟩,
      namesPoint_unique (⟨x, hname⟩ : ∃ y, P.NamesPoint _ y).choose_spec hname⟩

/-- Names of `cauchyRep` are exactly `NamesPoint`. -/
@[simp]
theorem cauchyRep_names_iff {p : Baire} {x : X} :
    P.cauchyRep.Names p x ↔ P.NamesPoint p x := by
  constructor
  · rintro ⟨hex, rfl⟩
    exact hex.choose_spec
  · intro hx
    exact ⟨⟨x, hx⟩, namesPoint_unique (⟨x, hx⟩ : ∃ y, P.NamesPoint p y).choose_spec hx⟩

variable {P}

/-- **Completeness.** In a complete space, every syntactically fast Cauchy stream names
some point — with the same pinned rate, by the geometric tail sum. -/
theorem IsFastCauchy.exists_namesPoint [CompleteSpace X] {p : Baire}
    (h : P.IsFastCauchy p) : ∃ x, P.NamesPoint p x := by
  have hu : ∀ m, dist (P.dense (p m)) (P.dense (p (m + 1))) ≤ (2 : ℝ)⁻¹ * ((2:ℝ)⁻¹) ^ m :=
    fun m => by simpa [pow_succ, mul_comm] using h m
  have hcau : CauchySeq fun n => P.dense (p n) :=
    cauchySeq_of_le_geometric ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) (by norm_num) hu
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨x, fun n => ?_⟩
  have hd := dist_le_of_le_geometric_of_tendsto (r := (2 : ℝ)⁻¹) (C := (2 : ℝ)⁻¹)
    (by norm_num) hu hx n
  calc dist (P.dense (p n)) x ≤ (2 : ℝ)⁻¹ * ((2 : ℝ)⁻¹) ^ n / (1 - (2 : ℝ)⁻¹) := hd
    _ = ((2 : ℝ)⁻¹) ^ n := by norm_num

/-- In a complete space, every syntactically fast Cauchy stream is a valid name. -/
theorem IsFastCauchy.valid [CompleteSpace X] {p : Baire} (h : P.IsFastCauchy p) :
    P.cauchyRep.Valid p := by
  obtain ⟨x, hx⟩ := h.exists_namesPoint
  exact Representation.valid_iff_exists_names.mpr ⟨x, (P.cauchyRep_names_iff).mpr hx⟩

end ComputableMetricPresentation

end ComputableAnalysis
