/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.VitaliLimit
import ComputableAnalysis.Measure.DisintegrateUpper
import ComputableAnalysis.Measure.WeakLimit

/-!
# The Vitali-limit conditional reduces strongly to `Lim`

The upper bound of Ackerman–Freer–Roy's Prop. 5.6, in partial form: for a computable joint law
with a computable Vitali witness, `VitaliDisintegrate P Q μ V ≤sW Lim`. The problem is partial,
so no totality hypothesis is needed. The Vitali covering property is not used.

Assumptions: metric, measurable and Borel structure on both factors, the two computable
presentations, a computable joint law, and a computable witness. No completeness or standard
Borel assumption is made.

## Main results

* `exists_condSeqCompiler` — one fixed code sending a name of any accepted point to packed weak
  names of a sequence of conditionals converging to its accepted measure.
* `vitaliDisintegrate_le_lim` — the headline.

## Implementation notes

The compiler runs `exists_conditionalOnContOpenCode` on every track. Track `t` of its input
interleaves a fixed computable name of the joint law with track `t` of the witness stream. The
witness code and that name are fixed before the input quantifiers. The outer admissible
sequence appears only in the correctness proof, where null enlargement identifies the computed
conditionals with the admissible ones. The reduction is then the compiler followed by
`limTable`, with `exists_weakLimitDecoder` as the answer-only postprocessor.
-/

open MeasureTheory Filter Topology

namespace ComputableAnalysis

section Compiler

open OracleCode

variable {X Y : Type} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable {P : ComputableMetricPresentation X} {Q : ComputableMetricPresentation Y}

/-- The per-track conditioning input: track `t` is `interleave pμ (track t s)`. -/
private def condInput (pμ s : Baire) : Baire := fun m =>
  Baire.interleave pμ (Baire.track m.unpair.1 s) m.unpair.2

private theorem track_condInput (pμ s : Baire) (t : ℕ) :
    Baire.track t (condInput pμ s) = Baire.interleave pμ (Baire.track t s) := by
  funext k
  simp [condInput, Baire.track, Nat.unpair_pair]

/-- One code builds `condInput pμ s` from `s`, for a fixed computable `pμ`. -/
private theorem exists_condInputCode {pμ : Baire} (hpμ : Computable pμ) :
    ∃ T : OracleCode, ∀ s : Baire, condInput pμ s ∈ T.evalStream s := by
  have hk : Primrec fun y : ℕ => y.unpair.1.unpair.2 := primrec_unpairSnd.comp primrec_unpairFst
  have hv : Primrec fun y : ℕ => y.unpair.2 := primrec_unpairSnd
  have hpost : Computable fun y : ℕ =>
      (1 - y.unpair.1.unpair.2 % 2) * pμ (y.unpair.1.unpair.2 / 2)
        + (y.unpair.1.unpair.2 % 2) * y.unpair.2 :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp
        (Primrec.nat_sub.comp (Primrec.const 1)
          (Primrec.nat_mod.comp hk (Primrec.const 2))).to_comp
        (hpμ.comp (Primrec.nat_div.comp hk (Primrec.const 2)).to_comp))
      (Primrec.nat_mul.comp (Primrec.nat_mod.comp hk (Primrec.const 2)) hv).to_comp
  have hpos : Primrec fun m : ℕ => Nat.pair m.unpair.1 (m.unpair.2 / 2) :=
    Primrec₂.natPair.comp primrec_unpairFst
      (Primrec.nat_div.comp primrec_unpairSnd (Primrec.const 2))
  obtain ⟨G, hG⟩ := exists_ofNatFnCode hpost
  obtain ⟨C, hC⟩ := exists_ofNatFnCode hpos.to_comp
  refine ⟨comp G (pair OracleCode.id (comp query C)), fun s => mem_evalStream.mpr fun m => ?_⟩
  rw [eval_comp_some (eval_pair_some (eval_id _ _) ((eval_comp_some (hC _ _)).trans
    (eval_query _ _))), hG]
  refine Part.mem_some_iff.mpr ?_
  simp only [condInput, Baire.interleave, Baire.track, Nat.unpair_pair]
  rcases Nat.mod_two_eq_zero_or_one m.unpair.2 with h | h <;> simp [h]

/-- **The conditional-sequence compiler.** For a fixed computable joint law with a computable
Vitali witness, one fixed code sends a name of any accepted point to packed weak names of a
sequence of conditionals converging to its accepted measure. The witness code and the joint
name are extracted before the input quantifiers; the outer sequence `E` appears only in the
correctness argument. -/
theorem exists_condSeqCompiler {μ : ProbabilityMeasure (X × Y)}
    (hμ : (jointMeasureSpace P Q).rep.ComputablePoint μ) {V : Set (Set X)}
    (hV : ∃ W, IsVitaliWitness P (fstMarginal μ) V W) :
    ∃ S : OracleCode, ∀ (p : Baire) (x : X) (ν : ProbabilityMeasure Y),
      P.cauchyRep.Names p x → IsVitaliLimit μ V x ν →
      ∃ w ∈ S.evalStream p, ∃ σ : ℕ → ProbabilityMeasure Y,
        (∀ n, WeakMeasureNames Q (Baire.track n w) (σ n)) ∧ Tendsto σ atTop (𝓝 ν) := by
  classical
  have : BorelSpace (X × Y) := P.borelSpace_prod
  obtain ⟨W, hW⟩ := hV
  obtain ⟨pμ, hpμc, hpμn⟩ := hμ
  have hpμ : WeakMeasureNames (P.prod Q) pμ μ := (weakMeasureRep_names_iff (P.prod Q)).mp hpμn
  obtain ⟨C, hC⟩ := exists_conditionalOnContOpenCode P Q
  obtain ⟨T, hT⟩ := exists_condInputCode hpμc
  refine ⟨(mapTracks C).subst (T.subst W), fun p x ν hp hν => ?_⟩
  obtain ⟨s, hs, E, hE, hsE⟩ := hW p x hp hν.exists_admissible
  have hpos : ∀ n, (fstMarginal μ).toMeasure (openOf P (Baire.track n s).evenPart) ≠ 0 :=
    fun n => (hsE n).2.2 ▸ (hE.1 n).2.2
  have hcond := fun n => hC pμ (Baire.track n s) μ hpμ (hsE n).1 (hpos n)
  choose q hq ν' hν' hnames using hcond
  have hTs : condInput pμ s ∈ (T.subst W).evalStream p := by
    rw [evalStream_subst hs]; exact hT s
  refine ⟨Baire.packTracks q, ?_, fun n => sndMarginal (ν' n), fun n => ?_, ?_⟩
  · rw [evalStream_subst hTs]
    refine evalStream_mapTracks_iff.mpr fun t => ?_
    rw [Baire.track_packTracks, track_condInput]
    exact hq t
  · rw [Baire.track_packTracks]
    exact (weakMeasureRep_names_iff Q).mp (hnames n)
  · obtain ⟨σ', hσ', hlim⟩ := hν.tendsto E hE
    have hsame : (fun n => sndMarginal (ν' n)) = σ' := by
      funext n
      refine Subtype.ext ?_
      change (sndMarginal (ν' n)).toMeasure = (σ' n).toMeasure
      rw [hσ' n, sndMarginal_toMeasure, Measure.snd, hν' n,
        ← condSnd_eq_of_subset_of_measure_eq (measurableSet_openOf P _) (hsE n).2.1
          (hsE n).2.2 (hE.1 n).2.1]
      rfl
    rw [hsame]
    exact hlim

/-- **The upper bound** (the paper's Prop. 5.6, in partial form). The Vitali-limit conditional
of a computable joint law with a computable Vitali witness reduces strongly to `Lim`: no
totality, no covering property. -/
theorem vitaliDisintegrate_le_lim {μ : ProbabilityMeasure (X × Y)}
    (hμ : (jointMeasureSpace P Q).rep.ComputablePoint μ) {V : Set (Set X)}
    (hV : ∃ W, IsVitaliWitness P (fstMarginal μ) V W) :
    VitaliDisintegrate P Q μ V ≤sW Lim := by
  obtain ⟨S, hS⟩ := exists_condSeqCompiler hμ hV
  obtain ⟨L, hL⟩ := exists_limTableCode
  obtain ⟨H, hH⟩ := exists_weakLimitDecoder Q
  refine stabilizationTable_le_lim (K := L.subst S) (H := H) fun p x hp hdom => ?_
  obtain ⟨ν, hν⟩ := hdom
  obtain ⟨w, hw, σ, hσ, hlim⟩ := hS p x ν hp hν
  refine ⟨limTable w, by rw [evalStream_subst hw]; exact hL w, limTable_dom w,
    fun a hacc => ?_⟩
  obtain ⟨r, hr, hrn⟩ := hH w a σ ν hσ hlim hacc
  exact ⟨r, hr, ν, (weakMeasureRep_names_iff Q).mpr hrn, hν⟩

end Compiler

end ComputableAnalysis
