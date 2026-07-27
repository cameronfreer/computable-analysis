/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Measure.BernsteinIntegrand
import ComputableAnalysis.Measure.HausdorffMomentRealizer
import ComputableAnalysis.Measure.HausdorffMoments

/-!
# The computable Hausdorff moment theorem on the unit interval

The classical moment foundations live in `ComputableAnalysis.Measure.HausdorffMoments`: the
moment sequence `moment η n = ∫ p^n dη`, its complete monotonicity
(`isCompletelyMonotone_moment`), moment determinacy (`eq_of_forall_moment_eq`,
`moment_injective`) and the moment-sequence representation `hausdorffMomentRep` with its
name characterisation.

This module holds the **effective** content, and only the headline results:

* `computableMap_momentsOfMeasure` — from a weak name of `η`, compute all its moments, by
  integrating the bounded-Lipschitz monomials of
  `ComputableAnalysis.Measure.BernsteinIntegrand` uniformly in the exponent;
* `computableMap_measureOfMoments` — from names of all the moments, compute a weak name of
  `η`, through the effective Bernstein-polynomial reconstruction of
  `ComputableAnalysis.Measure.HausdorffMomentRealizer`;
* `hausdorffMomentRep_equiv_weak` — the resulting computable equivalence between
  `hausdorffMomentRep` and `weakMeasureRep unitIntervalPresentation`.

## Not here: classical Hausdorff existence

The converse classical theorem — that every normalized completely monotone sequence *is*
the moment sequence of some measure — is deliberately absent, and no statement of it is
introduced anywhere in this layer. Nothing here needs it: `hausdorffMomentRep`'s carrier is
*measures*, so its surjectivity only ever requires names for measures that already exist.
Which abstract sequences are realizable is a genuinely separate theorem, and a theorem is
recorded when it is proved, not before.
-/

namespace ComputableAnalysis

open MeasureTheory

/-- **Computable Hausdorff moment theorem, forward direction**: from a weak name of `η`,
compute all moments — integration of the bounded-Lipschitz monomials `p ↦ p^n`,
uniformly in `n`. -/
theorem computableMap_momentsOfMeasure :
    ComputableMap (weakMeasureRep unitIntervalPresentation) hausdorffMomentRep id := by
  classical
  -- The family-integration realizer, over the unit-interval presentation.
  obtain ⟨c, -, hc⟩ :=
    exists_boundedLipschitzFamilyIntegration_realizer unitIntervalPresentation
  -- The integrand stream is a *fixed* computable stream, so plain substitution suffices.
  obtain ⟨cI, hcI⟩ : Type2Computable fun M : Baire ↦ Baire.interleave M monomialStreamFn :=
    Type2Computable.interleave type2Computable_id
      (type2Computable_const_stream primrec_monomialStreamFn.to_comp)
  refine ⟨c.subst cI, fun P η hη ↦ ?_⟩
  -- The `i`-th slice of `monomialStreamFn` names the monomial `p ↦ p ^ i`.
  have hname : ∀ i : ℕ, IntegrandName unitIntervalPresentation
      (fun j ↦ monomialStreamFn (Nat.pair i j)) i 1 (monomialBL i).toFun := fun i ↦ by
    rw [monomialStreamFn_slice]
    exact integrandName_monomialName i
  obtain ⟨q, hq, hqn⟩ := hc P monomialStreamFn η (fun i ↦ (monomialBL i).toFun) (fun i ↦ i)
    (fun _ ↦ 1) ((weakMeasureRep_names_iff _).mp hη) hname
  have hsub : (c.subst cI).evalStream P
      = c.evalStream (Baire.interleave P monomialStreamFn) :=
    OracleCode.evalStream_subst
      (Part.eq_some_iff.mp (OracleCode.computes_iff_evalStream.mp hcI P))
  refine ⟨q, hsub ▸ hq, hausdorffMomentRep_names_iff.mpr fun n ↦ ?_⟩
  -- The `n`-th integral is definitionally the `n`-th moment, so the layout already matches.
  have hval : ∫ x, (monomialBL n).toFun x ∂η.toMeasure = moment η n := by
    rw [moment]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ monomialBL_apply n x)
  refine Representation.subtype_names_iff.mpr ?_
  change realRep.Names _ (moment η n)
  rw [← hval]
  exact hqn n

/-- **Computable Hausdorff moment theorem, reverse direction**: from names of all
moments, compute a weak name of the measure, through effective Bernstein-polynomial
approximation. -/
theorem computableMap_measureOfMoments :
    ComputableMap hausdorffMomentRep (weakMeasureRep unitIntervalPresentation) id := by
  -- The realizer: read a prefix of the moment name, then do rational arithmetic on it.
  obtain ⟨c, hc⟩ := OracleCode.exists_prefixPostCode
    (b := fun n _ ↦ momentBound n) (g := momentPost)
    (primrec_momentBound.comp Primrec.fst) primrec_momentPost
  refine ⟨c, Realizes.of_computes hc fun F η hF ↦ ?_⟩
  refine (weakMeasureRep_names_iff _).mpr fun n ↦ ?_
  -- The postprocessor decodes the prefix it was handed.
  have hdec : momentPost (Nat.pair n (Encodable.encode (streamTake F (momentBound n))))
      = Encodable.encode (momentAtomList n (streamTake F (momentBound n))) := by
    rw [momentPost, Nat.unpair_pair, Denumerable.ofNat_encode]
  rw [hdec]
  exact levyProkhorovDist_atomic_momentAtomList_le (hausdorffMomentRep_names_iff.mp hF) n

/-- **The computable Hausdorff moment theorem**: the moment-sequence representation and the
weak representation of probability measures on `[0, 1]` are computably equivalent.

Both halves are proved, so this is a theorem outright: it depends only on `propext`,
`Classical.choice` and `Quot.sound`. Note that a packaging term like this one stays
complete even when the halves it packages are not, which is why the project gate is a
transitive axiom audit rather than a source scan. -/
theorem hausdorffMomentRep_equiv_weak :
    hausdorffMomentRep ≡c weakMeasureRep unitIntervalPresentation :=
  ⟨computableMap_measureOfMoments, computableMap_momentsOfMeasure⟩

end ComputableAnalysis
