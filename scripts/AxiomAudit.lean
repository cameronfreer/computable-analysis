/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis

/-!
# Axiom audit

Checks that the library depends only on the standard axioms `propext`,
`Classical.choice`, and `Quot.sound`. Run via
`lake env lean scripts/AxiomAudit.lean` (done by `scripts/check.sh`); any
disallowed axiom is a hard error.

Two layers:

* **Environment sweep**: every declaration whose *owning module* is `ComputableAnalysis`
  or a submodule is checked — including `private` declarations (whose mangled
  `_private.*` names defeat any namespace-prefix filter) and compiler-generated
  auxiliaries — so a `native_decide`/`ofReduceBool` (or any custom axiom) anywhere in
  the library fails the gate, whether or not the declaration is listed below.
* **Headline regression list**: `headlineDecls` is extended in every unit; because the
  double-backtick names resolve at elaboration, a deletion or rename of a headline
  declaration also fails the gate. The list targets proof declarations and named
  instances, not `structure` types (auditing a structure declaration is vacuous).
-/

open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Headline declarations to audit; extended with each unit. -/
def headlineDecls : List Name :=
  [-- Unit 1: Baire/Cantor finite-observation layer
   ``ComputableAnalysis.isClopen_cylinder,
   ``ComputableAnalysis.cylinder_streamTake,
   ``ComputableAnalysis.primrec_isPrefix,
   ``ComputableAnalysis.primrec_boolWordToNat,
   ``ComputableAnalysis.primrec_natWordToBool,
   -- Unit 2: oracle-code syntax and evaluator
   ``ComputableAnalysis.OracleCode.instDenumerable,
   ``ComputableAnalysis.OracleCode.primrec₂_pair,
   ``ComputableAnalysis.OracleCode.primrec₂_comp,
   ``ComputableAnalysis.OracleCode.primrec₂_prec,
   ``ComputableAnalysis.OracleCode.primrec_rfind',
   ``ComputableAnalysis.OracleCode.primrec_const,
   ``ComputableAnalysis.OracleCode.primrec₂_curry,
   ``ComputableAnalysis.OracleCode.eval_query,
   ``ComputableAnalysis.OracleCode.eval_rfind,
   ``ComputableAnalysis.OracleCode.eval_ofPartrecCode,
   -- Unit 3: bounded simulation
   ``ComputableAnalysis.OracleCode.primrec_recOn,
   ``ComputableAnalysis.OracleCode.evalnPrefix_bound,
   ``ComputableAnalysis.OracleCode.evalnPrefix_mono,
   ``ComputableAnalysis.OracleCode.evalnPrefix_sound,
   ``ComputableAnalysis.OracleCode.evalnPrefix_complete,
   ``ComputableAnalysis.OracleCode.evaln_sound,
   ``ComputableAnalysis.OracleCode.evaln_complete,
   ``ComputableAnalysis.OracleCode.primrec_evalnPrefix,
   ``ComputableAnalysis.OracleCode.computable_evalnPrefix,
   -- Unit 4: universal evaluator, s-m-n, fixed-oracle RecursiveIn
   ``ComputableAnalysis.OracleCode.smn,
   ``ComputableAnalysis.OracleCode.eval_comp_eq,
   ``ComputableAnalysis.OracleCode.exists_code_iff_recursiveIn,
   ``ComputableAnalysis.OracleCode.exists_universal,
   -- Unit 5: finite use, continuity, stream layer
   ``ComputableAnalysis.OracleCode.eval_eq_of_agree_on_use,
   ``ComputableAnalysis.type2Computable_continuous,
   ``ComputableAnalysis.type2Computable_truncate,
   ``ComputableAnalysis.not_type2Computable_notAllZero,
   -- Unit 5 (stream closure API): composition, pairing, projections, stream-view link
   ``ComputableAnalysis.OracleCode.eval_subst,
   ``ComputableAnalysis.OracleCode.computes_iff_evalStream,
   ``ComputableAnalysis.Type2Computable.comp,
   ``ComputableAnalysis.Type2Computable.interleave,
   ``ComputableAnalysis.type2Computable_evenPart,
   ``ComputableAnalysis.type2Computable_oddPart,
   -- Unit 5 (API hardening): pointwise partial-realizer interface + reusable pairing
   ``ComputableAnalysis.OracleCode.mem_evalStream,
   ``ComputableAnalysis.OracleCode.eval_subst_of_eval,
   ``ComputableAnalysis.OracleCode.evalStream_subst,
   ``ComputableAnalysis.OracleCode.exists_pairStreams,
   ``ComputableAnalysis.OracleCode.pairCode_spec,
   ``ComputableAnalysis.type2Computable_const_stream,
   ``ComputableAnalysis.Baire.evenPart_interleave,
   ``ComputableAnalysis.Baire.oddPart_interleave,
   -- Unit 6: effective compactness (uniform prefix table)
   ``ComputableAnalysis.OracleCode.uniformPrefixTableSearch_partrec,
   ``ComputableAnalysis.OracleCode.uniformPrefixTableSearch_dom,
   ``ComputableAnalysis.OracleCode.uniformPrefixTableSearch_nodup,
   ``ComputableAnalysis.OracleCode.uniformPrefixTableSearch_length,
   ``ComputableAnalysis.OracleCode.uniformPrefixTableSearch_disjoint,
   ``ComputableAnalysis.OracleCode.uniformPrefixTableSearch_preimage,
   -- Unit 7: representations + computable points
   ``ComputableAnalysis.Representation.valid_iff_exists_names,
   ``ComputableAnalysis.Representation.names_unique,
   ``ComputableAnalysis.baireRep,
   ``ComputableAnalysis.cantorRep,
   ``ComputableAnalysis.natRep,
   ``ComputableAnalysis.discreteRep,
   -- Unit 8: realizers + computable maps
   ``ComputableAnalysis.OracleCode.computable_of_mem_evalStream,
   ``ComputableAnalysis.ComputableMap.id,
   ``ComputableAnalysis.ComputableMap.comp,
   ``ComputableAnalysis.ComputableMap.computablePoint,
   ``ComputableAnalysis.ComputableMap.pair,
   ``ComputableAnalysis.Representation.prod,
   ``ComputableAnalysis.Representation.sum,
   ``ComputableAnalysis.Representation.subtype,
   ``ComputableAnalysis.computableMap_fst,
   ``ComputableAnalysis.computableMap_snd,
   ``ComputableAnalysis.computableMap_inl,
   ``ComputableAnalysis.computableMap_inr,
   ``ComputableAnalysis.computableMap_subtypeVal,
   ``ComputableAnalysis.computableMap_encodeCantor,
   -- Unit 9: representation equivalence
   ``ComputableAnalysis.Representation.Equiv.refl,
   ``ComputableAnalysis.Representation.Equiv.symm,
   ``ComputableAnalysis.Representation.Equiv.trans,
   ``ComputableAnalysis.Representation.Equiv.computableMap_congr,
   ``ComputableAnalysis.Representation.Equiv.computablePoint_congr,
   ``ComputableAnalysis.cantorRepRedundant,
   ``ComputableAnalysis.cantorRep_equiv_redundant,
   -- Unit 10: problems + ordinary Weihrauch reduction
   ``ComputableAnalysis.Problem.exists_realizer,
   ``ComputableAnalysis.Problem.exists_realizer_patch,
   ``ComputableAnalysis.Problem.Equivalent.realizes_iff,
   ``ComputableAnalysis.reduction_iff_exists_reductionPair,
   ``ComputableAnalysis.WeihrauchReducible.refl,
   ``ComputableAnalysis.WeihrauchReducible.trans,
   ``ComputableAnalysis.WeihrauchReducible.congr,
   ``ComputableAnalysis.computableProblem_iff_le_idProblem,
   ``ComputableAnalysis.idProblem,
   ``ComputableAnalysis.zeroProblem,
   ``ComputableAnalysis.constNatZeroProblem,
   ``ComputableAnalysis.constZeroProblem,
   -- Unit 11: strong reduction + the ≤W/≤sW separation
   ``ComputableAnalysis.strongReduction_iff_exists_reductionPair,
   ``ComputableAnalysis.strongWeihrauch_le_weihrauch,
   ``ComputableAnalysis.StrongWeihrauchReducible.refl,
   ``ComputableAnalysis.StrongWeihrauchReducible.trans,
   ``ComputableAnalysis.StrongWeihrauchReducible.congr,
   ``ComputableAnalysis.idProblem_le_constZero,
   ``ComputableAnalysis.idProblem_not_sle_constZero,
   ``ComputableAnalysis.exists_reduction_not_strong,
   -- Unit 18: Cantor measurable structure + cylinder masses
   ``ComputableAnalysis.measurableSet_cylinder,
   ``ComputableAnalysis.isPiSystem_cantorCylinders,
   ``ComputableAnalysis.generateFrom_cantorCylinders,
   ``ComputableAnalysis.cylMass,
   ``ComputableAnalysis.cylMass_split,
   ``ComputableAnalysis.cylMass_isConsistent,
   ``ComputableAnalysis.cylMass_injective,
   -- Unit 19: existence from consistent masses (route B, Ionescu–Tulcea)
   ``ComputableAnalysis.existsUnique_probabilityMeasure_of_isConsistent,
   -- Unit 14: coded rationals + computable metric presentations + Type-2 riders
   ``ComputableAnalysis.OracleCode.exists_snocCode,
   ``ComputableAnalysis.OracleCode.exists_takeCode,
   ``ComputableAnalysis.OracleCode.exists_ofNatFnCode,
   ``ComputableAnalysis.OracleCode.exists_prefixPostCode,
   ``ComputableAnalysis.OracleCode.eval_comp_some,
   ``ComputableAnalysis.OracleCode.eval_pair_some,
   ``ComputableAnalysis.ratOfCode_surjective]

#eval show CoreM Unit from do
  for t in headlineDecls do
    let axs ← collectAxioms t
    for a in axs do
      unless allowedAxioms.contains a do
        throwError "axiom audit: {t} depends on disallowed axiom {a}"
  let env ← getEnv
  let moduleNames := env.allImportedModuleNames
  let mut swept := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if (`ComputableAnalysis).isPrefixOf moduleNames[idx.toNat]! then
        let axs ← collectAxioms name
        for a in axs do
          unless allowedAxioms.contains a do
            throwError "axiom audit (sweep): {name} depends on disallowed axiom {a}"
        swept := swept + 1
  IO.println
    s!"axiom audit: {headlineDecls.length} headline declaration(s) clean; swept {swept}"
