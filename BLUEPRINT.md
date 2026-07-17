# Blueprint: computable analysis on Cantor and Polish spaces

This document is the **self-contained specification** for the project: every
implementation-critical convention, the unit sequence with status, the acceptance
checklist, and the standing risks. External design notes exist as local provenance
only; nothing here depends on them.

## What this project is

Mathlib has a discrete computability stack (`Partrec`, `Nat.Partrec.Code`, `REPred`,
`Nat.RecursiveIn`, `TuringDegree`) and a classical analysis stack (`PiNat` sequence
spaces, Polish and standard Borel spaces, probability measures, kernels). It has no
bridge: no Type-2 (TTE) machine model, no represented spaces, no Weihrauch
reducibility, no computable measures. This project builds that bridge, validated
Cantor-first.

**Scope (first spine deliverable).** (1) Baire/Cantor prefixes and cylinders, (2) a
universal finite oracle code, (3) represented spaces and computable maps, (4)
ordinary and strong Weihrauch reduction, (5) LPO/LLPO/lim, (6) computable metric
presentations with a fast Cauchy representation, (7) computable Cantor probability
measures via cylinder values.

**Deferred (post-deliverable re-plan).** Continuous reductions, degree quotients,
closed choice, effective open/closed sets, effective Borel codes, general Polish
measures, kernels, disintegration and conditioning (the target application — see
ROADMAP.md).

The bar for "done": a researcher can state and prove computability or
Weihrauch-degree results about maps, sets, and measures on Cantor space or
computable metric spaces without choosing a fresh coding convention, rebuilding a
Type-2 machine model, or confusing classical existence with computability.

## Pinned conventions

Changing any of these later invalidates a large fraction of the API. They are fixed
now, before theorem development.

1. **Root namespace `ComputableAnalysis`** (bare `Representation` collides with
   mathlib's representation theory). `abbrev Baire := ℕ → ℕ`,
   `abbrev Cantor := ℕ → Bool` inside it; the `PiNat`/product topology is reused,
   never duplicated; finite words are `List ℕ` / `List Bool`.
2. **The Type-2 primitive is coordinatewise**:
   ```lean
   def OracleCode.eval (c : OracleCode) (p : Baire) : ℕ →. ℕ
   ```
   Derived notions, in order:
   ```lean
   def OracleCode.Computes (c : OracleCode) (F : Baire → Baire) : Prop :=
     ∀ p n, c.eval p n = Part.some (F p n)                      -- total stream ops
   def OracleCode.evalStream (c : OracleCode) (p : Baire) : Part Baire :=
     ⟨∀ n, (c.eval p n).Dom, fun h n => (c.eval p n).get (h n)⟩ -- partial stream ops
   def Type2Computable (F : Baire → Baire) : Prop := ∃ c, c.Computes F
   ```
   `Baire →. Baire` is never the unexplained primary object; realization of
   represented maps/problems is defined via `evalStream` on valid names only.
3. **Uniformity**: always `∃ code, ∀ p, …`; never `∀ p, ∃ code, …`. A statement of
   the form `∀ p, Nat.RecursiveIn {p} (F p)` does **not** establish Type-2
   computability of `F`; the finite code witness stays outside `∀ p`. Never apply
   first-order `Computable` to `Baire → Baire` (Baire is not `Primcodable`).
4. **Representations are partial surjections** (`rep : Baire →. α` + `onto`), built
   as **explicit objects, not typeclass instances**. Invalid names stay invalid: no
   default-point totalization. Pinned Cantor representation:
   ```lean
   def cantorRep : Representation Cantor where
     rep p := Part.assert (∀ n, p n ≤ 1) fun _ => Part.some fun n => p n == 1
   ```
   Valid names take values in `{0,1}` (`0 ↦ false`, `1 ↦ true`); a name with any
   coordinate `≥ 2` has **no** denotation.
5. **Problems are relation-valued** (`accepts : X → Y → Prop`), partial, multivalued;
   `Dom` is derived from `accepts`, so domain conditions live inside `accepts` (or in
   an input subtype) — never in a separate unenforced side condition.
6. **Ordinary vs strong Weihrauch reduction are separate definitions**, each in a
   realizer-quantified form and a transformer form, with equivalence proved. Name
   pairing is `Baire.interleave` (`(interleave p q) (2*n) = p n`,
   `(interleave p q) (2*n+1) = q n`). Pinned transformer shapes, for
   `G : Baire →. Baire` an arbitrary realizer of `g`:
   ```lean
   -- ordinary: postprocessor sees the original input and the oracle answer
   fun p => do
     let k ← K.evalStream p
     let a ← G k
     H.evalStream (Baire.interleave p a)
   -- strong: postprocessor sees only the oracle answer
   fun p => do
     let k ← K.evalStream p
     let a ← G k
     H.evalStream a
   ```
   `f ≤W g` (resp. `f ≤sW g`) iff there exist codes `K H` such that for **every**
   realizer `G` of `g` the displayed operator realizes `f`.
7. **Metric computability is presentation-relative**: explicit
   `ComputableMetricPresentation` bundles (dense sequence + `REPred` semidecisions
   of both strict rational distance comparisons); no typeclass in this deliverable.
   `MetricSpace` (not `Pseudo`) wherever name-decoding must be functional.
8. **Fast Cauchy names, pinned rate `((2 : ℝ)⁻¹) ^ n`.** Two distinct predicates:
   ```lean
   -- semantic: p names x (functional on MetricSpace; cauchyRep's graph)
   def NamesPoint (p : Baire) (x : α) : Prop :=
     ∀ n, dist (X.dense (p n)) x ≤ ((2 : ℝ)⁻¹) ^ n
   -- syntactic: no limit mentioned
   def IsFastCauchy (p : Baire) : Prop :=
     ∀ n, dist (X.dense (p n)) (X.dense (p (n + 1))) ≤ ((2 : ℝ)⁻¹) ^ (n + 1)
   ```
   `cauchyRep` is **partial on arbitrary `MetricSpace`**: `p` is valid iff some `x`
   with `NamesPoint p x` exists (unique by `MetricSpace`); surjectivity follows from
   density alone, so ℚ is a legitimate incomplete example. The completeness theorem
   is stated with the syntactic predicate: in a `CompleteSpace`, every `IsFastCauchy`
   name is valid (tail sum `∑ k ≥ n, ((2:ℝ)⁻¹)^(k+1) = ((2:ℝ)⁻¹)^n`).
9. **Computable measures are computable points of a represented measure space**;
   Cantor-first via cylinder masses valued through `measureReal` (mathlib measures
   return `ℝ≥0∞`, never raw `Real`). Computable measures are not identified with
   computable densities or samplers.
10. **Code equality is syntactic** (`DecidableEq OracleCode`); extensional equality
    is only ever stated through `eval` lemmas, never as a quotient.
11. **PiNat metric handling**: mathlib deliberately does not make
    `PiNat.metricSpaceNatNat` (and relatives) global. The project mirrors this with
    `scoped instance` declarations in the namespace
    `ComputableAnalysis.PiNatInstances`; every public declaration mentioning `dist`
    on Baire/Cantor lives under `open scoped ComputableAnalysis.PiNatInstances`, and
    downstream units use the metric only through the presentation objects.

## Module layout

The target tree, populated unit by unit; directories appear when their first unit lands.

```
ComputableAnalysis.lean                  -- umbrella import, extended each unit
ComputableAnalysis/
  TypeTwo/      Baire.lean Cantor.lean OracleCode.lean Eval.lean Evaln.lean
                Universal.lean Continuity.lean PrefixTable.lean StreamExamples.lean
  RepresentedSpace/ Basic.lean Realizer.lean ComputableMap.lean
                Constructions.lean Equivalence.lean
  Weihrauch/    Problem.lean Reduction.lean StrongReduction.lean
                Principles/LPO.lean Principles/LLPO.lean Principles/Limit.lean
  Metric/       Presentation.lean CauchyRepresentation.lean Real.lean Examples.lean
  Measure/      CylinderMass.lean Construction.lean CantorRepresentation.lean
                CylinderValues.lean Constructors.lean Pushforward.lean
scripts/AxiomAudit.lean                  -- axiom-whitelist gate
```

Core stream constructions live in the core modules, not the examples module:
`encodeCantor`, `natStreamToBool` (the neutral zero/positive decoder), and `truncate` in
`Cantor.lean`; `Baire.interleave`/`evenPart`/`oddPart` and `streamTake_succ` in `Baire.lean`;
the output-pairing closure (`Type2Computable.interleave`, `OracleCode.exists_pairStreams`,
the Skolemized `OracleCode.pairCode` + `pairCode_spec`) and the production closure lemmas
(`type2Computable_const_stream`/`query_comp`/`evenPart`/`oddPart`) in `Continuity.lean`.
`StreamExamples.lean` holds only worked instances (id, const, shift, `truncate`) and the
discontinuity separator; `PrefixTable.lean` imports core modules only.

## Unit sequence and status

One commit per unit; `bash scripts/check.sh && git commit && git push`. Review
stops are external reviews.

| Unit | Content | Status |
| ---- | ------- | ------ |
| 0 | BLUEPRINT, README, axiom-audit gate | done |
| 1 | Baire/Cantor utilities (first-order only) | done |
| 2 | OracleCode syntax + evaluator (`Primcodable`, `rfind'`) | done |
| — | **Review Stop A**: oracle conventions | approved 2026-07-12 |
| 3 | Bounded simulation `evalnPrefix` (executable, `Option`-valued) | done |
| 4 | Universal evaluator, s-m-n, fixed-oracle `RecursiveIn` | done |
| 5 | Finite use, continuity, stream layer + examples | done |
| 6 | Effective compactness: `uniformPrefixTableSearch` | done |
| — | API-hardening pass: partial-realizer interface, module moves, decoder, namespaces | done |
| — | **Review Stop B**: representation/reduction signatures | approved 2026-07-13 |
| 7 | Representations + computable points | done |
| 8 | Realizers + computable maps | done |
| 9 | Representation equivalence | done |
| 10 | Problems + ordinary Weihrauch reduction | done |
| 11 | Strong reduction + formal ≤W/≤sW separation | done |
| — | **Review Stop C**: semantic API as implemented | approved 2026-07-14 |
| 12 | LPO, LLPO (+ multivalued-oracle test) | — |
| 13 | lim | — |
| 14 | Computable metric presentations | done |
| 15 | Fast Cauchy representation | done |
| 16 | Represented reals + arithmetic contract | done |
| 17 | Metric examples + rate equivalence | deferred — not required for Review Stop D |
| 18 | Cantor measurable structure, cylinder masses, uniqueness | done |
| — | **Feasibility review**: measure-existence route | approved 2026-07-16 |
| 19 | Existence: measure from consistent masses | done |
| 20 | Cantor measure representation | done |
| 21 | Uniform cylinder-value equivalence | — |
| 22 | Measure constructors | — |
| 23 | Pushforward | — |
| — | **Review Stop D**: deliverable complete; re-plan | — |

## Signatures appendix (grows before each review stop)

### For Review Stop A — units 2–6 operational layer

```lean
-- Unit 2: syntax. Atoms zero/succ/left/right/query; composites pair/comp/prec/rfind'.
inductive OracleCode
  | zero | succ | left | right | query
  | pair (f g : OracleCode) | comp (f g : OracleCode)
  | prec (f g : OracleCode) | rfind' (f : OracleCode)

def OracleCode.eval (c : OracleCode) (p : Baire) : ℕ →. ℕ
-- query: (query).eval p n = Part.some (p n)
-- rfind': mathlib's starting-point convention, mirroring Nat.Partrec.Code.rfind'
instance : Denumerable OracleCode   -- bijective encodeCode/ofNatCode round trip
-- Primcodable OracleCode is derived from this instance via the priority-10
-- mathlib instance Primcodable.ofDenumerable (Denumerable does imply
-- Primcodable: encode ∘ decode is succ, which is primitive recursive) —
-- the same way Nat.Partrec.Code obtains its Primcodable instance.

-- Unit 3: executable bounded simulation; queries answered from a finite prefix.
def OracleCode.evalnPrefix (fuel : ℕ) (c : OracleCode)
    (oraclePrefix : List ℕ) (input : ℕ) : Option ℕ
def OracleCode.evaln (k : ℕ) (c : OracleCode) (p : Baire) (n : ℕ) : Option ℕ
  -- := evalnPrefix k c (streamTake p k) n
-- Computable on the packed product ((ℕ × OracleCode) × List ℕ × ℕ);
-- monotone in fuel and under compatible prefix extension;
-- sound (evaln ⊆ eval) and convergent (eval = ⋃ k, evaln k).

-- Unit 4:
theorem exists_universal :
    ∃ u : OracleCode, ∀ c p n, u.eval p (Nat.pair (encode c) n) = c.eval p n
theorem smn : ∃ s : ℕ → ℕ → ℕ, Computable₂ s ∧
    ∀ c m p n, (ofNat OracleCode (s (encode c) m)).eval p n
      = c.eval p (Nat.pair m n)
-- (`eval_comp` is the pointwise evaluator equation from unit 2; the unit 4 form
-- is the explicit-witness equality, not an existential)
theorem eval_comp_eq (f g : OracleCode) (p : Baire) :
    (comp f g).eval p = f.eval p <=< g.eval p
theorem exists_code_iff_recursiveIn (p : Baire) (f : ℕ →. ℕ) :
    (∃ c : OracleCode, c.eval p = f) ↔ Nat.RecursiveIn {(p : ℕ →. ℕ)} f

-- Unit 5:
theorem eval_eq_of_agree_on_use (h : y ∈ c.eval p n) :
    ∃ u : Finset ℕ, ∀ q, (∀ i ∈ u, q i = p i) → y ∈ c.eval q n
theorem type2Computable_continuous (h : Type2Computable F) : Continuous F

-- Unit 5 (API-hardening pass — partial-realizer interface, before Review Stop B).
-- The pointwise laws are the primitives; the globally total forms are corollaries.
theorem OracleCode.mem_evalStream : q ∈ c.evalStream p ↔ ∀ n, q n ∈ c.eval p n
theorem OracleCode.eval_subst_of_eval (h : cg.eval p = fun n => Part.some (q n)) (cf) :
    (cf.subst cg).eval p = cf.eval q             -- eval_subst and Type2Computable.comp corollaries
theorem OracleCode.evalStream_subst (hq : q ∈ cg.evalStream p) :
    (cf.subst cg).evalStream p = cf.evalStream q  -- valid-name composition for represented maps
theorem OracleCode.exists_pairStreams :           -- reusable code-level output pairing
    ∃ pairCode, ∀ cf cg p q r, q ∈ cf.evalStream p → r ∈ cg.evalStream p →
      Baire.interleave q r ∈ (pairCode cf cg).evalStream p
theorem type2Computable_const_stream (hs : Computable s) : Type2Computable (fun _ => s)

-- Unit 6: canonical partial search; List not Finset (no Primcodable (Finset α)
-- at the pinned rev). Result (m, T): T.Nodup, all lengths = m, cylinders pairwise
-- disjoint, union = preimage of the target cylinder.
def uniformPrefixTableSearch :
    OracleCode → List Bool →. ℕ × List (List Bool)
theorem uniformPrefixTableSearch_partrec : Partrec₂ uniformPrefixTableSearch
theorem uniformPrefixTableSearch_dom (hc : TotalOnCantor c) (s : List Bool) :
    (uniformPrefixTableSearch c s).Dom
```

### For Review Stop B — units 7–11 representation/reduction layer

Signatures only; no implementation until this stop is approved. Drafted against the
API-hardening foundation (`6a52e45`): realization goes through `OracleCode.evalStream` on
valid names, composition through `evalStream_subst`, products through `exists_pairStreams`.
Bare `Representation` carries units 7–9 (comparing representations of one fixed carrier);
`RepSpace` bundles carrier + representation for units 10–11, where the endpoints vary.

```lean
universe u v w

-- Unit 7 (RepresentedSpace/Basic.lean): representations + computable points.
-- Representations are partial surjections built as explicit objects (convention 4).
structure Representation (α : Type u) where
  rep  : Baire →. α
  onto : ∀ a, ∃ p, a ∈ rep p

namespace Representation
def Names (X : Representation α) (p : Baire) (a : α) : Prop := a ∈ X.rep p
def Valid (X : Representation α) (p : Baire) : Prop := (X.rep p).Dom
theorem valid_iff_exists_names : X.Valid p ↔ ∃ a, X.Names p a
-- `Part α` is single-valued: a valid name denotes AT MOST one point. Multivaluedness
-- begins at `Problem.accepts` (unit 10), never at `Representation`.
theorem names_unique (ha : X.Names p a) (hb : X.Names p b) : a = b   -- Part.mem_unique
-- `Computable p` treats p : ℕ → ℕ first-order (only the ℕ input/output are Primcodable);
-- Baire itself is NOT Primcodable (convention 3). An oracle-code formulation can be proved
-- equivalent later but is not the definition.
def ComputablePoint (X : Representation α) (a : α) : Prop :=
  ∃ p : Baire, Computable p ∧ X.Names p a
end Representation

-- Bundled carrier + chosen representation, for units 10–11 where the ENDPOINTS VARY
-- (Problem, reducibility). Units 8–9 stay on bare `Representation` — the right object for
-- comparing two representations of one FIXED carrier. Distinct representations of a carrier
-- remain distinct RepSpace values (needed by unit 9).
structure RepSpace where
  carrier : Type u
  rep     : Representation carrier
instance : CoeSort (RepSpace.{u}) (Type u) := ⟨RepSpace.carrier⟩

-- Explicit objects (no typeclass instances, no default-point totalization):
def baireRep  : Representation Baire                        -- rep p := Part.some p
def cantorRep : Representation Cantor where                  -- convention 4, verbatim
  rep p := Part.assert (∀ n, p n ≤ 1) fun _ => Part.some fun n => p n == 1
def natRep    : Representation ℕ                            -- rep p := Part.some (p 0)
def discreteRep [Encodable α] : Representation α where       -- partial decoder; no [Inhabited]
  rep p := Part.ofOption (Encodable.decode (p 0))
example : ¬ cantorRep.Valid (fun _ => 2)                     -- invalid name denotes nothing
def baireSpace  : RepSpace := ⟨Baire, baireRep⟩             -- named bundles for problems
def cantorSpace : RepSpace := ⟨Cantor, cantorRep⟩
def natSpace    : RepSpace := ⟨ℕ, natRep⟩

-- Unit 8 (RepresentedSpace/Realizer.lean, ComputableMap.lean, Constructions.lean):
-- realizers + computable maps on BARE representations. Realization is through evalStream
-- on valid names only (conv. 2).
def Realizes (X : Representation α) (Y : Representation β) (c : OracleCode) (f : α → β) : Prop :=
  ∀ p a, X.Names p a → ∃ q ∈ c.evalStream p, Y.Names q (f a)
def ComputableMap (X : Representation α) (Y : Representation β) (f : α → β) : Prop :=
  ∃ c : OracleCode, Realizes X Y c f
-- Foundation bridge (proved in the Type-2 layer, consumed here): a total stream value of a
-- code on a COMPUTABLE input is itself computable — needed to preserve computable points,
-- which partial substitution alone does not give.
theorem OracleCode.computable_of_mem_evalStream
    (hp : Computable p) (hq : q ∈ c.evalStream p) : Computable q
theorem ComputableMap.id : ComputableMap X X id
theorem ComputableMap.comp (hg : ComputableMap Y Z g) (hf : ComputableMap X Y f) :
    ComputableMap X Z (g ∘ f)                               -- via OracleCode.evalStream_subst
theorem ComputableMap.computablePoint (hf : ComputableMap X Y f) (ha : X.ComputablePoint a) :
    Y.ComputablePoint (f a)                                 -- via computable_of_mem_evalStream
-- Products, sums, subtypes with their (co)projections/injections as computable maps:
def Representation.prod    (X : Representation α) (Y : Representation β) : Representation (α × β)
def Representation.sum     (X : Representation α) (Y : Representation β) : Representation (α ⊕ β)
def Representation.subtype (X : Representation α) (P : α → Prop) : Representation {a // P a}
theorem ComputableMap.pair (hf : ComputableMap X Y f) (hg : ComputableMap X Z g) :
    ComputableMap X (Y.prod Z) (fun a => (f a, g a))        -- via OracleCode.exists_pairStreams
theorem computableMap_fst : ComputableMap (X.prod Y) X Prod.fst
theorem computableMap_snd : ComputableMap (X.prod Y) Y Prod.snd
theorem computableMap_inl : ComputableMap X (X.sum Y) Sum.inl
theorem computableMap_inr : ComputableMap Y (X.sum Y) Sum.inr
theorem computableMap_subtypeVal : ComputableMap (X.subtype P) X Subtype.val
theorem computableMap_encodeCantor : ComputableMap cantorRep baireRep encodeCantor
-- Names characterizations (as implemented; the Unit 8 API surface consumed by unit 9).
-- One simp lemma per representation/construction, plus the Computes→Realizes bridge:
--   baireRep_names_iff, cantorRep_names_iff, natRep_names_iff, discreteRep_names_iff,
--   prod_names_iff, sum_names_inl_iff, sum_names_inr_iff, subtype_names_iff  (all @[simp])
--   Realizes.of_computes : c.Computes F → (∀ p a, X.Names p a → Y.Names (F p) (f a)) →
--     Realizes X Y c f

-- Unit 9 (RepresentedSpace/Equivalence.lean): representation equivalence + invariance.
def Representation.Equiv (X X' : Representation α) : Prop :=
  ComputableMap X X' id ∧ ComputableMap X' X id
infix:50 " ≡c " => Representation.Equiv
theorem Representation.Equiv.refl  : X ≡c X
theorem Representation.Equiv.symm  : X ≡c X' → X' ≡c X
theorem Representation.Equiv.trans : X ≡c X' → X' ≡c X'' → X ≡c X''
theorem Representation.Equiv.computableMap_congr (hX : X ≡c X') (hY : Y ≡c Y') :
    ComputableMap X Y f ↔ ComputableMap X' Y' f
theorem Representation.Equiv.computablePoint_congr (hX : X ≡c X') :
    X.ComputablePoint a ↔ X'.ComputablePoint a
-- Worked equivalence: the redundant Cantor representation (accepts any name, decoding
-- 0/positive) is ≡c cantorRep, with `truncate` realizing one direction and `id` the other.
def cantorRepRedundant : Representation Cantor
theorem cantorRep_equiv_redundant : cantorRep ≡c cantorRepRedundant
-- As implemented: also cantorRepRedundant_names_iff (@[simp], the Names characterization).

-- Unit 10 (Weihrauch/Problem.lean, Reduction.lean): problems + ordinary reduction.
-- Problems are relation-valued, partial, multivalued (convention 5); Dom is derived.
structure Problem (X : RepSpace.{u}) (Y : RepSpace.{v}) where
  accepts : X → Y → Prop
def Problem.Dom (f : Problem X Y) (x : X) : Prop := ∃ y, f.accepts x y
-- A realizer sends each valid name of an in-domain input to a name of an accepted output.
def Problem.Realizes (f : Problem X Y) (G : Baire →. Baire) : Prop :=
  ∀ p x, X.rep.Names p x → f.Dom x → ∃ q ∈ G p, ∃ y, Y.rep.Names q y ∧ f.accepts x y
-- Every problem has a realizer (classical choice of an accepted answer name per valid input).
theorem Problem.exists_realizer (f : Problem X Y) : ∃ G, f.Realizes G
-- Patched realizer: fix any permitted answer name at a valid oracle input into a full
-- realizer of the problem (classical). The ingredient for the reverse of
-- reduction_iff_exists_reductionPair.
theorem Problem.exists_realizer_patch (hp : X.rep.Names p x) (hy : f.accepts x y)
    (hq : Y.rep.Names q y) : ∃ G : Baire →. Baire, f.Realizes G ∧ q ∈ G p
-- Ordinary reduction, realizer-quantified (convention 6): THERE EXIST FIXED codes K H such
-- that FOR EVERY realizer G of g the transformer realizes f (NOT ∀ G, ∃ K H). Postprocessor H
-- sees the ORIGINAL input via Baire.interleave — the original-input distinction, structural.
def WeihrauchReducible (f : Problem X Y) (g : Problem X' Y') : Prop :=
  ∃ K H : OracleCode, ∀ G, g.Realizes G →
    f.Realizes fun p => do let k ← K.evalStream p; let a ← G k; H.evalStream (Baire.interleave p a)
infix:50 " ≤W " => WeihrauchReducible
-- Transformer form: a FIXED-WITNESS local condition on (K, H) with NO quantification over G.
def IsReductionPair (f : Problem X Y) (g : Problem X' Y') (K H : OracleCode) : Prop :=
  ∀ p x, X.rep.Names p x → f.Dom x →
    ∃ k ∈ K.evalStream p, ∃ x', X'.rep.Names k x' ∧ g.Dom x' ∧
      ∀ a y', Y'.rep.Names a y' → g.accepts x' y' →
        ∃ q ∈ H.evalStream (Baire.interleave p a), ∃ y, Y.rep.Names q y ∧ f.accepts x y
theorem reduction_iff_exists_reductionPair : f ≤W g ↔ ∃ K H, IsReductionPair f g K H
theorem WeihrauchReducible.refl  : f ≤W f
theorem WeihrauchReducible.trans : f ≤W g → g ≤W h → f ≤W h
def idProblem           (X : RepSpace) : Problem X X      -- accepts x y := y = x
def zeroProblem         : Problem baireSpace natSpace := ⟨fun _ _ => False⟩  -- empty domain (calibration)
def constNatZeroProblem : Problem baireSpace natSpace      -- accepts _ n := n = 0 (total)
def constZeroProblem    : Problem baireSpace baireSpace    -- accepts _ q := q = fun _ => 0 (separation)
-- Computability of a (partial, multivalued) problem: a single code realizes it — NOT a total
-- extensional selection F : X → Y, which is strictly stronger and would break the equivalence.
def ComputableProblem (f : Problem X Y) : Prop := ∃ c : OracleCode, f.Realizes c.evalStream
theorem computableProblem_iff_le_idProblem :               -- computable ⇔ below identity
    ComputableProblem f ↔ f ≤W idProblem X
def Problem.Equivalent (f f' : Problem X Y) : Prop := ∀ x y, f.accepts x y ↔ f'.accepts x y
theorem WeihrauchReducible.congr (hf : f.Equivalent f') (hg : g.Equivalent g') :
    (f ≤W g) ↔ (f' ≤W g')

-- Unit 11 (Weihrauch/StrongReduction.lean): strong reduction + ≤W/≤sW separation.
-- Strong: postprocessor sees ONLY the oracle answer (no Baire.interleave with the input).
def StrongWeihrauchReducible (f : Problem X Y) (g : Problem X' Y') : Prop :=
  ∃ K H : OracleCode, ∀ G, g.Realizes G →
    f.Realizes fun p => do let k ← K.evalStream p; let a ← G k; H.evalStream a
infix:50 " ≤sW " => StrongWeihrauchReducible
def IsStrongReductionPair (f : Problem X Y) (g : Problem X' Y') (K H : OracleCode) : Prop :=
  ∀ p x, X.rep.Names p x → f.Dom x →                       -- as IsReductionPair, but H sees a only
    ∃ k ∈ K.evalStream p, ∃ x', X'.rep.Names k x' ∧ g.Dom x' ∧
      ∀ a y', Y'.rep.Names a y' → g.accepts x' y' →
        ∃ q ∈ H.evalStream a, ∃ y, Y.rep.Names q y ∧ f.accepts x y
theorem strongReduction_iff_exists_reductionPair :
    f ≤sW g ↔ ∃ K H, IsStrongReductionPair f g K H
theorem strongWeihrauch_le_weihrauch : f ≤sW g → f ≤W g
theorem StrongWeihrauchReducible.refl  : f ≤sW f
theorem StrongWeihrauchReducible.trans : f ≤sW g → g ≤sW h → f ≤sW h
-- HEADLINE separation (both over baireSpace): identity reduces ordinarily to the constant
-- zero problem — ordinary H recovers the input as `Baire.evenPart` of the interleaved name —
-- but NOT strongly, since strong H sees only the unique zero answer and cannot distinguish
-- two input streams.
theorem idProblem_le_constZero      : idProblem baireSpace ≤W constZeroProblem
theorem idProblem_not_sle_constZero : ¬ idProblem baireSpace ≤sW constZeroProblem
theorem exists_reduction_not_strong :                       -- immediate corollary, not headline
    ∃ (X Y X' Y' : RepSpace) (f : Problem X Y) (g : Problem X' Y'), (f ≤W g) ∧ ¬ (f ≤sW g)
```

### For the measure-existence feasibility review — units 18–19 (Cantor measures)

Unit 18 signatures frozen at Review Stop C closure (2026-07-16). Unit 19 freezes **only**
the route-independent headline contract; the internal constructor is pinned at the
feasibility review itself. No new measurable/Borel instances anywhere: `Cantor = ℕ → Bool`
carries mathlib's Pi `MeasurableSpace` (discrete factors). Masses are plain reals here —
represented `[0,1]` values arrive with units 14–16 and enter at unit 20.

```lean
-- Unit 18 (Measure/CylinderMass.lean): Cantor measurable structure + cylinder masses.
def cantorCylinders : Set (Set Cantor) := Set.range (cylinder : List Bool → Set Cantor)
theorem measurableSet_cylinder (s : List Bool) : MeasurableSet (cylinder s : Set Cantor)
theorem isPiSystem_cantorCylinders : IsPiSystem cantorCylinders
theorem generateFrom_cantorCylinders :
    MeasurableSpace.generateFrom cantorCylinders = (inferInstance : MeasurableSpace Cantor)
def cylMass (μ : ProbabilityMeasure Cantor) (s : List Bool) : ℝ  -- (μ (cylinder s) : ℝ≥0)
theorem cylMass_nil : cylMass μ [] = 1                           -- normalization
theorem cylMass_nonneg : 0 ≤ cylMass μ s
theorem cylMass_le_one : cylMass μ s ≤ 1
theorem cylMass_split :                                          -- binary consistency
    cylMass μ s = cylMass μ (s ++ [false]) + cylMass μ (s ++ [true])
-- Abstract consistency (normalization, nonnegativity, binary splitting); boundedness
-- `m s ≤ 1` is derived, never assumed.
def IsConsistentCylinderMass (m : List Bool → ℝ) : Prop :=
  m [] = 1 ∧ (∀ s, 0 ≤ m s) ∧ ∀ s, m s = m (s ++ [false]) + m (s ++ [true])
theorem cylMass_isConsistent (μ) : IsConsistentCylinderMass (cylMass μ)
-- As implemented (unit 19 rider): route-independent consequences published here —
--   IsConsistentCylinderMass.append_le / .le_of_prefix / .le_one
-- Uniqueness: cylinder masses determine the measure (π-system uniqueness on the
-- generating cylinders).
theorem cylMass_injective : Function.Injective (cylMass)

-- Unit 19 (Measure/Construction.lean): existence. ONLY this headline is frozen.
-- PINNED route B (feasibility review, approved 2026-07-16): Ionescu–Tulcea via mathlib
-- `Kernel.trajMeasure` over history-dependent next-bit `bernoulliMeasure` kernels
-- (`PMF.bernoulli` is deprecated at this pin) with parameter
--   p s := if m s = 0 then 0 else m (s ++ [true]) / m s
-- (arbitrary default transition on zero-mass prefixes), prefix-mass equation by
-- induction. Implementation route: an explicit constant-Bool family abbreviation +
-- Cantor-specialized wrappers (the `Π i : Iic n, X i` implicits of
-- partialTraj/frestrictLe/IicProdIoc do not pattern-unify with `↥(Iic n) → Bool`), and
-- private `oneStep`/`comp_step` singleton-recursion lemmas for `partialTraj` (credible
-- mathlib-upstreaming candidates; kept private during unit 19). The content/Carathéodory
-- route is retained only as historical fallback.
theorem existsUnique_probabilityMeasure_of_isConsistent {m : List Bool → ℝ}
    (hm : IsConsistentCylinderMass m) :
    ∃! μ : ProbabilityMeasure Cantor, ∀ s, cylMass μ s = m s
```

### For units 14–16 — minimal represented reals (unit 17 deferred)

Instantiates pinned conventions 7–8 (presentation bundles, `NamesPoint`/`IsFastCauchy`
with rate `((2:ℝ)⁻¹)^n`, partial `cauchyRep`). The uniform-sum packing and realizer
were validated pre-freeze by the uniform-sums spike (zero sorries, standard axioms,
realizer total on all streams); the `[0,1]`-restricted uniform product by the
unit-products spike. All rational thresholds and names go through the coded rationals
`RatCode`/`ratOfCode` — never mathlib's `Encodable`/`Primcodable ℚ` numberings, which
are two *different* numberings with no `Primrec`/`Computable` arithmetic lemmas.

```lean
-- Unit 14 (Metric/Presentation.lean): coded rationals + computable metric presentations
-- (explicit data, never typeclasses — convention 7). Semidecisions only; a decision
-- oracle is too strong.
abbrev RatCode := ℕ
def ratOfCode (m : RatCode) : ℚ :=                             -- total, surjective,
  ((m.unpair.1.unpair.1 : ℚ) - m.unpair.1.unpair.2) / (m.unpair.2 + 1)  -- unnormalized
theorem ratOfCode_surjective : Function.Surjective ratOfCode
structure ComputableMetricPresentation (X : Type u) [PseudoMetricSpace X] where
  dense      : ℕ → X
  denseRange : DenseRange dense
  ltSemidec  : REPred fun w : ℕ × ℕ × RatCode =>
    dist (dense w.1) (dense w.2.1) < (ratOfCode w.2.2 : ℝ)
  gtSemidec  : REPred fun w : ℕ × ℕ × RatCode =>
    (ratOfCode w.2.2 : ℝ) < dist (dense w.1) (dense w.2.1)
-- Foundation riders (spike-mandated, this unit) — the private Universal.lean builders
-- become public with these exact statements, plus the total head-adaptive bridge and
-- the code-assembly simp kit:
theorem OracleCode.exists_snocCode : ∃ e : OracleCode, ∀ (P : Baire) (x : ℕ) (l : List ℕ),
    e.eval P (Nat.pair x (encode l)) = Part.some (encode (l ++ [x]))
theorem OracleCode.exists_takeCode : ∃ t : OracleCode, ∀ (P : Baire) (k : ℕ),
    t.eval P k = Part.some (encode (streamTake P k))
theorem OracleCode.exists_ofNatFnCode {f : ℕ → ℕ} (hf : Computable f) :
    ∃ e : OracleCode, ∀ (P : Baire) (n : ℕ), e.eval P n = Part.some (f n)
theorem OracleCode.exists_prefixPostCode {b : ℕ → ℕ → ℕ} {g : ℕ → ℕ} (hb : Primrec₂ b)
    (hg : Primrec g) : ∃ c : OracleCode, ∀ (F : Baire) (n : ℕ),
      c.eval F n = Part.some (g (Nat.pair n (encode (streamTake F (b n (F 0))))))
theorem OracleCode.eval_comp_some {cf cg : OracleCode} {p : Baire} {n a : ℕ}
    (h : cg.eval p n = Part.some a) : (comp cf cg).eval p n = cf.eval p a
theorem OracleCode.eval_pair_some {cf cg : OracleCode} {p : Baire} {n a b : ℕ}
    (hf : cf.eval p n = Part.some a) (hg : cg.eval p n = Part.some b) :
    (pair cf cg).eval p n = Part.some (Nat.pair a b)

-- Unit 15 (Metric/CauchyRepresentation.lean): the notions of convention 8, in context
--   variable {X : Type u} [MetricSpace X] (P : ComputableMetricPresentation X)
-- (the structure stays over PseudoMetricSpace; name DECODING happens only in the
-- MetricSpace context, via the instance path — no simultaneous unrelated instances).
def P.NamesPoint (p : Baire) (x : X) : Prop                    -- convention 8, verbatim
def P.IsFastCauchy (p : Baire) : Prop                          -- convention 8, verbatim
def P.cauchyRep : Representation X                             -- valid iff ∃ x named; no
                                                               -- totalization (ℚ stays
                                                               -- a legit incomplete ex.)
theorem P.cauchyRep_names_iff : P.cauchyRep.Names p x ↔ P.NamesPoint p x
theorem P.isFastCauchy_exists_namesPoint [CompleteSpace X] (h : P.IsFastCauchy p) :
    ∃ x, P.NamesPoint p x
theorem P.isFastCauchy_valid [CompleteSpace X] : P.IsFastCauchy p → P.cauchyRep.Valid p
-- (No converse from NamesPoint to IsFastCauchy: the triangle inequality gives only
-- 3·2⁻⁽ⁿ⁺¹⁾ between successive approximants, not the pinned 2⁻⁽ⁿ⁺¹⁾.)

-- Unit 16 (Metric/Real.lean): represented reals over the unit 14 coded rationals.
def rationalPresentation : ComputableMetricPresentation ℚ      -- dense := ratOfCode;
                                                               -- the worked incomplete ex.
def realPresentation : ComputableMetricPresentation ℝ          -- dense := (ratOfCode · : ℝ)
def realRep : Representation ℝ := realPresentation.cauchyRep
def unitIntervalRep : Representation (Set.Icc (0 : ℝ) 1) :=    -- the [0,1] values of
  realRep.subtype _                                            -- units 20–23
theorem computablePoint_realZero : realRep.ComputablePoint 0
theorem computablePoint_realOne  : realRep.ComputablePoint 1
-- Arithmetic contract (binary ops as ComputableMap on prod; dist for the later
-- metric-measure interfaces; the [0,1] complement for cylinder-mass algebra):
theorem computableMap_realAdd  : ComputableMap (realRep.prod realRep) realRep fun p => p.1 + p.2
theorem computableMap_realNeg  : ComputableMap realRep realRep Neg.neg
theorem computableMap_realMul  : ComputableMap (realRep.prod realRep) realRep fun p => p.1 * p.2
theorem computableMap_realDist : ComputableMap (realRep.prod realRep) realRep fun p => |p.1 - p.2|
def unitSymm : Set.Icc (0 : ℝ) 1 → Set.Icc (0 : ℝ) 1           -- x ↦ 1 - x
theorem computableMap_unitSymm : ComputableMap unitIntervalRep unitIntervalRep unitSymm
-- Uniform variable-length folds (the units 22–23 consumer). PINNED packing:
def Packs (F : Baire) (k : ℕ) (x : Fin k → ℝ) : Prop :=
  F 0 = k ∧ ∀ i : Fin k, realRep.Names (fun n => F (1 + Nat.pair i n)) (x i)
-- Sum (spike-validated): precision bump n + k via k < 2^k; ONE code, TOTAL on all
-- streams (totality is part of the public contract), through exists_prefixPostCode:
theorem exists_uniform_sum_realizer :
    ∃ c : OracleCode, (∀ (F : Baire) (n : ℕ), (c.eval F n).Dom) ∧
      ∀ (k : ℕ) (F : Baire) (x : Fin k → ℝ), Packs F k x →
        ∃ q ∈ c.evalStream F, realRep.Names q (∑ i, x i)
-- Product, RESTRICTED to [0,1] inputs (what Bernoulli cylinder masses and the measure
-- constructors need; clamp each approximant into [0,1], then |∏a−∏b| ≤ ∑|aᵢ−bᵢ| gives
-- the SAME bump n + k — no arbitrary-magnitude bounds). Unit-products spike-validated.
theorem exists_uniform_unitProd_realizer :
    ∃ c : OracleCode, (∀ (F : Baire) (n : ℕ), (c.eval F n).Dom) ∧
      ∀ (k : ℕ) (F : Baire) (x : Fin k → ℝ), Packs F k x → (∀ i, x i ∈ Set.Icc (0:ℝ) 1) →
        ∃ q ∈ c.evalStream F, realRep.Names q (∏ i, x i)
```

### For units 20–23 — the Cantor computable-measure representation (draft; freeze pending)

On top of units 18–19 (`cylMass`, `IsConsistentCylinderMass`, `cylMass_injective`,
`existsUnique_probabilityMeasure_of_isConsistent`) and unit 16 (`unitIntervalRep`, the
packed folds). Word indices use `Encodable.encode : List Bool → ℕ` (the `Primcodable`
numbering — safe here, unlike ℚ: it is one numbering with the full `Primrec` list
toolkit). Completing 20–23 closes the measure spine; Review Stop D / Milestone A closes
only once units 12–13 land as well.

```lean
-- Unit 20 (Measure/CantorRepresentation.lean): the measure representation.
-- PINNED packing: one Baire name F carries, for every word s, the unitIntervalRep name
-- of the mass of s as the component  fun n => F (Nat.pair (Encodable.encode s) n).
-- Invalid behavior: if ANY component fails to name the corresponding mass — invalid
-- [0,1]-name or masses of no single measure — F denotes NOTHING (no default measure).
def cylMass01 (μ : ProbabilityMeasure Cantor) (s : List Bool) : Set.Icc (0 : ℝ) 1 :=
  ⟨cylMass μ s, cylMass_nonneg μ s, cylMass_le_one μ s⟩
def MeasureNames (F : Baire) (μ : ProbabilityMeasure Cantor) : Prop :=
  ∀ s : List Bool,
    unitIntervalRep.Names (fun n => F (Nat.pair (Encodable.encode s) n)) (cylMass01 μ s)
def cantorMeasureRep : Representation (ProbabilityMeasure Cantor)
  -- rep F valid iff ∃ μ, MeasureNames F μ (unique: component names are single-valued,
  -- then cylMass_injective); onto via unitIntervalRep.onto per word (choice).
theorem cantorMeasureRep_names_iff : cantorMeasureRep.Names F μ ↔ MeasureNames F μ
def cantorMeasureSpace : RepSpace := ⟨ProbabilityMeasure Cantor, cantorMeasureRep⟩

-- Unit 21 (Measure/CylinderValues.lean): first-order uniform cylinder-mass equivalence.
-- A measure is a computable point iff ONE first-order procedure uniformly produces the
-- [0,1]-names of all its cylinder masses from the encoded word.
theorem computablePoint_cantorMeasureRep_iff {μ : ProbabilityMeasure Cantor} :
    cantorMeasureRep.ComputablePoint μ ↔
      ∃ f : ℕ → ℕ → ℕ, Computable₂ f ∧ ∀ s : List Bool,
        unitIntervalRep.Names (f (Encodable.encode s)) (cylMass01 μ s)

-- Unit 22 (Measure/Constructors.lean). All constructions produce ProbabilityMeasure
-- Cantor via unit 19's existence theorem from an explicitly consistent mass function;
-- each has a cylMass law and a computability theorem.
def diracMeasure (x : Cantor) : ProbabilityMeasure Cantor
theorem cylMass_diracMeasure :
    cylMass (diracMeasure x) s = if x ∈ (cylinder s : Set Cantor) then 1 else 0
theorem computablePoint_diracMeasure (hx : cantorRep.ComputablePoint x) :
    cantorMeasureRep.ComputablePoint (diracMeasure x)
-- Bernoulli = the i.i.d. PRODUCT measure on Cantor (not the one-bit bernoulliMeasure),
-- uniformly computable in the parameter (via the [0,1] uniform product fold + unitSymm):
def bernoulliProduct (p : Set.Icc (0 : ℝ) 1) : ProbabilityMeasure Cantor
theorem cylMass_bernoulliProduct :
    cylMass (bernoulliProduct p) s = ∏ i : Fin s.length, cond s[i] p.1 (1 - p.1)
theorem computableMap_bernoulliProduct :
    ComputableMap unitIntervalRep cantorMeasureRep bernoulliProduct
-- Finite mixtures. PINNED input encoding: F = Baire.interleave W M, where W packs the
-- k weights per unit 16's Packs layout (as [0,1] values) and M packs the k measure
-- names with component i at  fun n => M (1 + Nat.pair i n):
def PacksMeasures (M : Baire) (k : ℕ) (μs : Fin k → ProbabilityMeasure Cantor) : Prop :=
  M 0 = k ∧ ∀ i : Fin k, cantorMeasureRep.Names (fun n => M (1 + Nat.pair i n)) (μs i)
-- Normalization is a HYPOTHESIS (∑ w = 1), never re-derived or repaired:
def finiteMixture {k : ℕ} (w : Fin k → Set.Icc (0 : ℝ) 1) (hw : ∑ i, (w i).1 = 1)
    (μs : Fin k → ProbabilityMeasure Cantor) : ProbabilityMeasure Cantor
theorem cylMass_finiteMixture :
    cylMass (finiteMixture w hw μs) s = ∑ i, (w i).1 * cylMass (μs i) s
theorem exists_uniform_finiteMixture_realizer :
    ∃ c : OracleCode, ∀ (k : ℕ) (W M : Baire) (w : Fin k → Set.Icc (0:ℝ) 1)
      (hw : ∑ i, (w i).1 = 1) (μs : Fin k → ProbabilityMeasure Cantor),
      Packs W k (fun i => (w i).1) → PacksMeasures M k μs →
      ∃ q ∈ c.evalStream (Baire.interleave W M),
        cantorMeasureRep.Names q (finiteMixture w hw μs)
-- Binary product via the PINNED interleaving identification. Cantor-typed interleaving
-- is frozen here and defined in TypeTwo/Cantor.lean at implementation
-- (Baire.interleave is ℕ → ℕ-stream-typed and does not apply to Cantor):
def Cantor.interleave (x y : Cantor) : Cantor :=
  fun n => if n % 2 = 0 then x (n / 2) else y (n / 2)
@[simp] theorem Cantor.interleave_even : Cantor.interleave x y (2 * n) = x n
@[simp] theorem Cantor.interleave_odd  : Cantor.interleave x y (2 * n + 1) = y n
theorem Cantor.measurable_interleave :
    Measurable fun p : Cantor × Cantor => Cantor.interleave p.1 p.2
-- Deinterleaved subwords, with explicit bodies and coordinate/length characterizations:
def wordEven (s : List Bool) : List Bool :=
  List.ofFn fun i : Fin ((s.length + 1) / 2) => s[2 * i.1]'(by omega)
def wordOdd (s : List Bool) : List Bool :=
  List.ofFn fun i : Fin (s.length / 2) => s[2 * i.1 + 1]'(by omega)
@[simp] theorem length_wordEven : (wordEven s).length = (s.length + 1) / 2
@[simp] theorem length_wordOdd  : (wordOdd s).length = s.length / 2
theorem getElem_wordEven (h : i < (wordEven s).length) :
    (wordEven s)[i] = s[2 * i]'(by simp at h; omega)
theorem getElem_wordOdd (h : i < (wordOdd s).length) :
    (wordOdd s)[i] = s[2 * i + 1]'(by simp at h; omega)
-- The membership law tying interleaving to the subwords:
theorem Cantor.interleave_mem_cylinder_iff :
    Cantor.interleave x y ∈ (cylinder s : Set Cantor) ↔
      x ∈ (cylinder (wordEven s) : Set Cantor) ∧ y ∈ (cylinder (wordOdd s) : Set Cantor)
def productMeasure (μ ν : ProbabilityMeasure Cantor) : ProbabilityMeasure Cantor
-- Classical semantics: productMeasure IS the image of the mathlib product measure under
-- the interleaving identification (implementation may still construct it through unit
-- 19's existence theorem and prove this equality):
theorem productMeasure_eq_map_prod :
    (productMeasure μ ν).toMeasure =
      (μ.toMeasure.prod ν.toMeasure).map fun p => Cantor.interleave p.1 p.2
theorem cylMass_productMeasure :
    cylMass (productMeasure μ ν) s = cylMass μ (wordEven s) * cylMass ν (wordOdd s)
theorem computableMap_productMeasure :
    ComputableMap (cantorMeasureRep.prod cantorMeasureRep) cantorMeasureRep
      fun p => productMeasure p.1 p.2

-- Unit 23 (Measure/Pushforward.lean): pushforward along a computable map
-- f : Cantor → Cantor. `f` is a TOTAL mathematical function (total by its type), and
-- the hypothesis ComputableMap cantorRep cantorRep f means its realizer converges on
-- every VALID Cantor name — not necessarily on every Baire stream.
-- Measurability bridge: computable ⇒ continuous (finite use on names) ⇒ measurable.
theorem continuous_of_computableMap_cantor (hf : ComputableMap cantorRep cantorRep f) :
    Continuous f
theorem measurable_of_computableMap_cantor (hf : ComputableMap cantorRep cantorRep f) :
    Measurable f
def pushforwardMeasure (f : Cantor → Cantor) (hf : ComputableMap cantorRep cantorRep f)
    (μ : ProbabilityMeasure Cantor) : ProbabilityMeasure Cantor   -- μ.map f
-- Prefix-table mass formula (unit 6): the preimage of a cylinder is a FINITE disjoint
-- union of cylinders read off uniformPrefixTableSearch on a realizer of f, so the
-- pushforward mass is the finite sum of source masses:
theorem exists_pushforward_cylinder_table (hf : ComputableMap cantorRep cantorRep f)
    (s : List Bool) : ∃ T : Finset (List Bool),
      (f ⁻¹' (cylinder s : Set Cantor) = ⋃ t ∈ T, (cylinder t : Set Cantor)) ∧
      (T : Set (List Bool)).Pairwise (Disjoint on fun t => (cylinder t : Set Cantor)) ∧
      ∀ μ, cylMass (pushforwardMeasure f hf μ) s = ∑ t ∈ T, cylMass μ t
-- Computability, uniform in the measure for a fixed computable f:
theorem computableMap_pushforwardMeasure (hf : ComputableMap cantorRep cantorRep f) :
    ComputableMap cantorMeasureRep cantorMeasureRep (pushforwardMeasure f hf)
-- Composition law:
theorem pushforwardMeasure_comp (hf : ComputableMap cantorRep cantorRep f)
    (hg : ComputableMap cantorRep cantorRep g) :
    pushforwardMeasure g hg (pushforwardMeasure f hf μ) =
      pushforwardMeasure (g ∘ f) (hg.comp hf) μ
```

## Worked-example checklist (acceptance test; each in its owning unit)

- Type-2 core (units 5–6): identity; constants; composition; pairing/projections;
  stream shift; interleaving; `truncate` proved `Type2Computable`; `encodeCantor`
  coordinate equations (its `ComputableMap` form lands in unit 8); per-coordinate
  finite use; `uniformPrefixTableSearch` with its four result theorems (`Nodup`,
  uniform length, disjointness, preimage union); a total discontinuous map proved
  not Type-2 computable.
- Represented spaces (units 7–9): countable discrete; products and sums; two
  computably equivalent representations of one carrier; an invalid name with no
  denotation.
- Weihrauch (units 10–13): `LLPO ≤W LPO`; `¬ComputableProblem LPO`; `LPO ≤W Lim`;
  formal separation `idProblem ≤W constZeroProblem` with `¬ ≤sW`; multivalued-oracle
  test `llpo_swap_le_llpo` verified against every realizer on the all-zero input.
- Metric (units 14–16, minimal): ℚ; ℝ (the encoded rational dense sequence). Deferred
  with unit 17 (not required for Review Stop D): Cantor and Baire presentations; finite
  products; a closed subspace; equivalence of two Cauchy rates.
- Measures (units 18–23): Dirac; Bernoulli; finite mixture; product; pushforward.
- Deferred with their layers: closed choice examples, kernel examples.

## Workflow

- Commits authored as Cameron Freer <cameronfreer@gmail.com>; one commit per unit;
  no amends; this status table updated in the same commit.
- `bash scripts/check.sh && git commit` — never `;`-chained. (`lake env lean <file>`
  does not apply lakefile linter options; only `lake build` gates.)
- `scripts/check.sh` = `lake build` (strict linters, `warningAsError`) + zero
  `sorry`-like tokens + zero project `axiom` declarations +
  `lake env lean scripts/AxiomAudit.lean`. The audit sweeps every declaration
  owned by a `ComputableAnalysis` module — including private and generated
  declarations — for dependence only on `propext`, `Classical.choice`,
  `Quot.sound`; the headline list (extended each unit) also guards against
  deletions/renames.
- Push to origin after every commit (`git push`); snapshot bundles are retired.

## Standing risks

- **Quantifier order**: `∃ code, ∀ p` everywhere; a `∀ p, ∃ code` proof is not
  Type-2 computability.
- **No default-point totalization**: invalid names must remain invalid.
- **`Nat.RecursiveIn` is semantic**: use it only at a fixed oracle; the code witness
  stays first-class.
- **No `DecidablePred` from effective data**: semidecidability (`REPred`) is the
  effective datum for distance comparisons; Borel-type membership is not decidable.
- **PiNat metrics are non-global**: only via `ComputableAnalysis.PiNatInstances`.
- **`measureReal`/`ℝ≥0∞` discipline**: every measure-valued statement fixes which
  real type it means.
- **Classical existence ≠ computability**: mathlib's classical constructions
  (measures, limits) enter computability theorems only through explicit realizers.
