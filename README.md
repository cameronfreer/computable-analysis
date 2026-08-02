# Computable Analysis

A Lean 4 formalization of Type-2 (TTE) computable analysis, bridging mathlib's
discrete computability stack and its classical Polish/Borel/measure stack.

## What is here

**Type-2 core.** A universal finite oracle-code model on Baire space (`ℕ → ℕ`),
with universal evaluation, oracle substitution, and the use-principle/continuity
layer.

**Represented spaces.** Representations, computable points and maps,
constructions (products, subtypes, sequences), function spaces via
advice-realizable maps, and admissibility in both directions (continuous ⇔
advice-realizable between Cauchy-represented spaces).

**Weihrauch reducibility.** Partial multivalued problems; ordinary (`≤W`) and
strong (`≤sW`) reduction, each with an equivalent fixed-witness transformer
characterization and an executable calculus of reduction pairs (identity,
composition, congruence, product); countable parallelization as a closure
operator, with parallel products and cylinders.

**Weihrauch principles.** The benchmark degrees `LPO`, `LLPO`, `Lim`, finite
binary choice `C₂`, weak Kőnig's lemma `WKL`, closed choice on Cantor space
`C_Cantor`, explicit finite inverse-limit compactness `EFILC`, and countable
`Hall`. Each is presented as a problem over an explicit coding, with its
promises inside `accepts` and a theorem identifying its domain semantically.
Their calibrations against one another are certified by explicit code pairs.

**Metric layer.** Computable metric presentations, fast-Cauchy representations,
represented reals with arithmetic, and a computable presentation of the unit
interval.

**Measures.** Computable probability measures on Cantor space via cylinder
values; generic weak (Lévy–Prokhorov) representations on computable metric
spaces and their equivalence with the cylinder representation on Cantor space;
continuous Markov kernels; bounded-Lipschitz integration as a computable map;
the moment-sequence representation on the unit interval and a computable
Hausdorff moment theorem.

**Conditioning (target application).** The Weihrauch calibration of
disintegration, after Ackerman–Freer–Roy
([arXiv:1509.02992](https://arxiv.org/abs/1509.02992)).

**`ForMathlib/`.** Mathlib-shaped modules staged for upstreaming: `Primrec`
arithmetic and container combinators, `REPred` closure lemmas, and staged
approximations of r.e. predicates.

## How to read a module

Conventions hold throughout, so a reader who learns them once can read any
module — including ones written after this file.

**Promises live in `accepts`, never in names.** Every stream is a valid name of
*some* object; being a genuine tree, system, or family is a promise carried by
the problem, not a condition on names. Each problem therefore comes with an
`accepts_iff` unfolding lemma and a `dom_iff` theorem identifying its domain in
semantic terms — the latter is usually where the mathematical content sits.

**Reductions are certified by named code pairs.** A reduction is proved as an
explicit `IsReductionPair`/`IsStrongReductionPair` over codes extracted once and
specified, not constructed inline; the `≤W`/`≤sW` statement is a corollary.
Where several reductions share a shape, a uniform *compiler* discharges the
representation bookkeeping once and takes only the semantic data.

**Claims are exactly as strong as stated.** Reductions are proved from the
presented promises alone, independently of any ω-model or provability-level
relationship between the corresponding statements. An upper bound is never
evidence for a lower bound, and an ordinary reduction is never evidence that no
strong one exists.

**Nothing is admitted.** The build gate fails on any `sorry`-like token or
`axiom` declaration, and the axiom audit sweeps every declaration owned by a
`ComputableAnalysis` module — private and compiler-generated included —
asserting dependence only on `propext`, `Classical.choice`, and `Quot.sound`.

## Plan and status

`ROADMAP.md` is the public plan, organized by reusable capability.
`BLUEPRINT.md` is the implementation contract: pinned conventions, signatures,
and the acceptance checklist. Current work and open questions are tracked in the
issues; deliberately, neither this file nor the roadmap duplicates that status.

- Toolchain: `leanprover/lean4:v4.32.0`
- Mathlib pinned to `81a5d257c8e410db227a6665ed08f64fea08e997` (the `v4.32.0` tag)

## Building

```
lake exe cache get
bash scripts/check.sh
```

`scripts/check.sh` runs `lake build` and the gates described above. A headline
regression list in `scripts/AxiomAudit.lean` additionally guards named results
against deletion and renaming.
