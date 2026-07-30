# Computable Analysis

A Lean 4 formalization of Type-2 (TTE) computable analysis, bridging mathlib's
discrete computability stack and its classical Polish/Borel/measure stack.

## What is here

**Type-2 core.** A universal finite oracle-code model on Baire space (`ℕ → ℕ`),
with universal evaluation, oracle substitution, and the use-principle/continuity
layer.

**Represented spaces.** Representations, computable points and maps,
constructions (products, subtypes), function spaces via advice-realizable maps,
and admissibility in both directions (continuous ⇔ advice-realizable between
Cauchy-represented spaces).

**Weihrauch reducibility.** Partial multivalued problems; ordinary (`≤W`) and
strong (`≤sW`) reduction, each with an equivalent fixed-witness transformer
characterization and bundled reduction witnesses; the benchmark principles
`LPO`, `LLPO`, and `Lim`, with the classical separations between them.

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
([arXiv:1509.02992](https://arxiv.org/abs/1509.02992)): the Cantor-specific
lower bound `Lim ≤sW Disintegrate` is complete; the generic upper bound
`Disintegrate ≤sW Lim` is in progress (#10).

**`ForMathlib/`.** Mathlib-shaped modules staged for upstreaming (#21):
`Primrec` arithmetic and container combinators, `REPred` closure lemmas, and
staged approximations of r.e. predicates.

## Current direction

The next structural layer is the **Weihrauch degree spine** (#35): countable
parallelization as a closure operator, parallel products and cylinders, and the
standard calibrations `parallelize LPO ≡sW Lim` and
`parallelize LLPO ≡sW WKL`, with uniform Σ₁-family compilers as the intended
entry points for later upper bounds.

`BLUEPRINT.md` is the self-contained specification: pinned conventions, the
unit sequence with status, and the acceptance checklist. `ROADMAP.md` is the
public plan.

- Toolchain: `leanprover/lean4:v4.32.0`
- Mathlib pinned to `81a5d257c8e410db227a6665ed08f64fea08e997` (the `v4.32.0` tag)

## Building

```
lake exe cache get
bash scripts/check.sh
```

`scripts/check.sh` runs `lake build`, fails on any `sorry`-like token or `axiom`
declaration in the sources, and runs the axiom audit (`scripts/AxiomAudit.lean`),
which sweeps every declaration owned by a `ComputableAnalysis` module — including
private and compiler-generated ones — asserting dependence only on `propext`,
`Classical.choice`, and `Quot.sound`; a headline regression list additionally
guards against deletions and renames.
