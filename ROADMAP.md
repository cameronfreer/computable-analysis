# Roadmap

This library develops a reusable, mathlib-style effective layer for computable analysis
in Lean 4. Milestones are organized by **reusable capability**: each layer is a
deliverable on its own terms, consumed by — but not defined by — the applications it
enables. `BLUEPRINT.md` is the implementation contract (unit-by-unit signatures, pinned
conventions, status); this file is the public plan.

## Current: the semantic Type-2 / represented-space / Weihrauch core

Complete (units 0–11): oracle codes and their evaluator; fuel-bounded executable
simulation; the universal machine and s-m-n; the fixed-oracle `RecursiveIn` bridge to
mathlib; finite use and continuity of Type-2 computable operators; effective compactness
of Cantor space; representations and computable points; realizers and computable maps
with products, sums, and subtypes; representation equivalence; problems (partial,
multivalued); and ordinary and strong Weihrauch reducibility, with the fixed-witness
transformer characterization and the formal `≤W`/`≤sW` separation.

## Completed prerequisite spine

Complete, each independently reusable:

- **Represented reals**: computable metric presentations, the fast Cauchy
  representation, represented reals with a `[0,1]` arithmetic contract including
  uniform variable-length folds.
- **Cantor-space computable measures**: cylinder masses, measure representation with
  uniqueness/existence, the uniform cylinder-value characterization, constructors
  (Dirac, Bernoulli, finite mixtures, products), and pushforward along computable maps.
- **Weihrauch principles**: LPO, LLPO, and lim, with `LLPO ≤W LPO`, the
  noncomputability of LPO, and `LPO ≤W Lim`.

## Next phase: measure/kernel interfaces

The general interfaces on computable metric spaces — the probability-measure
representation, represented continuous maps, continuous kernels, and bounded-continuous
integration — beginning with focused feasibility reviews before any signature freeze.

## Target application: computability of conditioning

The application this substrate is built to support is the computability theory of
conditional probability (Ackerman–Freer–Roy): the non-computability of conditional
distributions in general, the positive computability results under additional
hypotheses, and the Weihrauch calibration of disintegration against `lim`. It consumes
every layer above — represented spaces, computable maps, Weihrauch reductions,
represented reals and `[0,1]` arithmetic, computable probability measures,
integration/moments, and the measure/kernel interfaces — and will receive its own
signature and feasibility review once those APIs stabilize.

## Scope

The layers above, each built as independently reusable theory, plus the conditioning
application, are the whole of this repository's plan. Other applications of the
substrate are out of scope here and are not part of this roadmap.
