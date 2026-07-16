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

## Current prerequisite spine

In progress next, each independently reusable:

- **Represented reals**: computable metric presentations, the fast Cauchy
  representation, represented reals with a `[0,1]` arithmetic contract.
- **Cantor-space computable measures**: cylinder masses, measure representation and
  uniqueness/existence, measure constructors, pushforward.
- **General measure and kernel interfaces** on represented spaces, with
  integration/moments.
- **Weihrauch principles** (LPO, LLPO, lim) as the reducibility layer needs them.

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
