# Roadmap

Where the library is going, by theme. Individual task status lives in the
[issues](https://github.com/cameronfreer/computable-analysis/issues); this file
deliberately does not duplicate it, and is not a record of what is finished.

Each theme is developed as reusable theory first: a layer is a deliverable on its own
terms, consumed by — but not defined by — the applications it enables.

## Computability of conditioning

The application this substrate is built to support: the computability theory of
conditional probability, after Ackerman–Freer–Roy. Three strands — the
non-computability of conditional distributions in general, positive results under
additional hypotheses, and the Weihrauch calibration of disintegration against `lim`.
It consumes every layer below, which is why those layers are built generically rather
than to its specification.

## The Weihrauch degree spine

Countable parallelization, with extensivity, monotonicity, and idempotence, alongside
parallel products and cylinders, and a widening set of benchmark degrees calibrated
against one another by explicit code pairs. The direction of travel is compact choice:
the closed-choice principles and their relationships to weak Kőnig's lemma and to the
finite-choice hierarchy. Uniform
compilers for recurring reduction shapes are part of the deliverable, not a by-product
— they are the intended entry point for later upper bounds.

## Continuous reducibility and effective topology

Continuous (non-uniform) reducibility alongside the computable notions, degree
quotients, and effective open, closed, and Borel structure. This is the layer that
lets topological and computability-theoretic statements be separated cleanly rather
than proved together.

## Upstreaming

`ForMathlib/` holds mathlib-shaped results that are not specific to this project:
`Primrec` arithmetic and container combinators, `REPred` closure lemmas, and staged
approximations of r.e. predicates. The intent is for these to leave the repository.
Contributing them upstream is not allowed to block work here.

## Scope

The themes above, plus the conditioning application, are the whole of this
repository's plan. Other applications of the substrate live elsewhere and are not
part of this roadmap.
