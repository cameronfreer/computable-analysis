# Computable Analysis

A Lean 4 library connecting mathlib's discrete computability stack to its classical
analysis stack, through explicit Type-2 machines, represented spaces, Weihrauch
reducibility, and computable probability. Mathlib has `Partrec`, `Nat.RecursiveIn`,
and `TuringDegree` on one side, and Polish spaces, standard Borel spaces, measures,
and kernels on the other; this library is the bridge, built so that each layer is
usable on its own terms.

**Status.** An actively developed research library, pre-1.0. Nothing is admitted:
no `sorry`s, no custom axioms, and every declaration is audited (see below). The
lower layers are stable; APIs in layers under active development may still change.

## Design commitments

These are the choices the whole library is built on, and the ones most likely to
differ from a reader's expectations.

- **Representations are explicit partial surjections.** Invalid names stay invalid;
  nothing is totalized by mapping junk to a default point. A representation is an
  object, not a typeclass instance.
- **Problems are relation-valued, partial, and multivalued.** Domain conditions live
  inside `accepts`, never as an unenforced side condition, so a problem's domain is
  derived rather than asserted.
- **Computability and reductions are witnessed by explicit `OracleCode`s**, always
  in the uniform order `∃ code, ∀ input` — never `∀ input, ∃ code`. Headline
  reductions are certified as named code pairs a consumer can reuse.
- **Classical mathematics inside, audited claims outside.** Semantic arguments may
  use classical logic freely; what is audited is that every declaration depends only
  on the standard axioms, and that no result is admitted.

`ARCHITECTURE.md` states these and the rest of the invariants precisely.

## Architecture

| Layer | Role |
| ----- | ---- |
| `ForMathlib` | Generic computability lemmas awaiting upstreaming |
| `TypeTwo` | Baire machines, universal evaluation, finite-use and prefix compilers |
| `RepresentedSpace` | Representations, realizers, computable maps and function spaces |
| `Metric` | Cauchy representations, effective metric presentations and reals |
| `Weihrauch` | Problem algebra, reductions, products, cylinders and parallelization |
| `Measure` | Computable measures, kernels, moments and conditioning |

## Selected results

Landmarks, not an inventory, and not a status report:

- `LPO.parallelize ≡sW Lim` — parallelized limited principle of omniscience
- `C₂ ≡sW LLPO` — finite binary choice against the lesser principle
- `WKL ≤sW LLPO.parallelize` — weak Kőnig's lemma below parallelized `LLPO`
- `EFILC ≡W WKL` and `Hall ≤W WKL` — inverse-limit compactness and countable Hall
- A computable Hausdorff moment theorem on the unit interval
- `Lim ≤sW Disintegrate` on Cantor space — the lower bound for conditioning, after
  Ackerman–Freer–Roy ([arXiv:1509.02992](https://arxiv.org/abs/1509.02992))

## Building and verification

```
lake exe cache get
bash scripts/check.sh
```

The gate builds the library, fails on any `sorry`-like token or `axiom` declaration
in the sources, and runs an axiom audit over every declaration owned by a
`ComputableAnalysis` module — private and compiler-generated included — asserting
dependence only on `propext`, `Classical.choice`, and `Quot.sound`. A headline list
additionally guards named results against silent deletion or renaming.

The toolchain and mathlib revision are pinned in `lean-toolchain` and
`lake-manifest.json`, which are authoritative.

## Documentation

| File | Contents |
| ---- | -------- |
| `ARCHITECTURE.md` | The invariants: representations, uniformity, reductions, codings |
| `ROADMAP.md` | Active themes and direction |
| `CONTRIBUTING.md` | Working practice: the gate, axiom policy, review discipline |
| `BLUEPRINT.md` | Historical implementation record; not authoritative for status |

Current state and open questions live in the
[issues](https://github.com/cameronfreer/computable-analysis/issues). Module
docstrings document the actual API.

## Citation and license

Released under the Apache License 2.0; see `LICENSE`.

To cite the library, use the repository and the commit you built against:

> Cameron Freer, *Computable Analysis: a Lean 4 formalization of Type-2 computability*.
> https://github.com/cameronfreer/computable-analysis
