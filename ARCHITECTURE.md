# Architecture

The invariants this library is built on. They are stable by intent: changing any of
them would invalidate a large fraction of the API, so they are stated once here rather
than restated per module. `BLUEPRINT.md` records how they were arrived at;
this file is what a reader needs.

## Naming and ambient types

Everything lives under the root namespace `ComputableAnalysis` — bare `Representation`
collides with mathlib's representation theory. Inside it, `Baire := ℕ → ℕ` and
`Cantor := ℕ → Bool`, carrying mathlib's `PiNat`/product topology rather than a
duplicate of it; finite words are `List ℕ` and `List Bool`.

Mathlib deliberately does not make the `PiNat` metric instances global, and neither
does this library: they are `scoped instance`s in `ComputableAnalysis.PiNatInstances`,
and downstream layers reach the metric only through presentation objects.

## The Type-2 primitive is coordinatewise

```lean
def OracleCode.eval (c : OracleCode) (p : Baire) : ℕ →. ℕ
```

Stream-level notions are derived from it — `Computes` for total operators,
`evalStream` for partial ones — and realization of represented maps and problems is
defined through `evalStream` on valid names only. `Baire →. Baire` is never an
unexplained primary object.

Code equality is syntactic (`DecidableEq OracleCode`); extensional equality is stated
only through `eval` lemmas, never as a quotient.

## Uniformity: the witness stays outside the quantifier

Always `∃ code, ∀ input`, never `∀ input, ∃ code`. In particular
`∀ p, Nat.RecursiveIn {p} (F p)` does **not** establish Type-2 computability of `F` —
the finite code witness must not depend on the input. First-order `Computable` is never
applied to `Baire → Baire`, since `Baire` is not `Primcodable`.

This is why reductions are certified as explicit code *pairs*: the pair is the witness,
and the theorem quantifies over inputs and over every realizer of the target problem
afterwards.

## Representations are partial surjections

A representation is `rep : Baire →. α` together with surjectivity, built as an explicit
object rather than a typeclass instance. Invalid names have no denotation: there is no
totalization by default point. For Cantor space, a name with any coordinate `≥ 2` is
simply not a name.

Metric computability is presentation-relative: an explicit bundle of a dense sequence
with semidecisions of both strict rational distance comparisons, not a typeclass. Fast
Cauchy names use the pinned rate `(2⁻¹)^n`, with the semantic predicate (this name
converges to *this* point) kept distinct from the syntactic one (the name is fast
Cauchy, no limit mentioned), so that incomplete spaces remain legitimate examples.

## Problems, and where promises live

A problem is relation-valued (`accepts : X → Y → Prop`), partial and multivalued, with
`Dom` derived from `accepts`. Consequently **every stream is a valid name of *some*
object**, and being a genuine tree, system, or family is a promise carried inside
`accepts` — never a condition on names, and never an unenforced side condition.

Each problem therefore comes with two lemmas: an `accepts_iff` unfolding the definition,
and a `dom_iff` identifying the domain in semantic terms. The second is usually where
the mathematical content sits — for weak Kőnig's lemma it *is* weak Kőnig's lemma.

## Ordinary and strong reduction are separate definitions

Both are given in a realizer-quantified form and a fixed-witness transformer form, with
the equivalence proved. Name pairing is `Baire.interleave`. The difference is exactly
what the postprocessor sees:

- **ordinary** (`≤W`): the postprocessor receives the original input interleaved with
  the oracle's answer;
- **strong** (`≤sW`): the postprocessor receives the answer alone.

`f ≤W g` holds iff there are codes `K, H` such that for *every* realizer `G` of `g` the
resulting operator realizes `f`.

Reductions are proved from the presented promises alone, independently of any ω-model or
provability-level relationship between the corresponding statements. Two consequences
worth stating plainly, because they are easy to over-read:

- an upper bound is never evidence for a lower bound;
- an *ordinary* reduction being the one certified is never evidence that no strong
  reduction exists. It is a fact about the codes exhibited, not about the degrees.

## Codes are named, and shapes are compiled once

A code used by more than one theorem is extracted once — specified by a lemma, not
reconstructed inline — so that consumers share a single combinator. Where several
reductions have the same shape, a uniform *compiler* takes the semantic data and
discharges the representation bookkeeping once; the compilers are reusable independently
of the principles that motivated them.

## The computational / classical boundary

Semantic mathematics may be classical: measure theory, topology, and existence arguments
use mathlib's classical library freely, and `Classical.choice` appears throughout. What
is disciplined is the *effective* content — codes are finite syntax, uniformity is
enforced by quantifier order, and computable measures are computable points of a
represented space rather than being identified with densities or samplers.

The audit is what keeps the boundary honest: it asserts that every declaration in the
library depends only on `propext`, `Classical.choice`, and `Quot.sound`, so nothing has
been admitted or bolted on as a custom axiom. See `CONTRIBUTING.md`.
