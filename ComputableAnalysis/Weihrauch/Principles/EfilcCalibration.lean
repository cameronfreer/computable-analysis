/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import ComputableAnalysis.Weihrauch.Principles.WKLEfilc
import ComputableAnalysis.Weihrauch.Principles.EfilcWKL
import ComputableAnalysis.Weihrauch.Principles.HallEfilc

/-!
# `EFILC ≡W WKL`, and `Hall` below both

The three reductions proved separately compose. Nothing new is constructed here: each
result is an assembly of reductions already certified in the modules above, so the codes
are the composites the witness calculus builds.

`efilc_equiv_wkl` pairs `efilc_le_wkl` with `wkl_le_efilc`. The equivalence is stated at
`≡W` and not `≡sW` because the two *certified reductions* are asymmetric: `WKL ≤sW EFILC`
is strong, while the reduction certified in the other direction is only ordinary, its
decoder consulting the chunk widths of the *input* system. That is a fact about these
codes, not about the degrees: whether some other strong reduction `EFILC ≤sW WKL` exists
is not addressed here, and no lower bound is claimed in either direction.

`hall_le_wkl` composes `Hall ≤sW EFILC` with `EFILC ≤W WKL`. It is an upper bound only:
that countable Hall is *no harder* than weak Kőnig's lemma. The reverse direction, and
hence the degree of `Hall`, is untouched here.

These are the statements the cross-repository interchange layer names, so they are stated
once, at the top of the `EFILC` block, rather than being re-derived at each use.
-/

namespace ComputableAnalysis

/-- **`EFILC ≡W WKL`**: explicit finite inverse-limit compactness and weak Kőnig's lemma
are Weihrauch equivalent. The `WKL`-to-`EFILC` half is in fact strong; the converse is
ordinary, its decoder consulting the input system's chunk widths. -/
theorem efilc_equiv_wkl : EFILC ≡W WKL :=
  ⟨efilc_le_wkl, strongWeihrauch_le_weihrauch wkl_le_efilc⟩

/-- **`Hall ≤W WKL`**: countable Hall, in the one-sided relation-plus-enumerator
presentation, is no harder than weak Kőnig's lemma — through `EFILC`. An upper bound
only; nothing is claimed about the converse. -/
theorem hall_le_wkl : Hall ≤W WKL :=
  (strongWeihrauch_le_weihrauch hall_le_efilc).trans efilc_le_wkl

end ComputableAnalysis
