#!/usr/bin/env bash
# Project gate: build, source-level sorry/axiom scan, and the axiom audit — an
# environment sweep over every declaration owned by a ComputableAnalysis module
# (including private/generated ones), plus the headline regression list. Run from
# anywhere; operates on the repository root.
set -euo pipefail
cd "$(dirname "$0")/.."

lake build

# grep exits 1 when nothing matches, so invert: any hit fails the gate.
# (Scope note: `unsafe`/`partial`/`@[implemented_by]` are compilation-side and cannot
# affect proof soundness, so they are deliberately not gated; `native_decide` is caught
# structurally by the AxiomAudit environment sweep.)
if grep -Ernw --include='*.lean' 'sorry|sorryAx|admit' ComputableAnalysis ComputableAnalysis.lean scripts; then
  echo "check.sh: FAIL — sorry-like token found in sources" >&2
  exit 1
fi
# Matches the `axiom` keyword after optional attributes/modifiers, so decorated forms
# (`private axiom`, `@[simp] axiom`, ...) fail too, without matching prose in comments.
if grep -Ern --include='*.lean' \
    '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private|protected|unsafe|noncomputable|scoped|local)?[[:space:]]*axiom[[:space:]]' \
    ComputableAnalysis ComputableAnalysis.lean scripts; then
  echo "check.sh: FAIL — axiom declaration found in sources" >&2
  exit 1
fi

lake env lean scripts/AxiomAudit.lean

echo "check.sh: all gates passed"
