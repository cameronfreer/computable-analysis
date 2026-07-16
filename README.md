# Computable Analysis

A Lean 4 formalization of Type-2 (TTE) computable analysis, bridging mathlib's
discrete computability stack and its classical Polish/Borel/measure stack:

- a universal finite oracle-code model on Baire space (`ℕ → ℕ`);
- represented spaces, computable points, and computable maps;
- partial multivalued problems with ordinary and strong Weihrauch reducibility;
- benchmark principles (`LPO`, `LLPO`, `lim`);
- computable metric presentations and fast Cauchy representations;
- computable probability measures on Cantor space via cylinder values.

`BLUEPRINT.md` is the self-contained specification: pinned conventions, the unit
sequence with status, and the acceptance checklist.

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

See [ROADMAP.md](ROADMAP.md) for the public plan and [BLUEPRINT.md](BLUEPRINT.md)
for the implementation contract.
