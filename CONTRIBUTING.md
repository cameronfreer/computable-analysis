# Working practice

Conventions for changing this repository. `ARCHITECTURE.md` covers what the library
is; this file covers how work on it is done.

## The gate

```
bash scripts/check.sh
```

is the single acceptance check. It builds the library, rejects any `sorry`-like token
or `axiom` declaration in the sources, and runs the axiom audit. Everything that lands
passes it first.

**Never pipe the gate — or any build — into another command.** A shell pipeline takes
the exit status of its *last* stage, so

```
bash scripts/check.sh | tail          # WRONG: reports success on a failed gate
lake build | tail -40                 # WRONG: same
```

report success no matter what happened upstream. Redirect, capture the status, and
check it — noting that a `;`-chain has the same defect, since its status is the *last*
command's, so the check must come after the log is displayed:

```
bash scripts/check.sh > gate.log 2>&1
status=$?
tail -20 gate.log
test "$status" -eq 0
```

This has produced false "green" readings more than once, in both directions —
believing a broken build was fine, and reporting it as fine to someone else.

## Axiom policy

The audit sweeps every declaration owned by a `ComputableAnalysis` module, including
private and compiler-generated ones, and asserts dependence only on `propext`,
`Classical.choice`, and `Quot.sound`. No custom axiom is introduced to make a proof go
through; if a proof appears to need one, that is a design question, not a licence.

`scripts/AxiomAudit.lean` also carries a headline list of named results. Because the
names resolve at elaboration, deleting or renaming one fails the gate. Extend it when
adding a result that consumers will depend on.

## Commits and review

- One self-contained change per commit, gated before it is made. Anything that
  compiles and is coherent may land, even if the surrounding work is unfinished; do
  not amend published commits.
- Commit messages say what changed and *why*, not how the work proceeded.
- Everything is world-readable. No private plans in code, docstrings, commit
  messages, or issues.
- Substantial layers are frozen by signature review before implementation, so that
  the API is agreed before proofs are written against it.

## Docstrings

Module and declaration docstrings describe the API and the mathematics, in terms that
stay true. They are not a record of how the proof was found, and they do not carry
process vocabulary or status.

State results at exactly their strength. In particular, do not let a certified upper
bound read as a lower bound, or the absence of a strong reduction in the development
read as a claim that none exists.

## Environment

- Toolchain and mathlib revision are pinned in `lean-toolchain` and
  `lake-manifest.json`. Run `lake exe cache get` before a first build.
- Concurrent work uses one git worktree per task, so that builds do not contend over
  a shared `.lake`. Verify what is actually on the remote rather than inferring push
  state, and pin immutable revisions when referring to another repository.
- Prefer extracting a heavy sub-proof into a lemma over raising elaboration limits.
