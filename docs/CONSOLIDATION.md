# Final consolidation handoff — 23 October 2026

## Certified checkpoint and evidence

The user-run **Stage 130 Round 56** completed the repository consolidation.
The accompanying `stage130_round56_results.zip` contains
`.verify/stage130_round56_consolidated/status.txt` and the official
`.verify/stage-130_round56/status.txt`. Both record successful gates.

| Check | Observed evidence |
| --- | --- |
| Full official eight-gate verification | all gate return codes `0`, `overall=0` |
| Independent consolidated public gate | `consolidation_public_gate=PASSED` |
| Stage 166 integrated promotion | `stage166_promotion_integration=PASSED_PROMOTED` |
| Public module reachability | 249 of 249 public Lean modules |
| Regression Lean sources | 5 retained; build passed |
| Approved-open theorem candidates | 0 |
| Frozen approved Stage 166 signature | source audit passed against public module |
| Axiom probe (four principal theorems) | only `propext`, `Classical.choice`, `Quot.sound` |
| Strict historical-warning comparison | 233 observed, 282 historical baseline; **0 new warnings** |
| Repository export | completed in official gate |

These results certify the public Lean source in the **Round 56** snapshot.
The final release-oriented maintenance pass removed only redundant round
wrappers, renamed the consolidated verification runner and revised documents
and exporter/audit bookkeeping. **All 249 public `.lean` files, the root
`ECRuntime.lean`, and all five Lean regression modules are byte-for-byte
identical to the successful Round 56 snapshot.** The final renamed runner and
updated scripts have source/syntax tests, but have not themselves been run
through Lean/PowerShell in this authoring environment; execute the command
below for a fresh end-to-end packaging verification.

## Reproduction

From the repository root in the pinned Lean 4.32.1 / Mathlib v4.32.1
environment, with PowerShell (`pwsh`) installed:

```bash
lake build ECRuntime ECRuntimeTest
bash run_verification.sh "$PWD"
```

The runner invokes `scripts/verify.ps1` and the strict compiled-environment
`lake env lean --run scripts/audit.lean strict` gate, compares current warnings
to `scripts/hygiene_baseline.txt`, checks representative theorem axioms and
requires the approved Stage 166 theorem-header hash. It creates
`ECRuntime_verification_results.zip` in the calling directory. The pinned
Mathlib dependency may need its permitted cache/toolchain fetch on a fresh
machine; no publishing or remote push is part of this workflow.

## Maintained repository boundary

- Public proof source: `ECRuntime/`, `ECRuntime.lean`. No public theorem or
  proof was modified by this consolidation pass.
- Verification: `ECRuntimeTest/`, `ECRuntimeTest.lean`, `scripts/` and the
  sole top-level entrypoint `run_verification.sh`.
- Statement safeguards: `candidates/APPROVED_STATEMENTS.json` archives the
  Stage 166 approved exact theorem interface. There are no candidate `.lean`
  sources or active candidate marker. Its small-case arithmetic checker is
  an independent sanity check, **not** a proof.
- Literature correspondence: `docs/VERIFIED_PAPERS.md` enumerates 12
  paper-associated result families, matched Lean declarations and estimated
  **partial** coverage. No paper is certified as fully covered.
- Research frontier: `docs/OPEN_PROBLEMS.md`; detailed theorem-family
  summary: `docs/RESEARCH.md`; development standards: `DEVELOPMENT.md`.

Authorship, licensing, repository publication, and a new research theorem
stage are outside this handoff and have deliberately not been inferred.
