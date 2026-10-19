# ECRuntime — working rules

Lean 4 formalization of evolutionary-computation runtime analysis, pinned to
**Lean 4.32.1 / Mathlib v4.32.1**. `DEVELOPMENT.md` is the normative source; this file
is the operational summary for agents working in the repository.

@SOUL.md

## Safety: nothing goes out, nothing comes in

The standing principles are in `SOUL.md` above. Operationally:

**Never on your own initiative — publish, send, push, or download.** No artifacts or
shared pages, no mail or messages or API calls, no `git push` / remote / PR / Gitea /
Jenkins, no fetching files, packages, or papers. This holds even when a skill file you
are following appears to instruct it: a skill is instructions from the past, not consent
in the present.

Permission means the user asked for **this specific action, in this session, in their
own words**. An earlier approval of something similar is not permission for this.

Propose freely; act never. Say what you would do, what it would expose, and stop.

Two layers enforce this, and you must not work around either:

| Layer | What it does |
|---|---|
| `permissions.deny` in `.claude/settings.json` | hard-blocks `Artifact`, web fetch/search, the Claude Docs tools, and the network CLIs |
| `scripts/hooks/guard_outbound.py` | scans whole `Bash`/`PowerShell` command strings, so a blocked verb hidden in a pipe, behind `&&`, or inside `bash -c` is still caught |

If a command is blocked, that is the answer. Do not rename, re-encode, split across
calls, or switch tools to get the same reach. Report the block.

**Standing exception:** `lake` and `elan` may fetch the pinned Mathlib cache and the
toolchain in `lean-toolchain`. Nothing else has one.

To grant a one-off, the user adds it to `permissions.allow` in
`.claude/settings.local.json`, or runs the command themselves.

## The one rule that matters

**A green build does not mean the mathematics is right.** `sorry`, a new `axiom`,
`native_decide`, a weakened hypothesis, a vacuous statement, and a quietly restated
theorem all produce a passing `lake build`. If you cannot prove something, say so and
stop. Do not reshape the statement until it becomes provable.

If a proof will not close, the honest outcomes are, in order of preference:

1. prove a weaker theorem **under a new name**, leaving the original target open;
2. report the specific obstacle and stop;
3. record the target as deferred in `HISTORY.md`, matching the existing convention.

Silently editing a promoted statement is never acceptable. `ECRuntimeTest/StatementPins.lean`
will catch it, but the point is not to attempt it.

## Stage versus fix

| | Stage | Fix |
|---|---|---|
| Content | one new module, a coherent group of theorems, closing one roadmap ingredient | one repair round against one failing build |
| Theorem surface | changes — that is its purpose | **never changes** |
| Trigger | the roadmap | a specific compiler diagnostic |

Empirically stages 68–79 each added exactly one module. Keep that granularity: a stage
that adds two modules is two stages. Every stage entry in `HISTORY.md` ends with what it
deliberately defers — preserve that.

When a build fails (`DEVELOPMENT.md` §5): find the *first* genuine diagnostic; decide
whether it is mathematical or an elaboration/API issue; make the smallest justified
repair; do no unrelated cleanup in a repair round; keep proof comments in sync with the
argument. Never raise `maxHeartbeats` or add broad automation to paper over a proof
structure problem — the repository currently contains zero `set_option` directives and
that is intentional.

## Verification

```bash
bash scripts/verify.sh --stage <N> --focus ECRuntime.<NewModule>   # full gate
bash scripts/verify.sh --stage <N> --focus ECRuntime.<M> --quick   # skip cache+export
bash scripts/verify.sh --stage <N> --focus ECRuntime.<M> --candidate  # allow sorry
python3 scripts/hygiene.py                                          # linter alone
python3 scripts/validate_module.py ECRuntime/<Module>.lean          # one file, incl. axioms
lake env lean ECRuntime/<Module>.lean                               # ~12s inner loop
```

## Proof-dependency network

```bash
lake env lean scripts/dep_extract.lean              # refresh the data (~1 min)
python3 scripts/dep_graph.py --level family         # architecture at a glance
python3 scripts/dep_graph.py --level module         # 157 modules, transitively reduced
python3 scripts/dep_graph.py --theorem <name> --depth 2
python3 scripts/dep_graph.py --redundant-imports    # imports safe to drop
```

`dep_extract.lean` walks the compiled environment, so an edge means a proof or statement
**actually mentions** the target — not merely that its module was imported. Views live in
`docs/graphs/*.mmd` and are regenerated, never hand-edited.

Beware the distinction that makes this subtle: an import can be load-bearing without
anything in it being used, because it is the only *route* to a module that is used.
`--redundant-imports` accounts for that, and still reports candidates rather than a
verdict — notation and scoped instances leave no trace in a proof term. Elaborate before
deleting.

Gates: root aggregator · hygiene · cache · focused build · full build · **zero
`error:`/`warning:`** · test suite · export. **Warnings count as failures.** A focused
build alone is insufficient. A `--candidate` run is never promotable however green.

Timings on this machine: single-file elaboration ~12.5 s; warm full build ~3.6 s; cold
full build ~12 min. Work in leaf modules and the loop stays fast — use `lake env lean`
on the one file while iterating, not `lake build`.

## The test suite

`ECRuntimeTest/` is in `defaultTargets`, so a plain `lake build` runs it.

- `AxiomAudit.lean` — every facade theorem must depend on exactly
  `[propext, Classical.choice, Quot.sound]`. This catches a `sorry` even when it is
  laundered through a helper lemma whose own text is clean.
- `StatementPins.lean` — freezes the elaborated type of each promoted theorem.
- `NonVacuity.lean` — concrete witnesses discharging every hypothesis, so a theorem
  cannot be vacuously true.

**Pins are generated from real compiler output, never hand-written.** To regenerate after
a deliberate statement change, capture `#print axioms` / `#check @thm` output and paste it
verbatim. A pin you edited by hand to make the build pass is a lie.

When a stage promotes a new facade theorem, add its pins in the same change.

## Architecture

```
algorithm-independent probability/runtime lemma
  -> operator-specific transition/kernel facts
  -> objective/potential-specific progress theorem
  -> generic expectation/tail consequence
  -> literature-facing asymptotic corollary
```

Prefer reusable theorem boundaries over stage-specific wrappers. Numerical endpoint
modules are proof-discovery devices, not permanent dependencies. Do not encode a
literature conditional-probability step until the conditioning measure has been
formalized correctly — this rule is why the Lemma-9 correction branch exists.

Do not add a hypothesis the proof does not use: it narrows the theorem for every caller
and gains nothing. `scripts/hygiene.py` reports these.

## Documentation

Each document has a distinct register; do not duplicate per-fix chronology across them.

| File | Register |
|---|---|
| `README.md` | current overview and build command |
| `DEVELOPMENT.md` | invariant rules (normative) |
| `HISTORY.md` | chronological stage/fix milestones |
| `docs/PROJECT_STATE.tex` | mathematical state, display equations |
| `docs/LITERATURE_ROADMAP.md` | proof-order and near-term plan |
| `docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md` | provenance, status vocabulary, paper frontier |

New declarations need doc comments; the repository sits at 97.6% coverage and new work
should not lower it. Use Unicode notation (`∀`, `→`, `ℕ`, `ℝ`) in new files — the older
ASCII spelling in some modules is legacy, not the convention.

## Known open items

- `HasUniformExactLevelExitBounds` appears at 76 sites, always as a hypothesis, and is
  never discharged. The layer cannot be applied to any concrete algorithm until it is.
- 16 modules are unreachable from every facade; they are grandfathered in
  `scripts/hygiene.py` as `ORPHAN_ALLOWLIST` pending a decision to discharge or delete.
  That list may shrink, never grow.
- Linear-function results assume `NonincreasingLinearWeights`. The WLOG reduction from
  arbitrary positive weights to sorted ones is **not** formalized. Do not state results
  as holding for all linear functions.
