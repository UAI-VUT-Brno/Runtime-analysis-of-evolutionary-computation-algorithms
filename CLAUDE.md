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
| `scripts/hooks/guard_outbound.ps1` | scans whole `Bash`/`PowerShell` command strings, so a blocked verb hidden in a pipe, behind `&&`, or inside `bash -c` is still caught |

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
3. record the target as deferred in its research line in `docs/history/`, matching the existing convention.

Silently editing a promoted statement is never acceptable. `ECRuntimeTest/StatementPins.lean`
will catch it, but the point is not to attempt it.

## Stage versus fix

| | Stage | Fix |
|---|---|---|
| Content | one new module, a coherent group of theorems, closing one roadmap ingredient | one repair round against one failing build |
| Theorem surface | changes — that is its purpose | **never changes** |
| Trigger | the roadmap | a specific compiler diagnostic |

Empirically stages 68–79 each added exactly one module. Keep that granularity: a stage
that adds two modules is two stages. Every stage entry in `docs/history/` ends with what it
deliberately defers — preserve that.

New stages on `main` are numbered from **461** upward. Numbers 80–460 appear in the doc
comments of merged modules as the source checkpoint's own stages; reusing them would make
a stage reference ambiguous.

When a build fails (`DEVELOPMENT.md` §5): find the *first* genuine diagnostic; decide
whether it is mathematical or an elaboration/API issue; make the smallest justified
repair; do no unrelated cleanup in a repair round; keep proof comments in sync with the
argument. Never raise `maxHeartbeats` or add broad automation to paper over a proof
structure problem — the repository currently contains zero `set_option` directives and
that is intentional.

## Verification

```bash
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<NewModule>    # full gate
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<M> -Quick     # skip cache+export
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<M> -Candidate # allow sorry
lake env lean --run scripts/audit.lean strict                            # audit alone, ~35s
lake env lean ECRuntime/<Module>.lean                                    # ~12s inner loop, one file
```

There is no single-module validator. `lake env lean <file>` gives elaboration errors and
warnings for one file; `scripts/audit.lean` reads the compiled environment and reports axiom
integrity, doc coverage, unused binders and facade reachability for the whole repository in
one pass, so filter its output for the module you care about. For one theorem's axioms:

```bash
printf '%s\n' 'import ECRuntime.<Module>' '#print axioms ECRuntime.<thm>' | lake env lean --stdin
```

## Proof-dependency network

```bash
# architecture at a glance
lake env lean --run scripts/audit.lean graph --level family
# every module, transitively reduced
lake env lean --run scripts/audit.lean graph --level module
# one module's direct neighbourhood
lake env lean --run scripts/audit.lean graph --module <name>
# one theorem's dependency tree
lake env lean --run scripts/audit.lean graph --theorem <name> --depth 2
# imports safe to drop
lake env lean --run scripts/audit.lean graph --redundant-imports
```

Add `--output <path>` to write a file instead of stdout; `--no-reduce` keeps implied
edges in the module view.

The same program also emits machine-readable state:

```bash
lake env lean --run scripts/audit.lean json --output .verify/state.json
```

`audit.lean` walks the compiled environment, so an edge means a proof or statement
**actually mentions** the target — not merely that its module was imported. Views live in
`docs/current/graphs/*.mmd` and are regenerated, never hand-edited.

`docs/current/facades.md` lists every public facade with its paper, its theorems and their
pins; `docs/history/README.md` and `docs/roadmap/papers/README.md` are generated indexes.
None of them is part of the `verify.ps1` gate, so regenerate them whenever a facade, a
history entry, a paper file or a citation changes, and run the documentation checks:

```bash
pwsh -File scripts/facade_index.ps1
pwsh -File scripts/docs_index.ps1 -Check
```

Beware the distinction that makes this subtle: an import can be load-bearing without
anything in it being used, because it is the only *route* to a module that is used.
`--redundant-imports` accounts for that, and still reports candidates rather than a
verdict — notation and scoped instances leave no trace in a proof term. Elaborate before
deleting.

Gates: root aggregator · hygiene · cache · focused build · full build · **zero
`error:`/`warning:`** · test suite · graphs · export. **Warnings count as failures.** A focused
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
- `VerifiedPapersAxiomAudit.lean`, `VerifiedPapersStatementPins.lean` — the axiom and
  statement pins for every theorem cited in `docs/current/papers/`. When a paper file
  starts citing a new theorem, pin it here in the same change; `docs_index.ps1 -Check`
  fails otherwise.

Coverage gap: of the 147 merged public facades, only the 14 whose theorems the paper
audit cites are pinned, and none of the merged theorems has a non-vacuity witness yet.

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
and gains nothing. `scripts/audit.lean` reports these.

## Agents and skills

Versioned under `.claude/`, so they travel with the repository instead of living in one
developer's profile.

| Name | Role |
|---|---|
| `/propose-paper` | mode 1, author: adds a paper to the roadmap; gate: roadmap acceptance |
| `/review-paper-proposal` | mode 1, review: a contributor's roadmap pull request |
| `/stage` | mode 2, author: runs one stage end to end, with two human gates |
| `/review-statement` | mode 2, review: a contributor's Statement proposal issue; gate: statement approval |
| `/review-implementation` | mode 2, review: a contributor's Lean pull request; gate: promotion |
| `/lean-validate` | checks one module, then interprets the findings |
| `lean-architect` | statements only, never proofs |
| `lean-prover` | discharges `sorry` against frozen statements |
| `lean-auditor` | adversarial, read-only |
| `lean-scribe` | the documentation set: history, current state, roadmap |

No agent changes files. `lean-architect` and `lean-scribe` are read-only; `lean-prover`
and `lean-auditor` add only `Bash`, for the toolchain and read-only commands. Agents return
new file contents and exact edits as text; the main conversation applies them, and
`permissions.ask` in `.claude/settings.json` makes the user approve every `Edit`, `Write`,
`NotebookEdit`, `Bash` and `PowerShell` call.

Adding theorems is `/stage` or, for a contributor's work, `/review-statement` followed by
`/review-implementation`. There is deliberately no lighter path that adds them while
skipping the statement and promotion gates. Every statement approval is recorded in the
history entry as `Statements approved by <maintainer> on <YYYY-MM-DD>.`; from stage 461 on,
`scripts/docs_index.ps1 -Check` enforces it. The review skills prepare comments and replies
as text; posting, merging and pushing stay with the maintainers.

## Documentation

Each document has a distinct register; do not duplicate per-fix chronology across them.

| File | Register |
|---|---|
| `README.md` | current overview and build command |
| `DEVELOPMENT.md` | invariant rules (normative) |
| `docs/history/<line>.md` | chronological milestones, one file per research line; `README.md` there is a generated index |
| `docs/current/` | the current state: `README.md` (checkpoint, status vocabulary, coverage table), `papers/<key>.md`, generated `facades.md` and `graphs/` |
| `docs/roadmap/` | `README.md` proof-order and near-term plan, `frontier.toml` queue that `/stage` selects from, `papers/<key>.md` one per candidate paper |

A paper has one key everywhere: `<first-author>-<year>`, or `<first>-et-al-<year>` from
four authors. `docs/history/archive/` holds the documents frozen at Stage 79 — read, never
extended: `FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md` (its frontier sections now live
verbatim in `docs/roadmap/papers/`) and `PROJECT_STATE.tex`. The root `HISTORY.md` only
points to `docs/history/`.

`CONTRIBUTING.md`, `CODE_OF_CONDUCT.md`, `CONTRIBUTORS.md`, `CITATION.cff`, `LICENSE`
and `.github/` serve the planned public repository. Its content is exactly what
`scripts/export_repository.ps1 -Profile public` exports. That includes the whole Claude
Code setup — `CLAUDE.md`, `SOUL.md`, `.claude/settings.json`, `.claude/agents/`,
`.claude/skills/` and the guard hooks — so that a public clone works the same; only
`.claude/settings.local.json` (one machine's grants) never leaves this repository. The root
`README.md` documents the agent and skill workflow and warns that it is used at one's own
risk; keep that section in step with the agents and skills. Keep `CONTRIBUTING.md` consistent
with `DEVELOPMENT.md` when either changes. External pull requests come in exactly two
modes: mode 1 adds a paper to `docs/roadmap/` (from `docs/roadmap/TEMPLATE-paper.md`,
plus a `frontier.toml` target), mode 2 implements a roadmap target in Lean after a
`statement-approved` issue. Everything else is an issue that maintainers act on. When `audit.lean` warnings legitimately change,
regenerate `.github/audit-baseline.txt` (CI rejects any warning not in it).

The CI workflow lives in `scripts/public/ci.yml`, never in `.github/workflows/` here: this
repository must not run it. The public export publishes it as `.github/workflows/ci.yml`.

New declarations need doc comments. `scripts/audit.lean strict` reports every own
declaration without one; on 26 October 2026 that was 280 of 2951 (90.5% covered), 73 of
them compiler-generated (`congr_simp`, `ctorIdx`, instances). New work must not add to
that list. Use Unicode notation (`∀`, `→`, `ℕ`, `ℝ`) in new files — the older
ASCII spelling in some modules is legacy, not the convention.

## Known open items

- `HasUniformExactLevelExitBounds` appears at 76 sites, always as a hypothesis, and is
  never discharged. The layer cannot be applied to any concrete algorithm until it is.
- `LevelChargeExactResidence` is unreachable from every facade; it is grandfathered in
  `scripts/audit.lean` as `orphanAllowlist` pending a decision to discharge or delete.
  That list may shrink, never grow. It held 16 modules until the 547-module merge
  made 15 of them reachable.
- Linear-function results assume `NonincreasingLinearWeights`. The WLOG reduction from
  arbitrary positive weights to sorted ones is **not** formalized. Do not state results
  as holding for all linear functions.
