# ECRuntime

**Runtime analysis of evolutionary algorithms, machine-checked in Lean 4.**

How many evaluations does a `(1+1)` evolutionary algorithm need to optimize OneMax,
LeadingOnes, or a linear function? The evolutionary-computation literature answers this
with delicate probabilistic arguments. ECRuntime rebuilds those arguments from first
principles and has a proof assistant check every step.

**547 Lean modules · Lean 4.32.1 / Mathlib v4.32.1 · Apache License 2.0**

## Status

- **Verified build.** The library passes the full verification gate (26 October 2026):
  zero errors and warnings, and no declaration depends on `sorry` or a non-standard
  axiom.
- **Paper coverage.** Results from
  [13 publications](docs/current/README.md#paper-by-paper-coverage) are audited against
  their sources; no publication is claimed as completely formalized. The closest are
  [Doerr and Doerr (2013)](docs/current/papers/doerr-doerr-2013.md), where both numbered
  headline theorems have certified counterparts, and
  [Böttcher, Doerr and Neumann (2010)](docs/current/papers/boettcher-doerr-neumann-2010.md),
  with exact fixed-rate and adaptive LeadingOnes runtimes and the optimal rates. Each paper
  has its own file in [`docs/current/papers/`](docs/current/papers/) listing what is
  certified and what is missing.
- **Open.** Not every merged statement has been reviewed against its paper, and the
  merged theorems lack non-vacuity witnesses (see
  [below](#how-the-claims-are-kept-honest)). What comes next is in
  [`docs/roadmap/`](docs/roadmap/README.md).

## Quick start

Install [elan](https://github.com/leanprover/elan), Lean's version manager. On the first
`lake` command it reads `lean-toolchain` and installs the pinned Lean 4.32.1
automatically; you never install Lean by hand. Then:

```bash
lake exe cache get                               # pinned Mathlib build cache
lake build                                       # the library and the regression suite
lake env lean --run scripts/audit.lean strict    # axioms, doc comments, unused hypotheses, reachability
```

With PowerShell 7, `pwsh -File scripts/verify.ps1 -Stage <label>` runs the complete gate:
audit, builds, zero diagnostics, dependency graphs and export.

## Repository layout

```text
ECRuntime/          the Lean library, one module per file
ECRuntimeTest/      regression suite: axiom audit, statement pins, non-vacuity witnesses
scripts/            verification, audit and documentation tooling; scripts/hooks/ guards
.claude/            Claude Code agents, skills and permission settings (see below)
docs/
  current/          what holds today: checkpoint, coverage, one file per paper
  history/          what was done: one file per research line
  roadmap/          what comes next: priorities, target queue, one file per paper
```

## Architecture

The Lean sources live in [`ECRuntime/`](ECRuntime/), one module per file; the regression
suite is in [`ECRuntimeTest/`](ECRuntimeTest/). Theorems are layered from general to
specific:

```text
algorithm-independent probability/runtime lemma
        -> operator-specific transition/kernel facts
        -> objective/potential-specific progress theorem
        -> generic expectation/tail consequence
        -> asymptotic/literature-facing corollary
```

[`docs/current/graphs/architecture.mmd`](docs/current/graphs/architecture.mmd) shows the
module families and how many proof dependencies run between them;
[`modules.mmd`](docs/current/graphs/modules.mmd) shows all modules. Both are generated
from the compiled library, so an edge means a proof actually uses the target. For one
module's neighbourhood:

```bash
lake env lean --run scripts/audit.lean graph --module <name>
```

## How the claims are kept honest

Compilation is necessary but does not by itself establish absence of added axioms,
non-vacuity, or faithful paper-level coverage. The regression suite and the audit check
what a passing build does not:

| Check | What it catches |
|---|---|
| **Axiom / source-hygiene audit** | `scripts/audit.lean` checks every declaration for transitive admitted or non-standard-axiom dependencies, doc comments and unused signature hypotheses, and every module for reachability from the 153 public facades (6 original, 147 merged). |
| **Statement pins** | The original theorem statements and every theorem cited in `docs/current/papers/` are frozen, together with their axiom sets; the remaining merged declarations are not yet pinned. |
| **Non-vacuity witnesses** | Concrete instances discharge the hypotheses of the original facades and three merged results; this is not a universal automatic non-vacuity proof. The merged theorems cited in `docs/current/papers/` have no witnesses yet. |

Reachability is measured from an explicit, maintained set of 153 public facades rather
than from the umbrella root. The pre-existing `LevelChargeExactResidence`
grandfathered-orphan warning is retained; any newly disconnected module is an error.
Warnings count as failures. The gate tables of every verification run are in
[`docs/history/repository.md`](docs/history/repository.md).

**Not every formulation has been reviewed.** A proof checks that a statement holds, not
that the statement says what the paper says; that takes a human reading it. The doc
comments of 52 merged modules record that their statement was unapproved or only
proposed when written, and no later approval is recorded on `main`. 18 of them are
public facades, and two are cited in `docs/current/papers/` as paper evidence:
`RLSAllDimensionPaperCenteredExact` (P02a) and `RLSStrictMonotoneFixedTargetExact`
(P07). Treat those results as proved but not yet confirmed to match their source.

## What this does *not* claim

See [Scope and limits](docs/current/README.md#scope-and-limits) in `docs/current/`.

## Contributing, license and citation

Contributions are welcome through pull requests from forks, in exactly two modes:
**proposing a paper** for the roadmap, or **implementing** results of a roadmap paper in
Lean, where every new theorem starts as a statement proposal that a maintainer approves
before any proof is written. Problems are reported in issues. The maintainers curate the
repository and alone merge into `main`. See
[`CONTRIBUTING.md`](CONTRIBUTING.md) and [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md).

ECRuntime is licensed under the [Apache License 2.0](LICENSE). To cite it, use
[`CITATION.cff`](CITATION.cff); contributors are listed in
[`CONTRIBUTORS.md`](CONTRIBUTORS.md).

## AI agents and skills

> [!WARNING]
> **Use the agents and skills at your own risk.** They drive an AI model through
> [Claude Code](https://claude.com/claude-code). They can propose a statement that does not
> match its paper, a proof that compiles for the wrong reason, or documentation that
> claims more than is proved. Nothing is certified because an agent produced it: every
> statement must pass a human statement gate, and every result a human promotion gate and
> the full verification gate. The configuration is provided as is, without warranty
> (Apache License 2.0, sections 7 and 8). You are responsible for every change you accept.

The repository versions the Claude Code setup the maintainers use. It needs Claude Code,
and PowerShell 7 for the guard hooks.

**Safeguards.** [`CLAUDE.md`](CLAUDE.md) and [`SOUL.md`](SOUL.md) hold the binding rules:
nothing is published, sent, pushed or downloaded on an agent's initiative, and no statement
is weakened to make a proof go through. [`.claude/settings.json`](.claude/settings.json)
denies network and publishing tools and makes you approve **every** file change and every
command (`Edit`, `Write`, `NotebookEdit`, `Bash`, `PowerShell`). The hooks in
[`scripts/hooks/`](scripts/hooks/) block outbound commands and refuse `sorry`, `axiom`,
`native_decide`, `unsafe` and `maxHeartbeats` in `ECRuntime/`.

**Agents** ([`.claude/agents/`](.claude/agents/)) change no files; they return text, which a
skill applies after your approval.

| Agent | Role | Tools |
|---|---|---|
| `lean-architect` | Lean statements (never proofs); feasibility of a roadmap paper | read-only |
| `lean-prover` | proofs for approved statements, as exact edits | read-only + `Bash` for the toolchain |
| `lean-auditor` | adversarial review: axioms, faithfulness, vacuity, approval, scope | read-only + `Bash`, read-only commands |
| `lean-scribe` | documentation drafts: history, current state, roadmap, credits | read-only |

**Skills** ([`.claude/skills/`](.claude/skills/)) follow the two
[contribution modes](CONTRIBUTING.md#two-ways-to-contribute); ▲ marks a human decision:

```text
Mode 1 — a paper for the roadmap
  author:  /propose-paper   paper text from you -> paper file + feasibility
                            -> frontier.toml target -> ▲ roadmap acceptance
  review:  /review-paper-proposal   contributor's branch -> scope, quotes, duplicates
                            -> ▲ accept / request changes / decline -> draft comment

Mode 2 — an implementation in Lean
  author:  /stage           target -> statements -> ▲ statement gate (approval recorded)
                            -> proofs -> audit -> pins -> docs -> verify.ps1
                            -> ▲ promotion gate
  review:  /review-statement        issue text -> elaboration, faithfulness, hypotheses
                            -> ▲ statement gate -> draft reply
           /review-implementation   contributor's branch -> exact statements, scope,
                            audit, full gate -> ▲ promotion gate -> docs, stage, credit

Any time:  /lean-validate <file>    one module: elaboration, axioms, docs, reachability
```

The skills never post, push, merge or fetch: review comments and issue replies are drafted
as text, and publishing stays with the maintainers.

## Documentation

| File | What it holds |
|---|---|
| [`CONTRIBUTING.md`](CONTRIBUTING.md) | The two contribution modes, step by step, and what CI and review check. |
| [`DEVELOPMENT.md`](DEVELOPMENT.md) | Invariant workflow rules: promotion criterion, proof architecture, verification runners, export discipline. |
| [`CLAUDE.md`](CLAUDE.md), [`SOUL.md`](SOUL.md) | Working rules and standing principles for the AI agents. |
| [`docs/README.md`](docs/README.md) | Map of the documentation. |
| [`docs/current/`](docs/current/README.md) | What holds today: checkpoint, status vocabulary, coverage table, one file per paper, generated facade index and dependency graphs. |
| [`docs/history/`](docs/history/README.md) | What was done: one file per research line, a generated chronological index, and the frozen Stage-79 documents in `archive/`. |
| [`docs/roadmap/`](docs/roadmap/README.md) | What comes next: priorities, the `frontier.toml` queue, and one file per candidate paper. |
