# Contributing to ECRuntime

ECRuntime publishes **verified claims**: Lean 4 statements about the runtime of
evolutionary algorithms, each checked by the compiler and matched against the paper it
formalizes. A contribution is welcome when it keeps both halves of that promise. A
green build alone is not enough, because `sorry`, a weakened hypothesis or a vacuous
statement can all compile.

## Two ways to contribute

Pull requests are accepted in exactly two modes:

| | Mode 1: propose a paper | Mode 2: implement a paper |
|---|---|---|
| What you add | a paper to the roadmap | Lean modules formalizing results of a roadmap paper |
| Files you touch | `docs/roadmap/papers/<key>.md`, `docs/roadmap/frontier.toml` | one new `ECRuntime/<Module>.lean` and its import in `ECRuntime.lean`, `ECRuntimeTest/*.lean`, the facade registration in `scripts/audit.lean`, the paper's docs |
| Before the pull request | nothing | an approved **Statement proposal** issue |
| A merge means | the paper is accepted onto the roadmap | the theorems are certified and recorded |

A pull request that is neither — a documentation fix, a proof refactor, a rename — is
closed. If you find something wrong, **report it in an issue** instead (see
[Reporting problems](#reporting-problems)); the maintainers fix it.

## Maintainers

The repository is curated. Only the maintainers merge into `main`:

- Jiri Kovar ([@KovarJiri](https://github.com/KovarJiri))
- Jakub Kůdela ([@JakubKudela](https://github.com/JakubKudela))

Everyone else contributes from a fork. Maintainers accept roadmap papers, approve theorem
statements, assign target ids and stage numbers, and alone update the Lean and Mathlib
versions. We review in our own time and cannot promise a response time.

## Before you start

- [`README.md`](README.md) gives the current state, including what is **not** claimed.
- [`docs/README.md`](docs/README.md) maps the documentation: `history/` (what was done),
  `current/` (what holds today) and `roadmap/` (what comes next).
- [`docs/current/README.md`](docs/current/README.md) and
  [`docs/current/papers/`](docs/current/papers/) list, paper by paper, what is certified
  and what is missing.
- [`docs/roadmap/papers/`](docs/roadmap/papers/README.md) lists every paper already on the
  roadmap, with its targets and their status from
  [`docs/roadmap/frontier.toml`](docs/roadmap/frontier.toml).
- [`docs/current/facades.md`](docs/current/facades.md) lists every public result module.
- The "Status vocabulary" section of [`docs/current/README.md`](docs/current/README.md#status-vocabulary)
  defines the status levels used below.
- [`DEVELOPMENT.md`](DEVELOPMENT.md) holds the binding technical rules: the promotion
  criterion, the proof architecture, and section 4's rule that a conditional-probability
  step from the literature may only be encoded once its conditioning measure is
  formalized.

## Mode 1: propose a paper for the roadmap

Use this mode to suggest a paper whose results the project should formalize next.

1. **Check that it is new.** Search [`docs/roadmap/papers/`](docs/roadmap/papers/README.md)
   and [`docs/current/papers/`](docs/current/papers/). If the paper is there, propose an
   additional target in its existing file instead of a new file.
2. **Write the paper file.** Copy
   [`docs/roadmap/TEMPLATE-paper.md`](docs/roadmap/TEMPLATE-paper.md) to
   `docs/roadmap/papers/<key>.md` and fill in every section. The key is all surnames up to
   three authors and `<first>-et-al-<year>` from four authors, e.g.
   `doerr-janett-lengler-2024`, `einarsson-et-al-2019`. Quote the results you propose
   exactly as the paper states them, with their numbers and the version you used.
3. **Add the target** to `docs/roadmap/frontier.toml`:

   ```toml
   [[target]]
   id = "C13"                          # tier letter + next free number; maintainers may renumber
   paper_file = "papers/<key>.md"
   paper = "Authors (year), venue"
   doi = "10.xxxx/..."                 # or: arxiv = "xxxx.xxxxx"
   goal = "the result(s) to formalize, in one line"
   new_framework = "none"              # or what the library lacks
   status = "open"
   ```

   Tiers describe how much new machinery a target needs: **A** continues an existing proof
   chain, **B** extends the LeadingOnes and drift machinery, **C** unary-unbiased, OneMax and
   mutation-distribution results, **D** mutation operators and plateaus, **E** populations
   and crossover.
4. **Run** `pwsh -File scripts/docs_index.ps1 -Check` (it regenerates the roadmap index and
   checks links) and open the pull request, choosing *Mode 1* in the template.

A maintainer may ask for changes, renumber the target or adjust the tier. **Merging the pull
request accepts the paper onto the roadmap**; closing it declines the paper. A roadmap
entry is a plan, not a claim: nothing about the paper is certified until mode 2 delivers it.

## Mode 2: implement a paper

Use this mode to formalize results of a paper that is **already on the roadmap** with a
target whose status is `open` or `active`. If the paper is not on the roadmap, start with
mode 1.

### 1. Propose the statement in an issue

Open a **Statement proposal** issue before writing any proof. A proof only proves the
statement that was written, so the statement is the one thing a human must check. The
issue names the roadmap target and gives:

- the statement in Lean, with every definition it relies on;
- the source: paper, version, and numbered result;
- every place the formalization deviates from the paper's phrasing, and why;
- for each hypothesis, why it is needed;
- a concrete instance that satisfies **all** hypotheses at once, showing that the
  statement is not vacuous.

A maintainer approves the statement by adding the label `statement-approved` and assigns
the issue to you. The approval is permanent record: when your work is merged, the history
entry states who approved the statements, when, and in which issue. An assignment lapses after four weeks without visible progress, so that
two people do not duplicate work.

### 2. Open a pull request

Reference the approved issue and choose *Mode 2* in the template. One pull request adds
**one new module** holding a coherent group of theorems; if your work needs two modules,
it is two pull requests.

- The statements are **exactly** the approved ones. If the proof forces a change, stop and
  say so in the issue; do not adjust the statement yourself.
- Every new declaration has a doc comment. Use Unicode notation (`∀`, `→`, `ℕ`, `ℝ`).
- No hypothesis the proof does not use. `scripts/audit.lean` reports them.
- Every new public theorem has a **statement pin** and an **axiom test**, generated from
  real compiler output and pasted verbatim (see below), and a **non-vacuity witness** in
  `ECRuntimeTest/`.
- A new public result module is registered as a facade in `scripts/audit.lean`, and
  `docs/current/facades.md` is regenerated.
- Draft the documentation: the certified results in `docs/current/papers/<key>.md` (create
  it from the roadmap file's front matter if the paper has no certified results yet) and an
  entry in the paper's research line in `docs/history/`. The maintainer finalizes both.

### 3. Review and merge

CI must pass. A maintainer then reviews what the compiler cannot check: whether the
statement matches the paper, whether the claimed status is justified, and whether the
module fits the architecture. Pull requests are squash-merged. After the merge a maintainer
assigns the stage number (stages on `main` continue from 461) and updates the target's
status in `frontier.toml`.

## Reporting problems

Problems are reported in issues, not fixed in pull requests. Open a **Mismatch or error**
issue when

- a theorem statement does not say what its paper says;
- a claimed status overstates what is proved;
- the documentation is wrong, or the build fails on the pinned toolchain.

Point to the exact declaration or passage and give the evidence. A report that a published
argument does not survive formalization is especially welcome.

## Not accepted in any pull request

- A change to an existing theorem statement.
- Weakening a hypothesis, or narrowing a statement, so that a proof goes through.
- `sorry`, a new `axiom`, `native_decide`, `unsafe`, or any `set_option` (including
  `maxHeartbeats`).
- Hand edits to generated files: statement pins, `docs/current/graphs/*.mmd`,
  `docs/current/facades.md`, `docs/history/README.md`, `docs/roadmap/papers/README.md`.

## Working locally

The toolchain is pinned in `lean-toolchain` (Lean 4.32.1, Mathlib v4.32.1). Install
[elan](https://github.com/leanprover/elan), Lean's version manager: on the first `lake`
command it reads `lean-toolchain` and installs exactly that Lean version, so you never
install Lean by hand. Then:

```bash
lake exe cache get                               # Mathlib build cache
lake env lean ECRuntime/<YourModule>.lean        # fast loop: one file
lake build                                       # library and test suite
lake env lean --run scripts/audit.lean strict    # axioms, docs, unused hypotheses, reachability
```

**Warnings count as failures.** The build must show zero `error:` and zero `warning:`
lines.

Generate pins from compiler output, never by hand:

```bash
printf '%s\n' 'import ECRuntime.<Module>' '#print axioms ECRuntime.<thm>' | lake env lean --stdin
printf '%s\n' 'import ECRuntime.<Module>' '#check @ECRuntime.<thm>' | lake env lean --stdin
```

Wrap each output in `/-- info: … -/` followed by `#guard_msgs in` and the command, as in
the existing files under `ECRuntimeTest/`. Every theorem must depend on exactly
`[propext, Classical.choice, Quot.sound]`. A pin edited by hand to make the build pass
defeats the purpose of the test suite.

Regenerate the generated documentation after registering a public module or editing
`docs/`, and check its links and pins:

```bash
pwsh -File scripts/facade_index.ps1        # docs/current/facades.md
pwsh -File scripts/docs_index.ps1 -Check   # history and roadmap indexes, links, pins
```

`pwsh -File scripts/verify.ps1 -Stage <label>` runs the complete gate (audit, builds,
zero diagnostics, graphs, export) if you have PowerShell 7.

## Honesty rules

These matter more than any single result.

- **Claim only what is proved.** Use the weakest status that is true: certified
  paper-level result, certified supporting chain, or reusable infrastructure. If unsure,
  choose the weaker one and say why.
- **Never reshape a statement until it becomes provable.** If a proof will not close,
  prove a weaker theorem under a **new name** and leave the original target open, or
  report the obstacle in the issue.
- **Finding that a published argument does not survive formalization is a result**, not
  a failure. Report it with the precise step that fails; it has happened here before.
- **Say what you deferred.** A pull request that covers part of a target states which
  part it leaves open.
- Linear-function results assume `NonincreasingLinearWeights`; the reduction from
  arbitrary positive weights is not formalized. Never state a result as holding for all
  linear functions.

## AI-assisted contributions

You may use AI tools. If you do, say so in the pull request and describe how. The
repository ships the Claude Code agents and skills the maintainers use (see
[AI agents and skills](README.md#ai-agents-and-skills)); using them is **at your own risk**,
and they replace none of the human gates. You remain
fully responsible for the contribution, above all for whether each statement matches its
source: a machine-generated statement can be subtly wrong and still look convincing. The
same review applies as to any other contribution.

## License and credit

ECRuntime is licensed under the [Apache License 2.0](LICENSE). By submitting a
contribution you agree that it is licensed under the same terms (section 5 of the
license); no separate agreement is needed.

Merged contributors are listed in [`CONTRIBUTORS.md`](CONTRIBUTORS.md) and credited in
`docs/history/` and the git history; an accepted roadmap paper names its proposer in its
file. Authorship of the citation in [`CITATION.cff`](CITATION.cff) and of papers about the
project is decided by the maintainers for each case.

## Conduct

Be respectful and precise; see [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md). Disagreement
about mathematics is welcome and is settled by statements, proofs and sources.
