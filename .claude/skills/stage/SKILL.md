---
name: stage
description: Run one ECRuntime formalization stage end to end as a maintainer (collaboration mode 2, author side) - select a roadmap ingredient, draft Lean statements for human approval, discharge the proofs, audit adversarially, synchronise the documentation, and verify. Two human gates - statement approval before proof search, promotion approval before the stage is recorded as promoted. Use when the user invokes /stage, asks to continue the formalization, to start the next stage, or to work on a specific roadmap ingredient or paper.
---

# ECRuntime stage runner

Orchestrates one stage written by a maintainer: mode 2 of `CONTRIBUTING.md` from the author's side. A contributor's implementation goes through `/review-statement` and `/review-implementation` instead; both hold it to the same gates. Read `CLAUDE.md` and `DEVELOPMENT.md` before starting.

**Argument**: a roadmap ingredient number, a frontier target id (`A1`…`D6`), a paper name, or nothing (then propose the next open ingredient from `docs/roadmap/frontier.toml` and confirm before proceeding).

There are **two human gates**. Do not cross either on your own authority.

**Agents change no files.** `lean-architect`, `lean-prover` and `lean-scribe` return their
work as text — a new file's content or exact edits. You apply each change with `Edit` or
`Write`, and the user approves every one; every `Bash` or `PowerShell` command is approved
too (`.claude/settings.json`, `permissions.ask`).

## State

No state files. A run is resumable from what is on disk:

| Signal | Meaning |
|---|---|
| `.candidate-stage` exists | a stage is in progress; `sorry` is permitted |
| new module has `sorry` | statements drafted, proofs not done |
| new module builds clean, marker still present | proofs done, not yet verified |
| marker deleted, `.verify/stage-N/status.txt` all zero | verified, awaiting promotion approval |

On invocation, inspect these first and resume rather than restarting.

## Steps

### 1. Select

Read `docs/roadmap/frontier.toml` and the target's `docs/roadmap/papers/<key>.md`. Pick the open ingredient or the named target; its status must be `open` or `active` (a paper not on the roadmap goes through `/propose-paper` first). Check its `depends_on` are all promoted. A target with status `merged` is already certified by the 547-module merge; for any other target, check `docs/current/papers/` that the part you plan to prove is not already certified. Number the stage one above the last stage in `docs/history/README.md`, and never below 461 (`CLAUDE.md`, stage numbering). State the choice, the paper, and what the stage will close. If the target needs a semantic framework the repository lacks (populations, crossover, query histories, Fourier analysis), say so and propose a nearer target instead.

### 2. Draft statements — `lean-architect`

Delegate to `lean-architect`. It returns the text of the new module, with fully elaborated signatures and `sorry` bodies, plus provenance, dependencies, a deferral list, and the hypothesis audit. Create `.candidate-stage` and write the module.

Confirm the skeleton elaborates:

```bash
lake env lean ECRuntime/<Module>.lean
```

### 3. ▲ STATEMENT GATE — human approval

Present to the user, compactly and in the same order as a contributor's **Statement proposal** issue, so that internal and external work face one gate:

- the roadmap target;
- the source: paper, version, numbered result, and the quote from `docs/roadmap/papers/<key>.md`;
- each statement, in Lean;
- any divergence from the paper's phrasing, with the reason;
- for each hypothesis: why it is needed, and a concrete witness showing the set is satisfiable;
- the claimed status level and what the stage defers.

**Stop here and wait.** This is the one thing the pipeline cannot self-check: a proof only proves the statement that was written. Do not begin proof search without an explicit go-ahead.

On approval, have `lean-scribe` draft the candidate entry in the paper's line in `docs/history/` now, including the line `Statements approved by <maintainer> on <YYYY-MM-DD>.` with the approving maintainer's name as the user gives it. An approval that is not recorded did not happen; `scripts/docs_index.ps1 -Check` rejects a candidate entry from stage 461 on without it.

### 4. Prove — `lean-prover`

Delegate. The prover returns each repair as an exact edit; apply it, let the prover elaborate the file, and repeat. The statements are now frozen: weakening a hypothesis, adding one, or renaming a theorem to something provable is out of bounds — refuse any proposed edit that touches a statement. If a `sorry` resists roughly a dozen genuine attempts, the agent reports the obstacle instead of grinding — surface that to the user rather than retrying indefinitely.

### 5. Audit — `lean-auditor`

Delegate. Read-only. Axiom integrity, statement faithfulness against the paper, vacuity, unused hypotheses, and whether the claimed status level is justified. Act on the findings before continuing; if the auditor says not promotable, go back to step 4 or, if the problem is the statement itself, back to step 3.

### 6. Add pins

Every newly promoted facade theorem needs an axiom pin and a statement pin. **Generate them from real compiler output** — capture and paste verbatim:

```bash
printf '%s\n' 'import ECRuntime.<Module>' '#print axioms ECRuntime.<thm>' | lake env lean --stdin
printf '%s\n' 'import ECRuntime.<Module>' '#check @ECRuntime.<thm>' | lake env lean --stdin
```

Wrap each in `/-- info: … -/` + `#guard_msgs in`. A pin edited by hand to make the build pass defeats the entire mechanism. Facade theorems go into `StatementPins.lean` and `AxiomAudit.lean`; a theorem that `docs/current/papers/` will cite goes into `VerifiedPapersStatementPins.lean` and `VerifiedPapersAxiomAudit.lean`. Add a non-vacuity witness to `ECRuntimeTest/NonVacuity.lean` for every new public theorem.

Register the new module as a facade in `scripts/audit.lean` (`facades`) if it is one, then regenerate `docs/current/facades.md` with `pwsh -File scripts/facade_index.ps1`.

### 7. Document — `lean-scribe`

Delegate. The scribe drafts the edits to the paper's file in `docs/current/papers/` (a new file if this is the paper's first certified result), the target's status in `docs/roadmap/frontier.toml`, the ingredient list in `docs/roadmap/papers/<key>.md` and, if the plan moved, the near-term plan in `docs/roadmap/README.md`. Apply them, then run `pwsh -File scripts/docs_index.ps1 -Check`.

### 8. Verify

Delete `.candidate-stage`, then:

```bash
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<Module>
```

Every gate must pass; warnings count as failures. If a gate fails, this is a **fix round**, not a new stage: find the first genuine diagnostic, make the smallest repair, change nothing unrelated, and record it as `Stage N fix M`. A fix must not change any theorem statement — the pins enforce this.

### 9. ▲ PROMOTION GATE — human approval

Present the gate table verbatim, what is now promoted, what remains open, and the auditor's verdict. **Stop and wait.** Only after approval does `lean-scribe` draft the promotion entry in `docs/history/` and the checkpoint updates in `docs/current/README.md`, `DEVELOPMENT.md` section 1 and the "Verified build" line of `README.md`; apply them.

### 10. Hand over

Propose a commit message. Do not commit unless the user asks, and never push.

## Honesty rules

- Never report a stage complete when a gate failed. Give the gate table as it is.
- Never describe a supporting chain as a certified paper-level result.
- If the statement turns out to be false or unprovable, that is a legitimate outcome worth reporting — the project has already found one published step that does not survive formalization.
- If you deferred part of the intended scope, say so explicitly and why.
