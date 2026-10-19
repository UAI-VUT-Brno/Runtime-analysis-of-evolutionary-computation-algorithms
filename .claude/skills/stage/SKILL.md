---
name: stage
description: Run one ECRuntime formalization stage end to end - select a roadmap ingredient, draft Lean statements for human approval, discharge the proofs, audit adversarially, synchronise the documentation, and verify. Two human gates - statement approval before proof search, promotion approval before the stage is recorded as promoted. Use when the user invokes /stage, asks to continue the formalization, to start the next stage, or to work on a specific roadmap ingredient or paper.
---

# ECRuntime stage runner

Orchestrates one stage. Read `CLAUDE.md` and `DEVELOPMENT.md` before starting.

**Argument**: a roadmap ingredient number, a frontier target id (`A1`…`D6`), a paper name, or nothing (then propose the next open ingredient from `docs/frontier.toml` and confirm before proceeding).

There are **two human gates**. Do not cross either on your own authority.

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

Read `docs/frontier.toml`. Pick the open ingredient or the named target. Check its `depends_on` are all promoted. State the choice, the paper, and what the stage will close. If the target needs a semantic framework the repository lacks (populations, crossover, query histories, Fourier analysis), say so and propose a nearer target instead.

### 2. Draft statements — `lean-architect`

Create `.candidate-stage`, then delegate to `lean-architect`. It produces the new module with fully elaborated signatures and `sorry` bodies, plus provenance, dependencies, a deferral list, and the hypothesis audit.

Confirm the skeleton elaborates:

```bash
lake env lean ECRuntime/<Module>.lean
```

### 3. ▲ STATEMENT GATE — human approval

Present to the user, compactly:

- each statement, in Lean;
- the source result it formalizes, and any divergence from the paper's phrasing, with the reason;
- for each hypothesis: why it is needed, and a concrete witness showing the set is satisfiable;
- what the stage defers.

**Stop here and wait.** This is the one thing the pipeline cannot self-check: a proof only proves the statement that was written. Do not begin proof search without an explicit go-ahead.

### 4. Prove — `lean-prover`

Delegate. The statements are now frozen: weakening a hypothesis, adding one, or renaming a theorem to something provable is out of bounds. If a `sorry` resists roughly a dozen genuine attempts, the agent reports the obstacle instead of grinding — surface that to the user rather than retrying indefinitely.

### 5. Audit — `lean-auditor`

Delegate. Read-only. Axiom integrity, statement faithfulness against the paper, vacuity, unused hypotheses, and whether the claimed status level is justified. Act on the findings before continuing; if the auditor says not promotable, go back to step 4 or, if the problem is the statement itself, back to step 3.

### 6. Add pins

Every newly promoted facade theorem needs an axiom pin and a statement pin. **Generate them from real compiler output** — capture and paste verbatim:

```bash
printf '%s\n' 'import ECRuntime.<Module>' '#print axioms ECRuntime.<thm>' | lake env lean --stdin
printf '%s\n' 'import ECRuntime.<Module>' '#check @ECRuntime.<thm>' | lake env lean --stdin
```

Wrap each in `/-- info: … -/` + `#guard_msgs in`. A pin edited by hand to make the build pass defeats the entire mechanism. Add a non-vacuity witness to `ECRuntimeTest/NonVacuity.lean`.

Register the new module as a facade in `scripts/audit.lean` (`facades`) if it is one.

### 7. Document — `lean-scribe`

Delegate. Six documents, six registers. Update `docs/frontier.toml` to mark the ingredient promoted.

### 8. Verify

Delete `.candidate-stage`, then:

```bash
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<Module>
```

Every gate must pass; warnings count as failures. If a gate fails, this is a **fix round**, not a new stage: find the first genuine diagnostic, make the smallest repair, change nothing unrelated, and record it as `Stage N fix M`. A fix must not change any theorem statement — the pins enforce this.

### 9. ▲ PROMOTION GATE — human approval

Present the gate table verbatim, what is now promoted, what remains open, and the auditor's verdict. **Stop and wait.** Only after approval does `lean-scribe` record the stage as promoted and advance the checkpoint in `DEVELOPMENT.md` section 1 and `README.md`.

## Honesty rules

- Never report a stage complete when a gate failed. Give the gate table as it is.
- Never describe a supporting chain as a certified paper-level result.
- If the statement turns out to be false or unprovable, that is a legitimate outcome worth reporting — the project has already found one published step that does not survive formalization.
- If you deferred part of the intended scope, say so explicitly and why.
