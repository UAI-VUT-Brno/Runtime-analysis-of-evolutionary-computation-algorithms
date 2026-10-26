---
name: review-statement
description: Review a contributor's Statement proposal issue for ECRuntime (collaboration mode 2, step 1) - check the roadmap target, elaborate the proposed Lean statement, check it against the paper, audit every hypothesis and the non-vacuity witness, then stop at the statement gate and draft the reply. Use when the user invokes /review-statement, pastes a Statement proposal issue, or asks whether a proposed theorem statement can be approved.
---

# Review a statement proposal (mode 2, statement gate)

Read `CLAUDE.md`, `DEVELOPMENT.md` §4 and mode 2 in `CONTRIBUTING.md` first.

**Input**: the issue text, **pasted by the user**, and the paper's text in the version the
issue names. This skill never reads or writes GitHub (`SOUL.md` §1). If the paper's text is
not available, ask for it; never judge faithfulness from memory.

A proof only proves the statement that was written. This gate is the one check the
pipeline cannot do for itself, so it is the most careful review in the project.

**Agents change no files.** They return text — a new file's content or exact edits — and you
apply each change with `Edit` or `Write`; the user approves every change and every
`Bash` or `PowerShell` command (`.claude/settings.json`, `permissions.ask`).

## Checks

**1. Target.** The issue names a target in `docs/roadmap/frontier.toml` with status `open` or
`active`, and its paper file exists. The result is not already certified
(`docs/current/papers/<key>.md`, `docs/current/facades.md`). Otherwise the answer is mode 1
first, or "already proved".

**2. Elaboration.** Put the proposed statement, with `sorry` as its proof and the imports it
needs, into a scratch file **outside the repository** and elaborate it:

```bash
lake env lean <scratch>/Proposal.lean
```

A statement that does not elaborate cannot be approved. Report the first error.

**3. Faithfulness.** Compare with the paper's result and with the quote in
`docs/roadmap/papers/<key>.md`: quantifier order, strict versus non-strict inequalities,
uniformity in parameters, the algorithm, operator, objective and initialization. Classify
every divergence as equivalent, deliberate strengthening, deliberate weakening, or
**unnoticed drift**. Delegate to `lean-auditor` (statement faithfulness) for a second
reading.

**4. Hypotheses.** For each: is it needed, and does the paper have it? A hypothesis the
proof will not need narrows the theorem for every caller. Linear-function statements must
assume `NonincreasingLinearWeights` and say so. A conditional-probability step from the
literature is acceptable only once its conditioning measure is formalized
(`DEVELOPMENT.md` §4). Delegate to `lean-architect` (hypothesis audit) where useful.

**5. Non-vacuity.** The issue's witness must satisfy **all** hypotheses at once. Elaborate it
in the scratch file if it can be stated in Lean; otherwise check it by hand and say so.

**6. Size.** The statements fit one new module; more is two pull requests.

## ▲ STATEMENT GATE — the maintainer's decision

Present each statement in Lean, the source result beside it, every divergence with its
classification, the hypothesis audit and the witness. Recommend **approve**, **approve
after changes** (list them exactly), or **reject**. **Stop and wait.** Only a maintainer
approves.

On approval, draft for the maintainer to post:

- the reply, repeating the **approved statements verbatim** in a Lean block, so that the
  pull request can later be compared with them exactly;
- the note to add the label `statement-approved` and assign the contributor.

Record the approval data — approving maintainer, date (`YYYY-MM-DD`), issue reference,
statements — in the reply. `/review-implementation` carries it into the history entry as
`Statements approved by <maintainer> on <date>.` when the work is merged.

Nothing is posted, labelled or assigned by this skill.
