---
name: review-implementation
description: Review a contributor's mode-2 pull request that implements an approved ECRuntime statement in Lean - scope, exact match with the approved statements, validation, adversarial audit, pins, non-vacuity, full gate - then stop at the promotion gate and finalize the documentation, stage number and contributor credit. Use when the user invokes /review-implementation, or asks to review a Lean pull request, an implementation, or a mode-2 contribution.
---

# Review an implementation (mode 2, promotion gate)

Read `CLAUDE.md`, `DEVELOPMENT.md` and mode 2 in `CONTRIBUTING.md` first.

**Input**: the contributor's branch, **checked out locally by the user**, and the approved
Statement proposal (the reply from `/review-statement` with the approved statements, or the
issue text). This skill never fetches, posts, merges or pushes (`SOUL.md` §1).

```bash
git diff --name-status main...<branch>
```

**Agents change no files.** They return text — a new file's content or exact edits — and you
apply each change with `Edit` or `Write`; the user approves every change and every
`Bash` or `PowerShell` command (`.claude/settings.json`, `permissions.ask`).

## Checks

**1. Scope.** A mode-2 pull request may add **one** module `ECRuntime/<Module>.lean`, and
change only: its import line in `ECRuntime.lean`, `ECRuntimeTest/` (pins, axiom tests,
non-vacuity witnesses for the new theorems), the facade registration in
`scripts/audit.lean`, `docs/current/papers/<key>.md`, the paper's line in `docs/history/`,
and the generated indexes. A change to any existing module, to an existing pin, or to an
unrelated file is a finding.

**2. Exact statements.** Every public theorem's elaborated type equals an approved
statement. Compare the `#check @ECRuntime.<thm>` output with the approved Lean block; a
weakened hypothesis, an added one, a changed constant or a renamed theorem is the most
serious finding there is. A theorem nobody approved is not promotable.

**3. Validation.** Run `/lean-validate ECRuntime/<Module>.lean`.

**4. Audit — `lean-auditor`.** All checks, including source fidelity against the quotes in
`docs/roadmap/papers/<key>.md` and the claimed status level.

**5. Pins and non-vacuity.** Regenerate the pins from compiler output and diff them with the
pull request's; a hand-edited pin is a finding. Every new public theorem has a non-vacuity
witness that discharges all hypotheses.

**6. Full gate.** Number the stage one above the last in `docs/history/README.md`, never below
461:

```bash
pwsh -File scripts/verify.ps1 -Stage <N> -Focus ECRuntime.<Module>
```

Every gate must pass; warnings count as failures.

## ▲ PROMOTION GATE — the maintainer's decision

Present the gate table verbatim, the auditor's verdict, what the stage proves, what it
defers, and every finding. Recommend **merge**, **request changes** (list them), or
**close**. **Stop and wait.**

On the decision, draft for the maintainer to post the review comment, addressed to the
contributor. After the maintainer has merged the pull request in the public repository and
the change is in the private repository (cherry-pick commands are prepared for the user to
run), have `lean-scribe` draft, and then apply:

- the history entries in the paper's line: a candidate entry containing
  `Statements approved by <maintainer> on <date>. Statement proposal: <issue reference>.`
  and `Contributed by <name> (@<handle>).`, then the promotion entry;
- the paper's file in `docs/current/papers/`, the target's status in
  `docs/roadmap/frontier.toml`, the checkpoint in `docs/current/README.md` and `README.md`;
- the contributor's line in `CONTRIBUTORS.md`;
- `pwsh -File scripts/facade_index.ps1` and `pwsh -File scripts/docs_index.ps1 -Check`.

Propose a commit message; do not commit unless asked, and never push.
