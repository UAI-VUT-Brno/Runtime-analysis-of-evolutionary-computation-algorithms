---
name: review-paper-proposal
description: Review a contributor's mode-1 pull request that proposes a paper for the ECRuntime roadmap - scope, template, verbatim quotes against the paper, duplicates, target entry and feasibility - and draft a review comment for the maintainer's decision. Use when the user invokes /review-paper-proposal, or asks to review a roadmap proposal, a paper proposal, or a mode-1 pull request.
---

# Review a paper proposal (mode 1, review)

Read `CLAUDE.md` and mode 1 in `CONTRIBUTING.md` first; the review checks a contribution
against exactly those rules.

**Input**: the contributor's branch, **already checked out or fetched locally by the
user**. This skill never fetches, pushes or posts (`SOUL.md` §1); if the branch is not
available locally, ask the user to provide it. Determine the change against `main`:

```bash
git diff --name-status main...<branch>
```

**Agents change no files.** They return text — a new file's content or exact edits — and you
apply each change with `Edit` or `Write`; the user approves every change and every
`Bash` or `PowerShell` command (`.claude/settings.json`, `permissions.ask`).

## Checks

**1. Scope.** A mode-1 pull request may change only `docs/roadmap/papers/<key>.md`,
`docs/roadmap/frontier.toml` and the generated `docs/roadmap/papers/README.md`. Any other
file is a finding; a Lean file means the pull request is not mode 1 at all.

**2. Template and key.** Every section of `docs/roadmap/TEMPLATE-paper.md` is filled in; the
key follows the rule; the front matter lists the targets. With the branch checked out:

```bash
pwsh -File scripts/docs_index.ps1 -Check
```

It catches a wrong key, unfilled placeholders, a target pointing elsewhere and duplicate
ids.

**3. Duplicates.** The paper is not already in `docs/roadmap/papers/` or
`docs/current/papers/` under another key, DOI or title.

**4. Quotes.** **Ask the user for the paper's text** in the version the proposal names.
Compare every quoted result with the source: number, hypotheses, quantifiers, constants.
A paraphrase presented as a quote, or a dropped hypothesis, is a finding. Never judge a
quote from memory.

**5. Target entry.** All fields present, `status = "open"`, the id unique, the tier
plausible. A maintainer may renumber or retier on acceptance; note the proposed change.

**6. Fit.** Optionally delegate to `lean-architect` (mode-1 role): is the paper within the
project's scope (runtime analysis of evolutionary algorithms on the library's semantics),
and is **Missing machinery** honest about what the library lacks?

## ▲ Decision — the maintainer's

Lead with a recommendation — **accept**, **request changes**, or **decline** — and the
findings behind it, most serious first. **Stop and wait** for the maintainer's decision.

Then draft, as text for the maintainer to post:

- the review comment, addressed to the contributor, polite and specific;
- on acceptance: any renumbering or tier change the maintainer should make, and the
  contributor's entry for `CONTRIBUTORS.md` (`lean-scribe` drafts it after the merge, and you apply it);
- the commands that bring the merged change into the private repository, for the user to
  run (cherry-pick of the squash-merge commit).

Nothing is posted, merged, pushed or fetched by this skill.
