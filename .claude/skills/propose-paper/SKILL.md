---
name: propose-paper
description: Add a paper to the ECRuntime roadmap as a maintainer (collaboration mode 1, author side) - check the paper is new, quote its results from text the user supplies, fill docs/roadmap/TEMPLATE-paper.md, assess feasibility, add a frontier.toml target, and stop for the maintainer's acceptance. Use when the user invokes /propose-paper, or asks to add, propose or plan a paper for formalization.
---

# Propose a paper for the roadmap (mode 1, author)

Read `CLAUDE.md` and mode 1 in `CONTRIBUTING.md` first. A contributor proposing a paper
follows exactly the same rules; this skill is the maintainer's way of meeting them.

**Argument**: the paper — title, authors and year, DOI or arXiv id. If it is missing or
ambiguous, ask.

A roadmap entry is a **plan, not a claim**. Nothing here marks anything certified.

**Agents change no files.** They return text — a new file's content or exact edits — and you
apply each change with `Edit` or `Write`; the user approves every change and every
`Bash` or `PowerShell` command (`.claude/settings.json`, `permissions.ask`).

## 1. Key and duplicates

Compute the key: all surnames up to three authors, `<first>-et-al-<year>` from four,
lower case, umlauts transcribed (`doerr-janett-lengler-2024`, `einarsson-et-al-2019`).

Check that the paper is new: `docs/roadmap/papers/<key>.md`, `docs/current/papers/<key>.md`,
and the DOI or title in `docs/roadmap/frontier.toml`. If the paper is already there,
propose a **new target in its existing file** instead of a new file, and say so.

## 2. The paper's text

**Ask the user for the paper** — a local PDF or text file, and which version (journal,
conference, arXiv vN). There is no network access (`SOUL.md` §1), and a result quoted from
memory is not acceptable: everything downstream inherits a misquoted statement. Read the
file the user names; do not fetch anything.

## 3. Write the paper file

`lean-scribe` drafts `docs/roadmap/papers/<key>.md` from `docs/roadmap/TEMPLATE-paper.md`;
you write the file:

- **Paper** — full citation, DOI or arXiv id, the version used.
- **Results to formalize** — each result **quoted verbatim**, with its number and the page
  or section, including every hypothesis and the algorithm, operator, objective and
  initialization it concerns.
- **Proposed by** — the maintainer, by name.

## 4. Assess feasibility — `lean-architect`

Delegate in its mode-1 role. It drafts **Already in the library** (from
`docs/current/papers/` and `docs/current/facades.md`), **Missing machinery**, **Proposed
decomposition** (stages, one module each) and **Risks** (conditional-probability steps under
`DEVELOPMENT.md` §4, conventions that differ from the library's). It writes no Lean.

## 5. Add the target

Add a `[[target]]` to `docs/roadmap/frontier.toml`: `id` = tier letter and the next free
number, `paper_file`, `paper`, `doi` or `arxiv`, `goal`, `new_framework`, `status = "open"`.
Tiers: **A** continues an existing proof chain, **B** extends the LeadingOnes and drift
machinery, **C** unary-unbiased, OneMax and mutation-distribution results, **D** mutation
operators and plateaus, **E** populations and crossover (usually `blocked`). List the id in
the file's front matter `targets`.

```bash
pwsh -File scripts/docs_index.ps1 -Check
```

## 6. ▲ ROADMAP ACCEPTANCE — human decision

Present compactly: the paper and version, the quoted results, the target id and tier, the
missing machinery, the proposed decomposition, the risks, and the duplicate check. **Stop
and wait.** Only the maintainer accepts a paper onto the roadmap.

On acceptance, change `docs/roadmap/README.md` only if the paper changes the priorities or
the near-term plan. Propose a commit message; do not commit unless asked, and never push.

## Rules

- Never set a target to `merged`, `promoted` or `active` here.
- Never paraphrase a result in **Results to formalize**; quote it, or leave it out.
- If the paper needs a framework the library lacks, say so in **Missing machinery** rather
  than making the target look nearer than it is.
