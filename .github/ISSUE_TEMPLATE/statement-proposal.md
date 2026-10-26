---
name: Statement proposal
about: Propose the Lean statement of a new theorem, before any proof is written
title: "Statement: "
labels: statement-proposal
---

Step 1 of mode 2 (implementing a roadmap paper, see CONTRIBUTING.md). A proof only proves
the statement that was written, so a maintainer approves the statement first (label
`statement-approved`). Pull requests for unapproved statements are not merged. The paper
must already be on the roadmap; if it is not, propose it first (mode 1).

## Roadmap target

<!-- The target id from docs/roadmap/frontier.toml (status open or active) and the paper
     file in docs/roadmap/papers/. -->

## Source

<!-- Paper (authors, year, venue or arXiv id, version) and the numbered result. -->

## Proposed statement

```lean
-- the full statement, with `sorry` as its proof
```

<!-- List any definition the statement relies on that does not yet exist in the library. -->

## Deviations from the paper

<!-- Every place the formalization differs from the paper's phrasing, and why.
     Write "none" only if there are none. -->

## Hypotheses

<!-- For each hypothesis: why is it needed? Is the paper's version weaker? -->

## Non-vacuity

<!-- A concrete instance satisfying all hypotheses at once. -->

## Status

<!-- certified paper-level result / certified supporting chain / reusable infrastructure -->

## Already in the library?

- [ ] I checked `docs/current/papers/` and `docs/current/facades.md`, and this is not already certified.

## AI assistance

<!-- Did you use AI tools to draft this statement? If so, how? -->
