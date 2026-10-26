## Mode

<!-- Pull requests are accepted in exactly two modes (CONTRIBUTING.md). Tick one and
     delete the checklist of the other mode. Anything else is reported in an issue. -->

- [ ] **Mode 1** — propose a paper for the roadmap
- [ ] **Mode 2** — implement results of a roadmap paper

## Summary

<!-- Mode 1: which paper, and why it fits the project.
     Mode 2: what the new module proves, mathematically. -->

## Mode 1 checklist

- [ ] The paper is not yet in `docs/roadmap/papers/` or `docs/current/papers/`.
- [ ] `docs/roadmap/papers/<key>.md` follows `docs/roadmap/TEMPLATE-paper.md`, with every
      section filled in and the proposed results quoted exactly, with their numbers.
- [ ] `docs/roadmap/frontier.toml` has a `[[target]]` entry with `paper_file`, `goal`,
      `new_framework` and `status = "open"`.
- [ ] `pwsh -File scripts/docs_index.ps1 -Check` passes.
- [ ] No other files changed.

## Mode 2 checklist

Closes #<!-- the Statement proposal issue labelled statement-approved -->

Roadmap target: <!-- e.g. C11, from docs/roadmap/frontier.toml -->

**Source:** <!-- paper, version and numbered result; any deviation from its phrasing and why -->

**Status claimed:** <!-- certified paper-level result / certified supporting chain /
reusable infrastructure. If unsure, choose the weaker one and explain. -->

**Deliberately deferred:** <!-- what this pull request does not attempt -->

- [ ] The statements are exactly the ones approved in the linked issue.
- [ ] One new module; no existing theorem statement changed.
- [ ] No `sorry`, new `axiom`, `native_decide`, `unsafe` or `set_option`.
- [ ] `lake build` shows zero `error:` and zero `warning:` lines.
- [ ] `lake env lean --run scripts/audit.lean strict` reports no new findings for my declarations.
- [ ] Every new declaration has a doc comment; no unused hypotheses.
- [ ] Statement pins and axiom tests were generated from compiler output and pasted verbatim.
- [ ] A non-vacuity witness discharges all hypotheses of each new public theorem.
- [ ] A new public module is registered as a facade, `docs/current/facades.md` is regenerated,
      and `pwsh -File scripts/docs_index.ps1 -Check` passes.
- [ ] Drafts added to `docs/current/papers/<key>.md` and the paper's line in `docs/history/`.

## AI assistance

<!-- Did you use AI tools? If so, which, and for what (paper summary, statements, proofs,
     documentation)? You remain responsible for every statement matching its source. -->
