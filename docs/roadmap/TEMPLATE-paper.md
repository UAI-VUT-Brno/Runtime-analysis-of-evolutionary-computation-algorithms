---
paper: <first-author>-<year>
targets: [<target-id>]
---

<!--
Template for mode 1 (proposing a paper for the roadmap). Copy it to
docs/roadmap/papers/<first-author>-<year>.md, fill in every section, delete this comment,
and add the matching [[target]] entry to docs/roadmap/frontier.toml. Key: all surnames up
to three authors (doerr-janett-lengler-2024), <first>-et-al-<year> from four authors,
umlauts transcribed (Kötzing -> koetzing). See CONTRIBUTING.md, mode 1.
-->

# <Authors> (<year>): <title>

## Paper

<!-- Full citation: authors, title, venue, year. DOI or arXiv id. The version you used
     (journal, conference or arXiv vN); theorem numbers differ between versions. -->

## Results to formalize

<!-- The numbered results this target covers. Quote each statement exactly as the paper
     gives it, with its hypotheses, and say which algorithm, operator, objective and
     initialization it is about. -->

## Already in the library

<!-- What ECRuntime already certifies that this builds on or overlaps with: links to
     docs/current/papers/ files or modules in docs/current/facades.md. "None" is a fine
     answer, but check first. -->

## Missing machinery

<!-- What the library lacks for this target, e.g. a lower-bound drift theorem,
     populations, crossover, plateau semantics. "Unknown" is a fine answer. -->

## Proposed decomposition

<!-- A rough split into stages, each one new Lean module with a coherent group of
     theorems, in dependency order. Optional, but it makes the target easier to accept. -->

## Risks

<!-- Steps that may not survive formalization: conditional-probability arguments
     (DEVELOPMENT.md section 4), informal asymptotics, conventions that differ from
     the library's (iterations versus evaluations, initialization). -->

## Proposed by

<!-- Your name and GitHub handle. -->
