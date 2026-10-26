---
name: lean-validate
description: Validate a single ECRuntime Lean module - elaboration, axiom integrity, forbidden constructs, unused hypotheses, documentation and reachability - then interpret the findings against the actual proof. Use when the user invokes /lean-validate <file>, passes a .lean file and asks to validate or check it, asks whether a module is clean or promotable, or wants to know if a Lean file is ready.
---

# Validate one Lean module

**Argument**: a path to a `.lean` file. Repo-relative (`ECRuntime/Foo.lean`), absolute, or
just a module name (`Foo`, `ECRuntime.Foo`) — resolve it to a file before starting. If the
argument is missing or matches nothing, say so and list the near misses; do not guess.

## 1. Run the checks

There is no single-module validator. Two commands together cover the ground:

```bash
lake env lean ECRuntime/<Module>.lean           # elaboration: errors AND warnings, ~12s
lake env lean --run scripts/audit.lean strict   # axioms, docs, binders, reachability, ~35s
```

Use `candidate` in place of `strict` when `.candidate-stage` exists at the repository root,
or when the file obviously still contains `sorry`; that run permits `sorryAx`. Otherwise use
the promotion standard. Do not run either twice for the same file.

The first command is per-file. The second reads the whole compiled environment, so it
reports every module at once — filter its output for the one under review. It exits 0 even
with warnings, so read the warnings rather than trusting the exit code. For one theorem's
axioms:

```bash
printf '%s\n' 'import ECRuntime.<Module>' '#print axioms ECRuntime.<thm>' | lake env lean --stdin
```

What they check between them: elaboration (errors **and** warnings — warnings block
promotion); **axiom integrity of every theorem**, which catches `sorryAx` and any
non-standard axiom, `native_decide` included, since it introduces `Lean.ofReduceBool`;
unused binders in signatures; module and declaration doc comments; reachability from the
public facades.

## 2. Interpret — this is the part the tooling cannot do

The checks report *what*. You explain *whether it matters* and *what to do*. Read the
actual code around each finding before commenting on it.

**`sorryAx` findings are the important ones.** A theorem can depend on `sorryAx` with no
`sorry` anywhere in its own text, because a lemma beneath it has one. Grep cannot find
this. When it appears, trace which lemma is responsible and say so by name.

**Elaboration warnings block promotion** (`DEVELOPMENT.md` §2) even though `lake build`
exits 0 on them. Treat them as failures, not style notes.

**Unused hypotheses**: read the proof before repeating the warning. An underscore-prefixed
binder in a *signature* narrows the theorem for every caller while the proof ignores it —
that is worth fixing. Removing one changes the statement, so it needs its own stage and a
regenerated pin, not a quiet edit.

**Reachability**: a module nothing consumes is dead weight under `DEVELOPMENT.md` §6. But
check the intent first — a module written minutes ago for a stage in progress is *expected*
to be unreachable until the stage wires it up. Say which case it is.

**Pin coverage**: a module whose public theorems are unpinned is fine if it is an internal
layer, and a gap if it is a facade. A theorem cited in `docs/current/papers/` must be pinned;
`pwsh -File scripts/docs_index.ps1 -Check` fails otherwise. Say which case applies.

## 3. Report

Lead with the verdict — **promotable**, **promotable after fixes**, or **not promotable** —
then the findings that justify it, most serious first. For each: what is wrong, the concrete
consequence, and the minimal fix.

Then state plainly what the validation does **not** cover, because the gap matters:

- it does not check the statement against the source paper — that is `lean-auditor`;
- it does not check the rest of the repository still builds — that is `scripts/verify.ps1`;
- it does not check `unsafe`, `set_option maxHeartbeats`, statement-pin coverage or ASCII
  vs Unicode notation. `maxHeartbeats` is refused at write time by
  `scripts/hooks/guard_lean_write.ps1`, and the pins are enforced by
  `ECRuntimeTest/StatementPins.lean` under a plain `lake build`;
- it confirms a theorem is *proved*, never that it is the *right* theorem.

A clean module should be reported as clean in one or two lines. Do not manufacture findings
to look thorough, and do not pad a clean result with generic advice.

## Scope

One file. For the whole repository use `lake env lean --run scripts/audit.lean strict`; for
the full promotion gate use `pwsh -File scripts/verify.ps1 -Stage <N> -Focus <module>`. If
the user's file is clean but they are mid-stage, say what the next step is rather than
stopping at the verdict.
