---
name: lean-validate
description: Validate a single ECRuntime Lean module - elaboration, axiom integrity, forbidden constructs, unused hypotheses, documentation, reachability and pin coverage - then interpret the findings against the actual proof. Use when the user invokes /lean-validate <file>, passes a .lean file and asks to validate or check it, asks whether a module is clean or promotable, or wants to know if a Lean file is ready.
---

# Validate one Lean module

**Argument**: a path to a `.lean` file. Repo-relative (`ECRuntime/Foo.lean`), absolute, or
just a module name (`Foo`, `ECRuntime.Foo`) — resolve it to a file before starting. If the
argument is missing or matches nothing, say so and list the near misses; do not guess.

## 1. Run the validator

```bash
python3 scripts/validate_module.py <path>              # promotion standard
python3 scripts/validate_module.py <path> --candidate  # stage in progress: `sorry` allowed
python3 scripts/validate_module.py <path> --skip-elab  # ~25s faster, much weaker
```

Use `--candidate` when `.candidate-stage` exists at the repository root, or when the file
obviously still contains `sorry`. Otherwise use the promotion standard.

It takes roughly 25 s, most of it elaboration. Do not run it twice for the same file.

What it checks: elaboration (errors **and** warnings — warnings block promotion);
`sorry`/`axiom`/`native_decide`/`unsafe`/`maxHeartbeats`; **axiom integrity of every
theorem**; unused hypotheses in signatures; module and declaration doc comments;
reachability from the public facades; statement-pin coverage; ASCII vs Unicode notation.

## 2. Interpret — this is the part the script cannot do

The script reports *what*. You explain *whether it matters* and *what to do*. Read the
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
layer, and a gap if it is a facade. Decide which by whether `README.md` or the docs present
its results as outcomes, and say so.

## 3. Report

Lead with the verdict — **promotable**, **promotable after fixes**, or **not promotable** —
then the findings that justify it, most serious first. For each: what is wrong, the concrete
consequence, and the minimal fix.

Then state plainly what the validation does **not** cover, because the gap matters:

- it does not check the statement against the source paper — that is `lean-auditor`;
- it does not check the rest of the repository still builds — that is `scripts/verify.sh`;
- it confirms a theorem is *proved*, never that it is the *right* theorem.

A clean module should be reported as clean in one or two lines. Do not manufacture findings
to look thorough, and do not pad a clean result with generic advice.

## Scope

One file. For the whole repository use `python3 scripts/hygiene.py`; for the full promotion
gate use `bash scripts/verify.sh --stage <N> --focus <module>`. If the user's file is clean
but they are mid-stage, say what the next step is rather than stopping at the verdict.
