#!/usr/bin/env python3
"""Collect the exact current state of the ECRuntime repository as JSON.

Everything here is **measured**, not read out of prose. The documentation set
describes the same state in six registers and can drift; this reports what the
compiler, the gates and the source actually say, and flags where the documented
claims disagree with the measurements.

    python3 scripts/state_report.py                 # measure, skip the slow gates
    python3 scripts/state_report.py --run-gates     # also run verify.sh (slower)
    python3 scripts/state_report.py -o state.json

Exit code is always 0 unless collection itself fails: a repository in a bad state
is a finding to report, not an error to raise.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hygiene import DECL, FACADES, ORPHAN_ALLOWLIST, REPO, strip_comments  # noqa: E402

SRC = REPO / "ECRuntime"
TEST = REPO / "ECRuntimeTest"
THEOREM = re.compile(r"^(?:private\s+)?(?:theorem|lemma)\s")


def run(cmd: list[str], timeout: int = 900) -> tuple[int, str]:
    try:
        p = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True,
                           encoding="utf-8", errors="replace", timeout=timeout)
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except (subprocess.TimeoutExpired, FileNotFoundError) as exc:
        return 127, str(exc)


def toolchain() -> dict:
    out: dict = {}
    for key, cmd in (("lean", ["lean", "--version"]), ("lake", ["lake", "--version"])):
        rc, text = run(cmd, timeout=60)
        out[key] = text.strip().splitlines()[0] if rc == 0 and text.strip() else "not found"
    tc = REPO / "lean-toolchain"
    out["pinned"] = tc.read_text(encoding="utf-8").strip() if tc.is_file() else "unknown"
    manifest = REPO / "lake-manifest.json"
    out["mathlib"] = "unknown"
    if manifest.is_file():
        try:
            data = json.loads(manifest.read_text(encoding="utf-8"))
            for pkg in data.get("packages", []):
                if pkg.get("name") == "mathlib":
                    out["mathlib"] = pkg.get("rev", "unknown")[:12] or "unknown"
                    inp = pkg.get("inputRev")
                    if inp:
                        out["mathlib_rev"] = inp
        except (json.JSONDecodeError, AttributeError):
            pass
    return out


def scale() -> dict:
    mods = sorted(SRC.glob("*.lean"))
    tests = sorted(TEST.glob("*.lean")) if TEST.is_dir() else []
    lines = decls = theorems = documented = 0
    for p in mods:
        text = p.read_text(encoding="utf-8")
        body = text.splitlines()
        lines += len(body)
        for i, line in enumerate(body):
            if not DECL.match(line):
                continue
            decls += 1
            if THEOREM.match(line):
                theorems += 1
            j = i - 1
            while j >= 0 and not body[j].strip():
                j -= 1
            prev = body[j].strip() if j >= 0 else ""
            if prev.endswith("-/") or prev.startswith("/--"):
                documented += 1
    return {
        "modules": len(mods),
        "test_modules": len(tests),
        "lines": lines,
        "declarations": decls,
        "theorems": theorems,
        "documented": documented,
        "doc_coverage_pct": round(documented / decls * 100, 1) if decls else 0.0,
    }


def hygiene_state() -> dict:
    rc, out = run([sys.executable, str(REPO / "scripts" / "hygiene.py")], timeout=300)
    errors = [l[len("error: "):] for l in out.splitlines() if l.startswith("error: ")]
    warnings = [l[len("warning: "):] for l in out.splitlines() if l.startswith("warning: ")]
    def count(sub: str) -> int:
        return sum(1 for w in warnings if sub in w)
    return {
        "exit": rc,
        "clean": rc == 0,
        "errors": errors,
        "warning_count": len(warnings),
        "orphans": count("grandfathered orphan"),
        "unused_hypotheses": [w for w in warnings if "bound but unused" in w],
        "undocumented": count("no doc comment"),
    }


def proof_holes() -> dict:
    """Textual scan. The axiom audit in ECRuntimeTest is the authoritative check --
    a `sorry` reachable through a helper does not appear in any file's own text."""
    found: dict[str, list[str]] = {k: [] for k in
                                   ("sorry", "axiom", "native_decide", "unsafe", "maxHeartbeats")}
    pats = {
        "sorry": re.compile(r"\bsorry\b"),
        "axiom": re.compile(r"^\s*axiom\s", re.M),
        "native_decide": re.compile(r"\bnative_decide\b"),
        "unsafe": re.compile(r"^\s*unsafe\s", re.M),
        "maxHeartbeats": re.compile(r"set_option\s+maxHeartbeats"),
    }
    for p in sorted(SRC.glob("*.lean")):
        body = strip_comments(p.read_text(encoding="utf-8"))
        for label, pat in pats.items():
            if pat.search(body):
                found[label].append(p.name)
    return found


def pins() -> dict:
    ax = TEST / "AxiomAudit.lean"
    st = TEST / "StatementPins.lean"
    def n(path: Path, marker: str) -> int:
        return path.read_text(encoding="utf-8").count(marker) if path.is_file() else 0
    return {
        "axiom_pins": n(ax, "#print axioms"),
        "statement_pins": n(st, "#check @"),
        "suite_present": ax.is_file() and st.is_file(),
    }


def frontier() -> dict:
    path = REPO / "docs" / "frontier.toml"
    if not path.is_file():
        return {"present": False}
    text = path.read_text(encoding="utf-8")
    ing = re.findall(r"\[\[ingredient\]\](.*?)(?=\[\[|\Z)", text, re.S)
    tgt = re.findall(r"\[\[target\]\](.*?)(?=\[\[|\Z)", text, re.S)

    def field(block: str, key: str) -> str | None:
        m = re.search(rf'^{key}\s*=\s*"(.*?)"', block, re.M)
        return m.group(1) if m else None

    def status_of(blocks: list[str]) -> dict[str, int]:
        counts: dict[str, int] = {}
        for b in blocks:
            s = field(b, "status") or "unknown"
            counts[s] = counts.get(s, 0) + 1
        return counts

    open_ing = [b for b in ing if field(b, "status") == "open"]
    active = [b for b in tgt if field(b, "status") == "active"]
    return {
        "present": True,
        "checkpoint": field(text, "checkpoint"),
        "active_target": field(text, "active_target"),
        "ingredients": status_of(ing),
        "targets": status_of(tgt),
        "next_open": (field(open_ing[0], "text") if open_ing else None),
        "active_paper": (field(active[0], "paper") if active else None),
        "active_goal": (field(active[0], "goal") if active else None),
    }


def documented_checkpoint() -> dict:
    """What the prose claims, for comparison against what is measured."""
    out: dict[str, str | None] = {}
    dev = REPO / "DEVELOPMENT.md"
    if dev.is_file():
        m = re.search(r"latest promoted checkpoint is \*\*(.*?)\*\*",
                      dev.read_text(encoding="utf-8"), re.I)
        out["development_md"] = m.group(1) if m else None
    rd = REPO / "README.md"
    if rd.is_file():
        # The whole sentence is bold, so the checkpoint is not delimited by `**`:
        # "**Latest compiler-promoted checkpoint: Stage 79 fix 1 (2026-09-25).**"
        m = re.search(r"compiler-promoted checkpoint:\s*(.*?)\s*(?:\(|\.\*\*|\*\*)",
                      rd.read_text(encoding="utf-8"), re.I)
        out["readme"] = m.group(1).strip() if m else None
    return out


def gates(stage: str, focus: str) -> dict:
    rc, out = run(["bash", str(REPO / "scripts" / "verify.sh"),
                   "--stage", stage, "--focus", focus, "--quick"], timeout=1800)
    results = dict(
        re.findall(r"^([a-z_]+)=(\d+)$", out, re.M)
    )
    return {
        "ran": True,
        "exit": rc,
        "promotable": rc == 0,
        "results": {k: int(v) for k, v in results.items()},
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("-o", "--output", help="write JSON here (default: stdout)")
    ap.add_argument("--run-gates", action="store_true",
                    help="also run scripts/verify.sh (slow)")
    ap.add_argument("--stage", default="79")
    ap.add_argument("--focus", default="ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain")
    args = ap.parse_args()

    fr = frontier()
    state = {
        "generated_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "repo": str(REPO),
        "toolchain": toolchain(),
        "scale": scale(),
        "hygiene": hygiene_state(),
        "proof_holes": proof_holes(),
        "pins": pins(),
        "frontier": fr,
        "documented": documented_checkpoint(),
        "facades": FACADES,
        "orphan_allowlist": sorted(ORPHAN_ALLOWLIST),
        "gates": gates(args.stage, args.focus) if args.run_gates else {"ran": False},
    }

    # Divergence between what is measured and what the prose claims.
    diffs: list[str] = []
    doc = state["documented"]
    claims = {v for v in doc.values() if v}
    for source, value in doc.items():
        if value is None:
            diffs.append(f"could not read the claimed checkpoint from {source}")
    if len(claims) > 1:
        diffs.append(f"documentation disagrees on the checkpoint: {sorted(claims)}")
    cp = fr.get("checkpoint")
    if cp and claims:
        norm = {c.lower().replace(" ", "-") for c in claims}
        if cp.lower() not in norm:
            diffs.append(f"frontier.toml says '{cp}' but the prose says {sorted(claims)}")
    holes = {k: v for k, v in state["proof_holes"].items() if v}
    if holes:
        diffs.append(f"proof-hole constructs present in source: {holes}")
    if not state["pins"]["suite_present"]:
        diffs.append("ECRuntimeTest pins are missing: axiom integrity is unverified")
    state["divergence"] = diffs

    text = json.dumps(state, indent=2, ensure_ascii=False)
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
        print(f"wrote {args.output}")
    else:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
