#!/usr/bin/env python3
"""Validate generated Mermaid graphs.

Written after a shipped graph turned out to be unrenderable: the family
"LeadingOnes" and the module `LeadingOnes.lean` sanitised to the same identifier,
so a subgraph and a node inside it were the same object. Mermaid shares one
identifier space between the two, and nothing in the generator noticed.

Checks:
  * no identifier is declared as both a subgraph and a node;
  * no identifier is declared twice as a node;
  * every edge endpoint is a declared node or subgraph;
  * every `class` target exists;
  * every subgraph is closed.

    python3 scripts/check_mermaid.py docs/graphs/*.mmd

Exit codes: 0 clean, 1 findings, 2 usage.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

NODE = re.compile(r"^\s{2,}([A-Za-z0-9_]+)\s*[\[(\{]")
SUBGRAPH = re.compile(r"^\s*subgraph\s+([A-Za-z0-9_]+)")
END = re.compile(r"^\s*end\s*$")
EDGE = re.compile(r"^\s*([A-Za-z0-9_]+)\s*-[.-]*-+>(?:\|[^|]*\|)?\s*([A-Za-z0-9_]+)")
CLASS = re.compile(r"^\s*class\s+([A-Za-z0-9_,]+)\s+\w+")


def check(path: Path) -> list[str]:
    findings: list[str] = []
    nodes: dict[str, int] = {}
    subgraphs: dict[str, int] = {}
    edges: list[tuple[str, str, int]] = []
    classes: list[tuple[str, int]] = []
    depth = 0

    for lineno, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        if line.lstrip().startswith("%%"):
            continue
        if m := SUBGRAPH.match(line):
            depth += 1
            name = m.group(1)
            if name in subgraphs:
                findings.append(f"{path.name}:{lineno}: subgraph `{name}` declared twice")
            subgraphs[name] = lineno
            continue
        if END.match(line):
            depth -= 1
            if depth < 0:
                findings.append(f"{path.name}:{lineno}: `end` without a matching subgraph")
                depth = 0
            continue
        if m := EDGE.match(line):
            edges.append((m.group(1), m.group(2), lineno))
            continue
        if m := CLASS.match(line):
            classes.append((m.group(1), lineno))
            continue
        if m := NODE.match(line):
            name = m.group(1)
            if name in nodes:
                findings.append(f"{path.name}:{lineno}: node `{name}` declared twice "
                                f"(first at line {nodes[name]})")
            nodes[name] = lineno

    if depth != 0:
        findings.append(f"{path.name}: {depth} subgraph(s) left unclosed")

    for name, lineno in sorted(subgraphs.items()):
        if name in nodes:
            findings.append(
                f"{path.name}:{lineno}: `{name}` is both a subgraph and a node "
                f"(node at line {nodes[name]}) -- Mermaid shares one identifier space, "
                f"so this does not render"
            )

    known = set(nodes) | set(subgraphs)
    for a, b, lineno in edges:
        for endpoint in (a, b):
            if endpoint not in known:
                findings.append(f"{path.name}:{lineno}: edge endpoint `{endpoint}` "
                                f"is never declared")
    for targets, lineno in classes:
        for t in targets.split(","):
            if t and t not in known:
                findings.append(f"{path.name}:{lineno}: class target `{t}` is never declared")

    return findings


def main() -> int:
    paths = [Path(p) for p in sys.argv[1:]]
    if not paths:
        print(__doc__, file=sys.stderr)
        return 2

    total = 0
    for path in paths:
        if not path.is_file():
            print(f"error: no such file: {path}", file=sys.stderr)
            return 2
        findings = check(path)
        total += len(findings)
        for f in findings:
            print(f"error: {f}")
        print(f"  {path.name}: {'OK' if not findings else f'{len(findings)} finding(s)'}")

    print(f"\n{len(paths)} file(s), {total} finding(s) -- {'FAIL' if total else 'OK'}")
    return 1 if total else 0


if __name__ == "__main__":
    raise SystemExit(main())
