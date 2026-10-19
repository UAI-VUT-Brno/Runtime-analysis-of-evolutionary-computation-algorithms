#!/usr/bin/env python3
"""Render the ECRuntime proof-dependency network as Mermaid.

Input is the real dependency data produced by `scripts/dep_extract.lean`, which
walks the compiled environment: an edge means a proof or statement *actually
mentions* the target, not merely that its module was imported.

    lake env lean scripts/dep_extract.lean          # refresh .verify/*.tsv first

    python3 scripts/dep_graph.py --level family     # architecture at a glance
    python3 scripts/dep_graph.py --level module     # all modules, transitively reduced
    python3 scripts/dep_graph.py --module WittMutationLogThreeRuntime
    python3 scripts/dep_graph.py --theorem leadingOnesUniformFirstHittingTimeExpectation_eq_formula
    python3 scripts/dep_graph.py --redundant-imports  # imports safe to drop
"""
from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from hygiene import FACADES, IMPORT, ORPHAN_ALLOWLIST, REPO  # noqa: E402

DEPS = REPO / ".verify" / "deps.tsv"
DECLS = REPO / ".verify" / "decls.tsv"

# Lean synthesises equation lemmas, match auxiliaries and recursors alongside the
# declarations actually written in the source. They carry no architectural meaning.
GENERATED = re.compile(
    r"\.(eq_\d+|eq_def|match_\d+|proof_\d+|induct|below|brecOn|ibelow|binductionOn"
    r"|noConfusion\w*|rec|recOn|casesOn|sizeOf_spec|injEq|mk\.injEq)$"
)

# First match wins; order matters.
FAMILIES: list[tuple[str, str]] = [
    (r"^StaticUnaryUnbiased", "Static unary-unbiased"),
    (r"^WittMutation", "Witt scaled rate c/n"),
    (r"^WittStandard", "Witt standard rate 1/n"),
    (r"^LeadingOnes", "LeadingOnes"),
    (r"^(BitString|Objective|Mutation|Transition)$", "Foundations"),
    (r"^(FiniteTrajectory|TransitionKernel|FiniteMarginal|PrefixMarginal|Trajectory"
     r"|UnrestrictedRuntime|HittingTime)", "Trajectory semantics"),
    (r"^(Linear|OneMax|AsymptoticRegime|MutationRate|ExpectedRuntime)", "Objectives & asymptotics"),
    (r"", "Generic runtime theory"),
]

SAFE = re.compile(r"[^A-Za-z0-9_]")


def nid(name: str) -> str:
    return "n_" + SAFE.sub("_", name)


def sgid(name: str) -> str:
    """Subgraph identifiers live in their own namespace.

    Mermaid shares one identifier space between subgraphs and nodes, and family
    names collide with module names: the family "LeadingOnes" and the module
    `LeadingOnes.lean` both sanitise to `n_LeadingOnes`, which makes a subgraph and
    a node inside it the same object and breaks rendering.
    """
    return "sg_" + SAFE.sub("_", name)


def all_modules() -> set[str]:
    """Every module on disk, including ones that declare nothing.

    A pure re-export facade such as `LeadingOnesMainResults` has no constants of its
    own, so it never appears in the extracted declaration table. Deriving the node
    set from that table alone silently drops it -- and a public entry point is
    exactly the node an architecture diagram must show.
    """
    return {p.stem for p in (REPO / "ECRuntime").glob("*.lean")}


def module_imports() -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    for path in sorted((REPO / "ECRuntime").glob("*.lean")):
        out[path.stem] = [
            m.group(1) for line in path.read_text(encoding="utf-8").splitlines()
            if (m := IMPORT.match(line))
        ]
    return out


def load() -> tuple[dict[str, str], dict[str, str], list[tuple[str, str]]]:
    if not DECLS.is_file() or not DEPS.is_file():
        sys.exit("error: run `lake env lean scripts/dep_extract.lean` first")
    decl_module: dict[str, str] = {}
    decl_kind: dict[str, str] = {}
    for line in DECLS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        name, module, kind = line.split("\t")
        if GENERATED.search(name):
            continue
        decl_module[name] = module.removeprefix("ECRuntime.")
        decl_kind[name] = kind
    edges = []
    for line in DEPS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        a, b = line.split("\t")
        if GENERATED.search(a) or GENERATED.search(b):
            continue
        if a in decl_module and b in decl_module:
            edges.append((a, b))
    return decl_module, decl_kind, edges


def module_edges(decl_module, edges) -> set[tuple[str, str]]:
    out = set()
    for a, b in edges:
        ma, mb = decl_module[a], decl_module[b]
        if ma != mb:
            out.add((ma, mb))
    return out


def family_of(module: str) -> str:
    for pat, fam in FAMILIES:
        if re.search(pat, module):
            return fam
    return "Generic runtime theory"


def transitive_reduction(nodes: set[str], edges: set[tuple[str, str]]) -> set[tuple[str, str]]:
    """Drop edges implied by a longer path. Declutters without losing reachability."""
    succ = defaultdict(set)
    for a, b in edges:
        succ[a].add(b)

    def reaches(start: str, goal: str, banned: tuple[str, str]) -> bool:
        stack, seen = [start], {start}
        while stack:
            cur = stack.pop()
            for nxt in succ.get(cur, ()):
                if (cur, nxt) == banned:
                    continue
                if nxt == goal:
                    return True
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append(nxt)
        return False

    return {(a, b) for a, b in edges if not reaches(a, b, (a, b))}


def header(direction: str, title: str) -> list[str]:
    return [f"%% {title}",
            "%% Generated by scripts/dep_graph.py from real proof dependencies.",
            "%% An edge means a proof or statement mentions the target.",
            "",
            f"graph {direction}"]


def styles() -> list[str]:
    return [
        "",
        "  classDef facade stroke-width:3px,stroke:#1d7a55,fill:#e7f4ee,color:#12291f;",
        "  classDef orphan stroke-dasharray:4 3,stroke:#96620f,fill:#fbf1de,color:#2a2113;",
        "  classDef plain fill:#f2f5f8,stroke:#8695a6,color:#141a21;",
    ]


def render_family(decl_module, edges) -> str:
    medges = module_edges(decl_module, edges)
    fam_edges: dict[tuple[str, str], int] = defaultdict(int)
    for ma, mb in medges:
        fa, fb = family_of(ma), family_of(mb)
        if fa != fb:
            fam_edges[(fa, fb)] += 1
    counts = defaultdict(int)
    for m in all_modules():
        counts[family_of(m)] += 1

    out = header("BT", "ECRuntime proof architecture, by family")
    for fam, n in sorted(counts.items()):
        out.append(f'  {nid(fam)}["{fam}<br/><small>{n} modules</small>"]')
    out.append("")
    for (fa, fb), w in sorted(fam_edges.items(), key=lambda kv: -kv[1]):
        out.append(f"  {nid(fa)} -->|{w}| {nid(fb)}")
    out += styles()
    return "\n".join(out)


def render_modules(decl_module, edges, reduce_: bool) -> str:
    nodes = all_modules()
    declaring = set(decl_module.values())
    reexport_only = sorted(nodes - declaring)

    medges = module_edges(decl_module, edges)
    if reduce_:
        medges = transitive_reduction(nodes, medges)

    # A module that declares nothing contributes no proof edges, but its imports
    # *are* its whole content. Draw those dashed so "solid edge = proof dependency"
    # stays true.
    reexport_edges = [(m, d) for m in reexport_only for d in module_imports().get(m, [])
                      if d in nodes]

    by_family: dict[str, list[str]] = defaultdict(list)
    for m in sorted(nodes):
        by_family[family_of(m)].append(m)

    out = header("BT", "ECRuntime module dependencies (transitively reduced)"
                 if reduce_ else "ECRuntime module dependencies")
    out.insert(3, "%% Solid edge: a proof or statement mentions the target.")
    out.insert(4, "%% Dashed edge: re-export only -- the module declares nothing itself.")
    for fam in sorted(by_family):
        out.append(f'  subgraph {sgid(fam)}["{fam}"]')
        for m in by_family[fam]:
            out.append(f'    {nid(m)}["{m}"]')
        out.append("  end")
    out.append("")
    for a, b in sorted(medges):
        out.append(f"  {nid(a)} --> {nid(b)}")
    for a, b in sorted(reexport_edges):
        out.append(f"  {nid(a)} -.-> {nid(b)}")
    out += styles()
    facades = [m for m in nodes if m in FACADES]
    orphans = [m for m in nodes if m in ORPHAN_ALLOWLIST]
    if facades:
        out.append(f"  class {','.join(nid(m) for m in sorted(facades))} facade;")
    if orphans:
        out.append(f"  class {','.join(nid(m) for m in sorted(orphans))} orphan;")
    return "\n".join(out)


def render_module_neighbourhood(decl_module, edges, target: str) -> str:
    medges = module_edges(decl_module, edges)
    ups = sorted({a for a, b in medges if b == target})
    downs = sorted({b for a, b in medges if a == target})
    if not ups and not downs and target not in set(decl_module.values()):
        sys.exit(f"error: no module named {target}")

    out = header("BT", f"{target}: direct proof dependencies")
    out.append(f'  {nid(target)}["{target}"]')
    for m in downs:
        out.append(f'  {nid(m)}["{m}"]')
        out.append(f"  {nid(target)} --> {nid(m)}")
    for m in ups:
        out.append(f'  {nid(m)}["{m}"]')
        out.append(f"  {nid(m)} --> {nid(target)}")
    out += styles()
    out.append(f"  class {nid(target)} facade;")
    return "\n".join(out)


def render_theorem(decl_module, decl_kind, edges, root: str, depth: int) -> str:
    full = root if root.startswith("ECRuntime.") else f"ECRuntime.{root}"
    if full not in decl_module:
        cands = [d for d in decl_module if d.endswith("." + root)]
        if len(cands) != 1:
            sys.exit(f"error: no declaration {full}"
                     + (f"; did you mean {cands[:5]}?" if cands else ""))
        full = cands[0]

    succ = defaultdict(set)
    for a, b in edges:
        succ[a].add(b)

    level = {full: 0}
    order = [full]
    frontier = [full]
    for d in range(1, depth + 1):
        nxt = []
        for cur in frontier:
            for t in sorted(succ.get(cur, ())):
                if t not in level:
                    level[t] = d
                    order.append(t)
                    nxt.append(t)
        frontier = nxt

    out = header("BT", f"{full.removeprefix('ECRuntime.')}: proof dependencies, depth {depth}")
    for name in order:
        short = name.removeprefix("ECRuntime.")
        mod = decl_module[name]
        out.append(f'  {nid(name)}["{short}<br/><small>{mod}</small>"]')
    out.append("")
    for a in order:
        for b in sorted(succ.get(a, ())):
            if b in level:
                out.append(f"  {nid(a)} --> {nid(b)}")
    out += styles()
    out.append(f"  class {nid(full)} facade;")
    return "\n".join(out)


def redundant_imports(decl_module, edges) -> str:
    """Imports that could be dropped without losing any proof dependency.

    An import is NOT redundant merely because nothing in it is mentioned: it may be
    the only *route* to a module that is. `ExpectedRuntimeCorollaries` mentions
    nothing from `LinearRuntime`, yet dropping that import breaks the build, because
    it is how `OneMax` arrives. So an import is removable only when every module this
    one actually depends on is still reachable through the imports that remain.

    Still a candidate list, not a verdict: an import can also carry notation or a
    scoped instance that no proof term mentions. Elaborate before deleting.
    """
    used = module_edges(decl_module, edges)
    imports = module_imports()

    def closure(roots: list[str]) -> set[str]:
        seen: set[str] = set()
        stack = list(roots)
        while stack:
            cur = stack.pop()
            if cur in seen:
                continue
            seen.add(cur)
            stack.extend(imports.get(cur, ()))
        return seen

    lines: list[str] = []
    total = 0
    for stem, declared in imports.items():
        needed = {b for a, b in used if a == stem}
        removable = []
        for cand in declared:
            remaining = [d for d in declared if d != cand]
            if needed <= closure(remaining):
                removable.append(cand)
        total += len(removable)
        if removable:
            lines.append(f"{stem}:  (depends on {len(needed)} module(s))")
            lines += [f"    import ECRuntime.{d}" for d in removable]

    head = (f"{total} import(s) are individually removable: every module the importer "
            f"actually depends on\nstays reachable without them. Candidates, not a "
            f"verdict -- elaborate before deleting.\n")
    return head + "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--level", choices=["family", "module"], default="family")
    ap.add_argument("--module", help="one module's direct neighbourhood")
    ap.add_argument("--theorem", help="one theorem's dependency tree")
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--no-reduce", action="store_true",
                    help="keep edges implied by longer paths")
    ap.add_argument("--redundant-imports", action="store_true",
                    help="imports removable without losing a proof dependency")
    ap.add_argument("-o", "--output", help="write here instead of stdout")
    args = ap.parse_args()

    decl_module, decl_kind, edges = load()

    if args.redundant_imports:
        text = redundant_imports(decl_module, edges)
    elif args.theorem:
        text = render_theorem(decl_module, decl_kind, edges, args.theorem, args.depth)
    elif args.module:
        text = render_module_neighbourhood(decl_module, edges, args.module)
    elif args.level == "family":
        text = render_family(decl_module, edges)
    else:
        text = render_modules(decl_module, edges, not args.no_reduce)

    if args.output:
        Path(args.output).write_text(text + "\n", encoding="utf-8", newline="\n")
        print(f"wrote {args.output}")
    else:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
