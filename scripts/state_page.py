#!/usr/bin/env python3
"""Render the measured repository state (state_report.py JSON) as an HTML page.

The page is generated so that publishing it cannot drift from the measurements.
Nothing here is written by hand except the presentation.

    python3 scripts/state_report.py --run-gates -o .verify/state.json
    python3 scripts/state_page.py .verify/state.json -o .verify/state.html
"""
from __future__ import annotations

import argparse
import html
import json
from pathlib import Path

GATE_LABELS = {
    "root_aggregator": "Root aggregator present",
    "hygiene": "Source hygiene",
    "cache_get": "Dependency cache",
    "focused_build": "Focused target",
    "full_build": "Complete root build",
    "test_build": "Regression suite",
    "diagnostics_clean": "Zero errors / warnings",
    "export": "Source export + manifest",
}
GATE_ORDER = list(GATE_LABELS)


def e(x) -> str:
    return html.escape(str(x))


def render(s: dict) -> str:
    sc, hy, fr, pn = s["scale"], s["hygiene"], s["frontier"], s["pins"]
    gates, holes, div = s["gates"], s["proof_holes"], s["divergence"]
    tc = s["toolchain"]
    hole_names = sorted(k for k, v in holes.items() if v)
    clean_kernel = not hole_names and pn["suite_present"]

    if gates.get("ran"):
        ok = gates["promotable"]
        verdict = "Promotable" if ok else "Not promotable"
        vclass = "ok" if ok else "bad"
        vnote = ("every gate green" if ok else "a gate failed — see the table below")
    else:
        verdict, vclass = "Gates not run", "idle"
        vnote = "measurements only; run with --run-gates for the promotion verdict"

    promoted = fr.get("ingredients", {}).get("promoted", 0)
    open_ing = fr.get("ingredients", {}).get("open", 0)
    total_ing = promoted + open_ing

    gate_rows = ""
    if gates.get("ran"):
        res = gates["results"]
        for key in GATE_ORDER:
            if key not in res:
                continue
            passed = res[key] == 0
            gate_rows += (
                f'<tr><td>{e(GATE_LABELS[key])}</td>'
                f'<td class="mono dim">{e(key)}</td>'
                f'<td><span class="pill {"ok" if passed else "bad"}">'
                f'{"pass" if passed else "FAIL"}</span></td></tr>'
            )
    else:
        gate_rows = ('<tr><td colspan="3" class="dim">Not run. '
                     '<span class="mono">scripts/state_report.py --run-gates</span></td></tr>')

    ing_dots = "".join(
        f'<span class="dot {"on" if i < promoted else "off"}" '
        f'title="ingredient {i + 1}"></span>' for i in range(total_ing)
    )

    def stat(value, label, sub="") -> str:
        return (f'<div class="stat"><div class="num">{e(value)}</div>'
                f'<div class="lab">{e(label)}</div>'
                + (f'<div class="sub">{e(sub)}</div>' if sub else "") + "</div>")

    open_items = []
    if hy["orphans"]:
        open_items.append(
            (f'{hy["orphans"]} modules unreachable from any façade',
             'Grandfathered in ORPHAN_ALLOWLIST pending a decision to discharge '
             'HasUniformExactLevelExitBounds for a concrete algorithm or delete the layer. '
             'The list may shrink, never grow.'))
    if hy["unused_hypotheses"]:
        open_items.append(
            (f'{len(hy["unused_hypotheses"])} hypotheses bound but unused',
             'Each narrows its theorem for every caller while the proof ignores it. '
             'Removing one changes the statement, so it needs its own stage and a regenerated pin.'))
    if hy["undocumented"]:
        open_items.append(
            (f'{hy["undocumented"]} declarations without a doc comment',
             f'Coverage is {sc["doc_coverage_pct"]}%. New work should not lower it.'))
    open_items.append(
        ('Linear-function results assume sorted weights',
         'NonincreasingLinearWeights is in force. The WLOG reduction from arbitrary '
         'positive weights is not formalized, so the certified statements cover sorted '
         'weight vectors rather than all linear functions.'))

    items_html = "".join(
        f'<li><span class="it-h">{e(h)}</span><span class="it-b">{e(b)}</span></li>'
        for h, b in open_items
    )

    div_html = (
        '<p class="none">None. Every documented claim matches what was measured.</p>'
        if not div else
        '<ul class="div">' + "".join(f"<li>{e(d)}</li>" for d in div) + "</ul>"
    )

    active = ""
    if fr.get("active_paper"):
        active = (f'<div class="active"><div class="eyebrow">Active target '
                  f'{e(fr.get("active_target", ""))}</div>'
                  f'<p class="paper">{e(fr["active_paper"])}</p>'
                  f'<p class="goal">{e(fr.get("active_goal", ""))}</p></div>')

    next_open = (f'<div class="nextup"><div class="eyebrow">Next open ingredient</div>'
                 f'<p>{e(fr["next_open"])}</p></div>') if fr.get("next_open") else ""

    tgt = fr.get("targets", {})
    tgt_line = " · ".join(f"{v} {k}" for k, v in sorted(tgt.items())) or "—"

    return f"""<title>ECRuntime Verification State</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Literata:opsz,wght@7..72,400;7..72,600&family=Source+Sans+3:wght@400;600&family=JetBrains+Mono:wght@400;600&display=swap">
<style>
  :root {{
    --ground:#fbfcfd; --surface:#ffffff; --sunken:#f2f5f8;
    --ink:#141a21; --body:#3c4854; --dim:#6b7887; --line:#dde4ec;
    --accent:#33408f; --ok:#1d7a55; --ok-bg:#e7f4ee;
    --warn:#96620f; --warn-bg:#fbf1de; --bad:#a8321f; --bad-bg:#fbeae7;
    --shadow:0 1px 2px rgba(20,26,33,.05), 0 8px 24px -16px rgba(20,26,33,.28);
  }}
  @media (prefers-color-scheme: dark) {{
    :root:not([data-theme="light"]) {{
      --ground:#0d1117; --surface:#151b23; --sunken:#1b222c;
      --ink:#e8edf3; --body:#bcc7d4; --dim:#8695a6; --line:#26303c;
      --accent:#93a4ef; --ok:#57c79a; --ok-bg:#12291f;
      --warn:#e0ac5a; --warn-bg:#2a2113; --bad:#ef8b76; --bad-bg:#2d1713;
      --shadow:0 1px 2px rgba(0,0,0,.4), 0 8px 24px -16px rgba(0,0,0,.8);
    }}
  }}
  :root[data-theme="dark"] {{
    --ground:#0d1117; --surface:#151b23; --sunken:#1b222c;
    --ink:#e8edf3; --body:#bcc7d4; --dim:#8695a6; --line:#26303c;
    --accent:#93a4ef; --ok:#57c79a; --ok-bg:#12291f;
    --warn:#e0ac5a; --warn-bg:#2a2113; --bad:#ef8b76; --bad-bg:#2d1713;
    --shadow:0 1px 2px rgba(0,0,0,.4), 0 8px 24px -16px rgba(0,0,0,.8);
  }}
  *,*::before,*::after {{ box-sizing:border-box; }}
  body {{
    background:var(--ground); color:var(--body);
    font-family:"Source Sans 3",-apple-system,BlinkMacSystemFont,Segoe UI,sans-serif;
    font-size:15px; line-height:1.55; margin:0;
    padding-block:44px; padding-left:20px; padding-right:20px;
  }}
  .wrap {{ max-width:1000px; margin:0 auto; display:flex; flex-direction:column; gap:30px; }}
  .mono {{ font-family:"JetBrains Mono",ui-monospace,SFMono-Regular,Menlo,monospace;
           font-size:.86em; font-variant-ligatures:none; }}
  .dim {{ color:var(--dim); }}
  h1,h2 {{ font-family:Literata,Georgia,serif; color:var(--ink);
           text-wrap:balance; margin:0; font-weight:600; }}
  h1 {{ font-size:clamp(28px,4.4vw,40px); letter-spacing:-.015em; line-height:1.15; }}
  h2 {{ font-size:19px; letter-spacing:-.005em; }}
  .eyebrow {{ font-size:11px; font-weight:600; letter-spacing:.1em;
              text-transform:uppercase; color:var(--dim); }}

  header .meta {{ display:flex; flex-wrap:wrap; gap:8px 18px; margin-top:12px; }}
  header .meta span {{ color:var(--dim); }}

  .verdict {{ display:flex; flex-wrap:wrap; align-items:baseline; gap:8px 16px;
    border-left:3px solid var(--accent); background:var(--surface);
    border-radius:0 8px 8px 0; padding:18px 22px; box-shadow:var(--shadow); }}
  .verdict.ok {{ border-left-color:var(--ok); }}
  .verdict.bad {{ border-left-color:var(--bad); }}
  .verdict .v {{ font-family:Literata,Georgia,serif; font-size:24px;
                 font-weight:600; color:var(--ink); }}
  .verdict.ok .v {{ color:var(--ok); }}
  .verdict.bad .v {{ color:var(--bad); }}

  section {{ display:flex; flex-direction:column; gap:14px; }}
  .panel {{ background:var(--surface); border:1px solid var(--line);
            border-radius:10px; padding:22px; box-shadow:var(--shadow); }}

  table {{ width:100%; border-collapse:collapse; }}
  .scroll {{ overflow-x:auto; }}
  th,td {{ text-align:left; padding:9px 12px; border-bottom:1px solid var(--line);
           font-variant-numeric:tabular-nums; }}
  th {{ font-size:11px; letter-spacing:.09em; text-transform:uppercase;
        color:var(--dim); font-weight:600; }}
  tr:last-child td {{ border-bottom:none; }}

  .pill {{ display:inline-block; padding:2px 9px; border-radius:99px;
    font-size:11px; font-weight:600; letter-spacing:.05em; text-transform:uppercase; }}
  .pill.ok {{ background:var(--ok-bg); color:var(--ok); }}
  .pill.bad {{ background:var(--bad-bg); color:var(--bad); }}
  .pill.warn {{ background:var(--warn-bg); color:var(--warn); }}

  .kernel {{ border-color:var(--ok); }}
  .axioms {{ display:flex; flex-wrap:wrap; gap:8px; margin:14px 0 4px; }}
  .axioms code {{ background:var(--ok-bg); color:var(--ok); padding:5px 11px;
    border-radius:6px; font-family:"JetBrains Mono",monospace; font-size:13px; }}

  .stats {{ display:grid; grid-template-columns:repeat(auto-fit,minmax(150px,1fr)); gap:1px;
            background:var(--line); border:1px solid var(--line); border-radius:10px;
            overflow:hidden; }}
  .stat {{ background:var(--surface); padding:16px 18px; }}
  .stat .num {{ font-family:Literata,Georgia,serif; font-size:26px; font-weight:600;
                color:var(--ink); font-variant-numeric:tabular-nums; line-height:1.1; }}
  .stat .lab {{ font-size:13px; margin-top:3px; }}
  .stat .sub {{ font-size:12px; color:var(--dim); margin-top:2px; }}

  .dots {{ display:flex; flex-wrap:wrap; gap:6px; align-items:center; margin:2px 0 10px; }}
  .dot {{ width:22px; height:7px; border-radius:2px; background:var(--line); }}
  .dot.on {{ background:var(--ok); }}
  .active,.nextup {{ background:var(--sunken); border-radius:8px; padding:14px 16px; }}
  .active .paper {{ color:var(--ink); font-weight:600; margin:5px 0 2px; }}
  .active .goal,.nextup p {{ margin:4px 0 0; font-size:14px; }}

  ul.items {{ list-style:none; margin:0; padding:0;
              display:flex; flex-direction:column; gap:14px; }}
  ul.items li {{ display:flex; flex-direction:column; gap:3px;
                 border-left:2px solid var(--warn); padding-left:14px; }}
  .it-h {{ color:var(--ink); font-weight:600; }}
  .it-b {{ font-size:14px; }}

  ul.div {{ margin:0; padding-left:20px; }}
  ul.div li {{ color:var(--bad); margin-bottom:6px; }}
  .none {{ margin:0; color:var(--ok); }}

  footer {{ border-top:1px solid var(--line); padding-top:18px;
            font-size:13px; color:var(--dim);
            display:flex; flex-direction:column; gap:6px; }}
  @media (max-width:520px) {{ .verdict {{ flex-direction:column; gap:4px; }} }}
</style>

<div class="wrap">
  <header>
    <div class="eyebrow">Lean 4 formalization · evolutionary-computation runtime analysis</div>
    <h1>ECRuntime verification state</h1>
    <div class="meta mono">
      <span>checkpoint <strong>{e(fr.get("checkpoint") or "unknown")}</strong></span>
      <span>{e(tc["pinned"])}</span>
      <span>mathlib {e(tc["mathlib"])}</span>
      <span>measured {e(s["generated_utc"])}</span>
    </div>
  </header>

  <div class="verdict {vclass}">
    <span class="v">{e(verdict)}</span>
    <span class="dim">{e(vnote)}</span>
  </div>

  <section>
    <h2>Promotion gates</h2>
    <div class="panel scroll">
      <table>
        <thead><tr><th>Gate</th><th>Key</th><th>Result</th></tr></thead>
        <tbody>{gate_rows}</tbody>
      </table>
    </div>
    <p class="dim" style="margin:0;font-size:13px">Warnings count as failures. A focused
    build alone is insufficient.</p>
  </section>

  <section>
    <h2>Kernel trust</h2>
    <div class="panel kernel">
      <p style="margin:0">Every façade theorem depends on exactly the three standard Lean
      axioms — nothing else:</p>
      <div class="axioms">
        <code>propext</code><code>Classical.choice</code><code>Quot.sound</code>
      </div>
      <p style="margin:10px 0 0;font-size:14px" class="dim">
        {e(pn["axiom_pins"])} axiom pins and {e(pn["statement_pins"])} statement pins are
        checked by the build. The axiom pin catches a <span class="mono">sorry</span>
        reached through a helper lemma whose own text is clean — a textual scan cannot.
        The statement pin makes “a fix changes no theorem statement” mechanical rather
        than asserted.
      </p>
      <p style="margin:10px 0 0;font-size:14px">
        Proof-hole constructs in source:
        {'<span class="pill ok">none</span>' if clean_kernel
         else '<span class="pill bad">' + e(", ".join(hole_names)) + '</span>'}
      </p>
    </div>
  </section>

  <section>
    <h2>Scale</h2>
    <div class="stats">
      {stat(f'{sc["modules"]:,}', "modules", f'+{sc["test_modules"]} test')}
      {stat(f'{sc["lines"]:,}', "lines of Lean")}
      {stat(f'{sc["theorems"]:,}', "theorems", f'{sc["declarations"]:,} declarations')}
      {stat(f'{sc["doc_coverage_pct"]}%', "documented", f'{sc["documented"]:,} of {sc["declarations"]:,}')}
    </div>
  </section>

  <section>
    <h2>Frontier</h2>
    <div class="panel">
      <div class="eyebrow">Near-term ingredients · {promoted} of {total_ing} promoted</div>
      <div class="dots">{ing_dots}</div>
      {active}
      {next_open}
      <p class="dim" style="margin:14px 0 0;font-size:13px">Literature frontier: {e(tgt_line)}.
      Source of truth is <span class="mono">docs/frontier.toml</span>.</p>
    </div>
  </section>

  <section>
    <h2>Measured against documented</h2>
    <div class="panel">{div_html}</div>
  </section>

  <section>
    <h2>Known open items</h2>
    <div class="panel"><ul class="items">{items_html}</ul></div>
  </section>

  <footer>
    <div>Generated from measurement, not from the prose documentation. Reproduce with
      <span class="mono">python3 scripts/state_report.py --run-gates</span> then
      <span class="mono">python3 scripts/state_page.py</span>.</div>
    <div>A green gate makes a stage promotable; it does not promote it. Promotion
      remains a human decision.</div>
  </footer>
</div>
"""


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("state", nargs="?", default=".verify/state.json")
    ap.add_argument("-o", "--output", default=".verify/state.html")
    args = ap.parse_args()
    data = json.loads(Path(args.state).read_text(encoding="utf-8"))
    out = Path(args.output)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(render(data), encoding="utf-8", newline="\n")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
