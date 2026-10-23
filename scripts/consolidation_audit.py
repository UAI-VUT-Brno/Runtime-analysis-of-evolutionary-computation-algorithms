#!/usr/bin/env python3
"""Static consolidation sanity check. NOT a substitute for Lean compilation."""
from pathlib import Path
import re, json, hashlib, sys
r=Path(__file__).resolve().parent.parent
errors=[]
public=sorted((r/'ECRuntime').glob('*.lean'))
tests=sorted((r/'ECRuntimeTest').glob('*.lean'))
root=(r/'ECRuntime.lean').read_text(encoding='utf-8')
test_root=(r/'ECRuntimeTest.lean').read_text(encoding='utf-8')

def imports(src):
    return re.findall(r'^import\s+([A-Za-z_][A-Za-z_0-9.]*)\s*$',src,re.M)

def without_comments(src):
    # Intentional coarse scan: compiled-environment audit is authoritative.
    src=re.sub(r'(?s)/-.*?-/', '',src)
    return re.sub(r'(?m)--[^\n]*','',src)

for p in public + tests:
    src=p.read_text(encoding='utf-8')
    for mod in imports(src):
        if mod.startswith(('ECRuntime.','ECRuntimeTest.')):
            if not (r/(mod.replace('.','/')+'.lean')).is_file():
                errors.append(f'{p.relative_to(r)} missing import {mod}')
    if p in public:
        body=without_comments(src)
        if re.search(r'(?m)^\s*(sorry|axiom|opaque|unsafe)\b|\bnative_decide\b|\bsorryAx\b',body):
            errors.append(f'{p.relative_to(r)} forbidden public declaration/proof')

# Confirm all maintained public sources remain import-reachable.
visited=set()
queue=[mod for mod in imports(root) if mod.startswith('ECRuntime.')]
while queue:
    mod=queue.pop()
    if mod in visited: continue
    visited.add(mod)
    path=r/(mod.replace('.','/')+'.lean')
    if not path.is_file():
        errors.append(f'Root missing import {mod}')
        continue
    queue.extend(m for m in imports(path.read_text()) if m.startswith('ECRuntime.'))
# A handful of historically listed orphans have deliberately been preserved.
orphans=[p.stem for p in public if 'ECRuntime.'+p.stem not in visited]
print('public_lean_modules=',len(public))
print('public_reachable_from_root=',len(visited))
print('legacy_unreachable_not_deleted=',','.join(orphans) or '(none)')
for mod in imports(test_root):
    if mod.startswith('ECRuntimeTest.') and not (r/(mod.replace('.','/')+'.lean')).is_file():
        errors.append(f'Test root missing {mod}')
if re.search(r'(?m)^import\s+ECRuntimeTest\.(Round\d+PromotionPins|Stage\d+PromotionPins)',test_root):
    errors.append('Old promotion pins imported in consolidated test root')
if 'candidates/' in root or 'candidates/' in test_root or 'import candidates' in root:
    errors.append('Public root references candidates')

# Frozen theorem interfaces survive promotion and deletion of duplicate
# candidate sources.  For historical keys, the stem after the stage number
# names the promoted ECRuntime module.  Check every future approved-open
# candidate as well, without creating per-round theorem pin snapshots.
registry=json.loads((r/'candidates/APPROVED_STATEMENTS.json').read_text())
header=re.compile(r'(?ms)^theorem\s+([A-Za-z_][A-Za-z_0-9]*)\b(.*?)\s*:= by')
observed_open=set()
count_promoted=0
for key, record in registry.items():
    parts=key.split(':',1)
    if len(parts)!=2:
        errors.append(f'Invalid approved statement key: {key}')
        continue
    filename, decl=parts
    m=re.fullmatch(r'[0-9]+_([A-Za-z_0-9]+)\.lean',filename)
    if m is None:
        errors.append(f'Invalid candidate filename in approved register: {filename}')
        continue
    status=record.get('status')
    if status not in ('approved-open','promoted'):
        errors.append(f'Unrecognized approved statement status {status!r}: {key}')
        continue
    if not re.fullmatch('[0-9a-f]{64}',record.get('sha256','')):
        errors.append(f'Invalid approved statement SHA-256: {key}')
        continue
    candidate=r/'candidates'/filename
    public_module=r/'ECRuntime'/(m.group(1)+'.lean')
    if status=='approved-open':
        observed_open.add(filename)
        paths=[candidate]
        if public_module.exists():  # temporary public promotion trial
            paths.append(public_module)
    else:
        count_promoted+=1
        if candidate.exists():
            errors.append(f'Promoted statement still has duplicate candidate source: {candidate.name}')
        paths=[public_module]
    for p in paths:
        if not p.is_file():
            errors.append(f'Missing source for {key} [{status}]: {p.relative_to(r)}')
            continue
        matches=[h for h in header.finditer(p.read_text(encoding='utf-8'))
                 if h.group(1)==decl]
        if len(matches)!=1:
            errors.append(f'Expected one theorem {decl} in {p.relative_to(r)}, found {len(matches)}')
            continue
        actual=hashlib.sha256(' '.join(matches[0].group(0).split()).encode()).hexdigest()
        if actual!=record['sha256']:
            errors.append(f'Approved theorem header changed in {p.relative_to(r)}: {key}')

active={p.name for p in (r/'candidates').glob('[0-9]*.lean')}
if active!=observed_open:
    errors.append(f'Active candidates {sorted(active)} != approved-open register {sorted(observed_open)}')
if count_promoted>=1 and (r/'.candidate-stage').exists() and not observed_open:
    errors.append('Stale .candidate-stage marker after completing all active candidates')

for must in ['run_verification.sh','docs/CONSOLIDATION.md','docs/RESEARCH.md','docs/OPEN_PROBLEMS.md','docs/VERIFIED_PAPERS.md','scripts/audit.lean',
             'scripts/hygiene_baseline.txt','ECRuntimeTest/AxiomAudit.lean']:
    if not (r/must).exists():errors.append('Missing '+must)
# A source-release checkout must not regress to round-numbered wrappers.
legacy_wrappers=sorted(p.name for p in r.glob('run_stage130_round*.sh'))
if legacy_wrappers:
    errors.append('Historical runners should be retired: '+', '.join(legacy_wrappers))
# Documentation link integrity: the catalogue is a maintained repository interface.
verified_catalogue=(r/'docs/VERIFIED_PAPERS.md').read_text(encoding='utf-8')
for rel in re.findall(r'\]\((\.\./ECRuntime/[^)#]+\.lean)\)',verified_catalogue):
    if not (r/'docs'/rel).resolve().is_file():
        errors.append('Verified-paper catalogue references missing Lean source: '+rel)
print('verified_source_paper_rows=',len(re.findall(r'(?m)^\| P\d{2} \|',verified_catalogue)))
if len(re.findall(r'(?m)^\| P\d{2} \|',verified_catalogue)) < 12:
    errors.append('Verified-paper catalogue incomplete: missing publication rows')
print('test_modules=',len(tests))
print('approved_open_candidate_theorems=',len(observed_open))
print('promoted_frozen_statement_guards=',count_promoted)
if errors:
    for e in errors: print('ERROR:',e)
    sys.exit(1)
print('STATIC AUDIT PASSED; the consolidated repository still requires Lean verification.')
