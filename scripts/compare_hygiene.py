#!/usr/bin/env python3
"""Compare Lean source-hygiene warnings to the grandfathered public baseline.

The baseline is a multiset, so duplicate warning lines retain their counts.
This is not an assertion that the historic audit is warning-free.
"""
from collections import Counter
from pathlib import Path
import sys
if len(sys.argv) != 3:
    raise SystemExit('Usage: compare_hygiene.py current_hygiene.log baseline.txt')
actual=Counter(line for line in Path(sys.argv[1]).read_text().splitlines()
               if line.startswith('warning:'))
prior=Counter(Path(sys.argv[2]).read_text().splitlines())
extra=actual-prior
print('historical_baseline_warnings=', sum(prior.values()))
print('observed_hygiene_warnings=', sum(actual.values()))
print('new_hygiene_warnings=',sum(extra.values()))
for line,n in sorted(extra.items()):
    print('NEW', n, line)
if extra:
    raise SystemExit(1)
