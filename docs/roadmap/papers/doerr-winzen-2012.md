---
paper: doerr-winzen-2012
targets: [C3]
---

# Doerr & Winzen (2012)

> Queue status for C3 is in [`frontier.toml`](../frontier.toml).
> The sections below are the frontier assessment written at the Stage 79 checkpoint (2026-09-25), copied verbatim from the [archived frontier document](../../history/archive/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md).

## C3. Doerr & Winzen (2012): Breaking the `O(n log n)` barrier of LeadingOnes

**Paper:** B. Doerr, C. Winzen, *Black-Box Complexity: Breaking the O(n log n) Barrier of LeadingOnes*, Evolution Artificielle 2011 / LNCS 7401, 205--216 (2012), DOI `10.1007/978-3-642-35533-2_18`; arXiv:1210.6465.

**Result:** `O(n log n / log log n)` unrestricted and 3-ary unbiased black-box complexity for permutation-/XOR-invariant LeadingOnes.

**Why reachable:** the exact LeadingOnes objective and future higher-arity black-box model provide the base. This is more involved than C2 but stays on a benchmark already deeply formalized.
