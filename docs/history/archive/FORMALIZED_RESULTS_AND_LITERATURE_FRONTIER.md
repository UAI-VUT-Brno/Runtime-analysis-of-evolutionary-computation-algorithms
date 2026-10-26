# Formalized EC Runtime Results and Literature Frontier

> **Frozen at Stage 79; not extended after the 547-module merge, and archived.** The
> current paper-by-paper coverage is [`docs/current/`](../../current/README.md). Section 1
> (status vocabulary) now lives in
> [`current/README.md`](../../current/README.md#status-vocabulary), and the frontier
> entries of section 6 in [`roadmap/papers/`](../../roadmap/papers/README.md), one file per
> paper. Its theorem catalogue is historical.

**Repository checkpoint:** Stage 79 fix 1, compiler-promoted on 2026-09-25  
**Pinned environment:** Lean 4.32.1 / Mathlib v4.32.1  
**Scope of this document:** machine-checked results already present in `ECRuntime`, their relationship to the research literature, and a literature-derived frontier of next formalization targets that are close to the current proof chain.

## 1. Reading guide and status vocabulary

This document deliberately distinguishes three different relationships between the repository and a paper.

- **Certified paper-level result:** the repository proves the mathematical statement (possibly in an equivalent convention or with a slightly stronger finite-dimensional interface) and the relevant source tree has passed the pinned compiler with no warnings or errors.
- **Certified supporting chain / paper theorem not yet closed:** substantial lemmas from a paper's proof have been formalized, but the repository does **not** claim the paper's headline theorem yet.
- **Reusable infrastructure:** the repository proves a general theorem from the same methodological lineage, but it is not intended as a line-by-line mechanization of a particular paper.

This distinction is especially important for the 2024 static unary-unbiased linear-function paper: the repository has found a conditioning issue in an intermediate displayed step and has therefore built a corrected factorial-moment route instead of certifying the published proof verbatim.

## 2. Current compiler-promoted state

Stage 79 fix 1 is the current promoted checkpoint. The focused build of `ECRuntime.StaticUnaryUnbiasedCorrectedLeftGain` and the complete root build both pass warning/error-free in Lean 4.32.1. The maintained proof graph contains 158 reachable Lean modules. The compiler-promoted verification exported 169 maintained files; this documentation-only repository checkpoint adds the present literature document to the maintained whitelist, bringing the clean source export to 170 files without changing any Lean source.

The major formalization branches are now:

1. finite and infinite stochastic-process semantics and hitting times;
2. generic additive/multiplicative drift, runtime tails, fitness levels, stochastic domination, and geometric waiting-time sums;
3. a completed exact LeadingOnes expectation development;
4. a compiler-promoted Witt-style sharp upper-bound line for the `(1+1)` EA on positive linear functions, including `p=c/n` on the certified finite interval `0<c<=log 3`;
5. a corrected reconstruction of the upper-bound side of static unary-unbiased linear optimization, through exact pair normalization, accepted pivot events, a corrected factorial-moment potential, closed gamma-tail control, and the Stage-79 event-weighted singleton left-gain lower bound.

No Stage-80 theorem is introduced in this checkpoint. The next mathematical boundary remains the event-weighted right-loss unconditioning and per-pivot drift assembly.

## 3. Major machine-checked statements already proved

### 3.1 Stochastic-process and runtime semantics

The repository has a reusable semantics layer for finite-state randomized search processes. Major certified interfaces include:

- normalized transition matrices/kernels and stochastic transitions;
- finite path weights and finite-horizon trajectory measures;
- projective consistency and infinite Markov/Ionescu--Tulcea trajectories;
- identification of finite marginals of the infinite trajectory law;
- first-hitting times and target events;
- `runtimeSup` and bridges between Bellman-style runtime quantities and sample-path first-hitting-time integrals.

These results are repository infrastructure rather than a mechanization of a single EC paper. They are what lets later algorithm-specific proofs move between one-step drift, finite horizons, infinite trajectories, expectations, and tail probabilities without reproving measure-theoretic semantics.

### 3.2 Additive drift

**Relevant literature:**

- Jun He and Xin Yao, *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*, Artificial Intelligence 127(1), 57--85 (2001), DOI `10.1016/S0004-3702(01)00058-3`.
- Jun He and Xin Yao, erratum/corrigendum, Artificial Intelligence 140, 245--248 (2002), DOI `10.1016/S0004-3702(02)00260-6`.
- Timo Kötzing and Martin S. Krejca, *First-hitting times under drift*, Theoretical Computer Science 796, 51--69 (2019), DOI `10.1016/j.tcs.2019.08.021`.

**Repository status:** reusable infrastructure.

`AdditiveDrift.lean` proves a Bellman supersolution, a finite-horizon additive-drift runtime bound, and the corresponding unrestricted `runtimeSup` bound. This is a modern first-hitting-time formulation in the additive-drift lineage rather than an attempt to reproduce every hypothesis/formulation from He--Yao.

Representative theorem names:

- `additiveDrift_superSolution`;
- `additiveDrift_finiteHorizonBound`;
- `additiveDrift_runtimeSup_le`.

### 3.3 Multiplicative drift and multiplicative tails

**Primary source:** Benjamin Doerr, Daniel Johannsen, and Carola Winzen, *Multiplicative Drift Analysis*, Algorithmica 64(4), 673--697 (2012), DOI `10.1007/s00453-012-9622-x`.

**Repository status:** certified reusable theorem family.

`MultiplicativeDrift.lean` implements the logarithmic-potential reduction to additive drift and obtains finite-horizon and unrestricted runtime bounds. `MultiplicativeDriftTail.lean` gives a first-hitting-time tail bound.

Representative theorem names:

- `multiplicativeDriftPotential_hasAdditiveDrift`;
- `multiplicativeDrift_finiteHorizonBound`;
- `multiplicativeDrift_runtimeSup_le`;
- `multiplicativeDriftRuntime_eq_log_ratio`;
- `multiplicativeDrift_firstHittingTime_tailMass_le`.

The repository does not claim that every application in Doerr--Johannsen--Winzen (MST, shortest paths, Euler tours, etc.) has been mechanized; the general drift machinery and the linear-function application chain are the parts currently represented.

### 3.4 Fitness levels, geometric waiting times, and stochastic domination

**Primary modern source for the domination viewpoint:** Benjamin Doerr, *Analyzing Randomized Search Heuristics via Stochastic Domination*, Theoretical Computer Science 773, 115--137 (2019), DOI `10.1016/j.tcs.2018.09.024`.

**Repository status:** certified reusable infrastructure, with many ingredients used by the LeadingOnes and runtime-tail developments.

The repository formalizes:

- stochastic domination as a tail comparison and its transitivity;
- natural-valued tail domination;
- product measures of independent geometric waiting variables;
- exact geometric coordinate tails;
- finite sums of independent geometric variables;
- level-exit domination and coupling/residence interfaces.

Representative modules include `StochasticDomination.lean`, `GeometricSum.lean`, `LevelExitDomination.lean`, `FiniteSumDomination.lean`, and the geometric coupling/tail modules.

This is sufficient infrastructure for the fitness-level theorem in stochastic-domination form, but the full collection of applications in Doerr (2019) is not yet reproduced.

### 3.5 LeadingOnes: exact expected runtime for arbitrary fixed mutation rate

**Primary source:** Süntje Böttcher, Benjamin Doerr, and Frank Neumann, *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*, PPSN XI (2010), pp. 1--10, DOI `10.1007/978-3-642-15844-5_1`.

**Repository status:** certified paper-level result for the fixed-rate exact expectation; the adaptive-rate optimization part of the paper is not yet formalized.

The public facade is `ECRuntime.LeadingOnesMainResults`. For uniformly initialized LeadingOnes and any `0<p<1`, the repository proves

$$
  \mathbb E[T]
  = \frac12\sum_{i=0}^{n-1}\frac{1}{p(1-p)^i}.
$$

This is algebraically equivalent to the Böttcher--Doerr--Neumann closed expression

$$
  \frac{1}{2p^2}\left((1-p)^{1-n}-(1-p)\right).
$$

The exact development is not a shortcut through the final formula: it mechanizes first-entry symmetry, exact entry distributions, occupation/residence identities, renewal, level charges, and the assembly of the first-hitting-time expectation.

Key public theorems include:

- `leadingOnesUniformFirstHittingTimeExpectation_eq_formula`;
- `leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum`;
- `leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula` for `p=c/n`;
- `leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm` for `p=1/n`.

At `p=1/n` and `n>=2`, the formal closed form is

$$
 \frac{n(n-1)}2\left[\left(\frac{n}{n-1}\right)^n-1\right].
$$

**Not yet formalized from this paper:** the proof that the optimal static rate is asymptotically about `1.59/n` with expected runtime about `0.77 n^2`, and the fitness-dependent adaptive rate achieving about `0.68 n^2`.

### 3.6 Linear functions: Witt's sharp standard-rate upper bound

**Primary source:** Carsten Witt, *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*, Combinatorics, Probability and Computing 22(2), 294--318 (2013), DOI `10.1017/S0963548312000600`.

**Repository status:** certified substantial paper-level upper-bound line; the paper's complete arbitrary-mutation-rate lower/upper theory is not yet fully formalized.

For positive nonincreasing linear objective weights, the repository formalizes the Witt-style potential and its C1/C2/C3 drift decomposition. At the standard mutation probability `p=1/n`, it proves an explicit finite upper envelope

$$
  e n\log n + 2en,
$$

and packages this as

$$
  e n\log n + O(n).
$$

It also exposes sample-path expectation and high-probability/tail interfaces.

Representative theorems:

- `wittStandard_runtimeSup_le_log_bound`;
- `wittStandardRuntimeUpperBound_eq_enlogn_add_bigO_n`;
- `wittStandard_runtimeSup_le_asymptotic_upperBound`;
- `wittStandard_firstHittingTime_tailMass_le_geometric`;
- `wittStandard_firstHittingTime_tailMass_le_exp_shifted`.

This matches the sharp leading constant `e` of Witt's theorem on the upper-bound side. The formal branch does **not** yet certify Witt's matching lower bound for all linear functions or the full arbitrary-`p` phase diagram.

### 3.7 Linear functions with `p=c/n`: certified finite interval and sharp leading factor

**Source:** the same Witt (2013) paper, which proves tight bounds for constant `c>0` and identifies the leading factor `e^c/c`.

**Repository status:** certified paper-level upper-bound result on a restricted finite parameter interval.

The repository proves a dimension-uniform C3 certificate on

$$
  0<c\le \log 3,\qquad n\ge4,
$$

then derives finite expectation and tail bounds and the asymptotic leading coefficient

$$
  (nq_n(c))^{-1}\to \frac{e^c}{c},
  \qquad
  q_n(c)=\frac cn\left(1-\frac cn\right)^{n-1}.
$$

It additionally proves that `e^c/c` is minimized at `c=1`.

Representative theorems:

- `wittMutation_runtimeSup_le_logThreeScale_log_bound`;
- `wittMutation_firstHittingTime_tailMass_le_exp_shifted_logThreeScale`;
- `wittMutationExactRateNormalizedRuntimeUpperBound_tendsto_certifiedScale`;
- `wittMutationExactRateRuntimeLeadingFactor_one_le_certifiedScale`.

**Important limitation:** Witt's published theorem applies to every fixed `c>0`; the repository's current finite proof certificate covers only the closed C3 regime ending at `log 3`. Extending the formal proof beyond this interval is therefore a genuine remaining target, not already-proved content.

### 3.8 Static unary-unbiased mutation: operator and exact marginal laws

**Primary source:** Carola Doerr, Duri Andrea Janett, and Johannes Lengler, *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*, Algorithmica 86(10), 3115--3152 (2024), DOI `10.1007/s00453-024-01258-9`.

**Repository status:** certified supporting chain; the paper's headline runtime theorem is **not yet claimed**.

Stages 68--72 establish the reusable operator/probability layer:

- `StaticUnaryUnbiasedMutation n` is a normalized nonnegative law on masks invariant under mask cardinality;
- `radiusMass law k` is the radius distribution;
- `oneBitMass law = p_1`;
- `meanRadius law = chi`;
- `singleZeroFlipWeight law x` aggregates the mass of elementary one-bit improvements;
- the independent-bit `(1+1)` EA embeds as `independentBitLaw`, so this abstraction
  extends the existing mutation semantics rather than forking them;
- a specified singleton mask has exact mass `p_1/n`;
- a specified coordinate flips with exact probability `chi/n`;
- the second factorial moment is `E[K(K-1)]`;
- all distinct coordinate pairs have equal flip mass;
- exact pair normalization gives
  $$
    \Pr(i,j\text{ flip})
      =\frac{\mathbb E[K(K-1)]}{n(n-1)};
  $$
- dividing by a specified-coordinate marginal yields the exact size-biased ratio
  $$
    \Pr(i\text{ flips}\mid j\text{ flips})
      =\frac{\mathbb E[K(K-1)]}{\chi(n-1)}
  $$
  whenever the denominator is positive.

This exact pair law is one of the most reusable results now present in the repository, and it connects directly to later work on mutation-strength distributions and monotone functions.

### 3.9 Audit of the 2024 paper's conditional pair step

The repository does **not** mechanically encode the mean-only conditional inequality displayed in Claim/Lemma 9, equation (27), of the 2024 paper. The formal audit shows that conditioning on one specified coordinate being flipped size-biases the radius distribution. Consequently, averaging `(k-1)/(n-1)` against the original `p_k` is not valid for an arbitrary unary-unbiased radius law.

The exact conditional quantity is governed by `E[K(K-1)]`, not by `chi` alone. A diagnostic distribution already documented in the repository is

$$
 p_1=\tfrac12,\qquad p_n=\frac{1}{2n},\qquad
 p_0=\tfrac12-\frac{1}{2n},
$$

for which `chi=1` but the conditional probability that a second specified coordinate flips, conditioned on the first specified coordinate flipping, is `1/2`; this is larger than `1/(n-1)` for `n>=4`.

Accordingly, the repository proceeds through a corrected factorial-moment coefficient. This is a formalization result in its own right: the current repository **does not certify the published 2024 headline theorem under the paper's stated assumptions**. It certifies the chain below, which is valid under the exact finite mask law.

### 3.10 Accepted-event bridge and concrete pivot events

Stages 73--74 prove the event-level bookkeeping needed for the linear-function proof.

For any finite event `A` that contains the singleton `{i}` and is supported on masks flipping `i`, the repository proves

$$
 \Pr(j\text{ flips}\mid A)
 \le
 \frac{\mathbb E[K(K-1)]}{p_1(n-1)}
$$

for a distinct coordinate `j`, provided `p_1>0`.

`StaticUnaryUnbiasedLinearAcceptedEvents.lean` then instantiates this for the accepted leftmost-error pivot events. In the repository convention, objectives are maximized toward the all-ones string and coordinate `0` is most important. The concrete event layer proves:

- the pivot is a zero bit that flips;
- no more-important zero bit flips;
- the offspring is accepted;
- the singleton pivot mask belongs to the event for positive weights;
- different pivot events are pairwise disjoint;
- the event has positive mass when `p_1>0`;
- the corrected second-coordinate conditional bound above.

### 3.11 Corrected `L/R` loss decomposition

Stage 75 (`StaticUnaryUnbiasedLinearLossDecomposition.lean`) formalizes the left/right coordinate split around an abstract anchor. On each accepted pivot event it proves the exact pointwise decomposition

$$
  \Delta=\Delta_L+\Delta_R.
$$

It defines the finite conditional right-loss proxy and sums the corrected per-coordinate conditional estimate over the whole right region, retaining

$$
  \frac{\mathbb E[K(K-1)]}{p_1(n-1)}
$$

as the exact distributional coefficient.

### 3.12 Corrected potential calibration and suffix-min anchor

Stage 76 (`StaticUnaryUnbiasedCorrectedPotential.lean`) introduces the corrected dimensionless penalty

$$
 \rho
 =\frac{\chi\,\mathbb E[K(K-1)]}
        {(n-1)p_1^2}.
$$

The module proves algebraically that the event-mass/right-loss coefficient equals the singleton rate `(p_1/n)` times `rho`. With slack `alpha>=0`, it defines

$$
  \gamma_i=(1+\alpha\rho)^{n-1-i}
$$

and the clipped objective-dependent coefficient

$$
  g_i=\min_{j\ge i}\gamma_j\frac{w_i}{w_j}.
$$

A concrete minimizing suffix coordinate is retained as `correctedAnchor`. The formalized results include anchor membership/minimality, `1<=g_i<=gamma_i`, nonnegativity of the resulting corrected potential, and exact characterization of the all-ones target.

### 3.13 Anchor envelope and closed gamma tail

Stages 77--78 prove the geometric control of the negative right side.

Stage 77 proves the exact contact formula

$$
  g_i=\gamma_{a(i)}\frac{w_i}{w_{a(i)}}
$$

and, for positive nonincreasing weights,

$$
  \gamma_{a(i)}\le g_i.
$$

It bounds the complete corrected-weight mass in the right region by the strict gamma suffix tail.

Stage 78 then evaluates that tail and proves

$$
  \Gamma_{>k}(\alpha\rho)=\gamma_k-1.
$$

For `alpha>0`, this yields

$$
  \rho\Gamma_{>a(i)}\le \frac{g_i}{\alpha}.
$$

Combining this with the exact Stage-76 calibration gives the drift-ready conditional right-loss scaling

$$
 \frac{\chi}{n}\,\mathrm{RightLossProxy}(A_i)
 \le
 \frac{p_1}{n}\frac{g_i}{\alpha}.
$$

### 3.14 Stage 79: corrected left-gain geometry and singleton contribution

Stage 79 fix 1 (`StaticUnaryUnbiasedCorrectedLeftGain.lean`) is compiler-promoted at this checkpoint.

It proves suffix monotonicity of the potential/objective ratio

$$
 \frac{g_i}{w_i}\le\frac{g_q}{w_q}
 \qquad(i\le q),
$$

and the anchor-side envelope

$$
 \frac{g_j}{w_j}\le\frac{g_i}{w_i}
 \qquad(j\le a(i)).
$$

These inequalities convert objective acceptance into a pointwise nonnegative left contribution:

$$
  \Delta_L(i)\ge0
$$

for every mask in the accepted pivot event. The singleton pivot event contributes exactly `g_i`, hence the event-weighted left contribution obeys

$$
  \boxed{
  \frac{p_1}{n}g_i
  \le
  \sum_{M\in A_i}\Pr(M)\Delta_L(M).
  }
$$

This is the current endpoint of the machine-checked 2024-paper reconstruction.

### 3.15 What is explicitly *not* yet proved

The repository should not currently be cited as proving any of the following:

1. the full Doerr--Janett--Lengler (2024) upper theorem under only the paper's published assumptions;
2. its matching lower bound;
3. the full Witt (2013) arbitrary-mutation-rate upper/lower phase diagram;
4. the full fixed-`c` Witt theorem beyond the repository's finite certificate `c<=log 3`;
5. the optimal static/adaptive LeadingOnes mutation-rate statements of Böttcher--Doerr--Neumann (2010);
6. a unary-unbiased black-box complexity theorem;
7. the monotone-function dichotomy or plateau-runtime results listed later in this document.
8. any linear-function statement for **arbitrary** positive weights. The formalized
   results assume `PositiveLinearWeights` together with `NonincreasingLinearWeights`.
   The WLOG reduction of an arbitrary positive linear function to a sorted one is
   routine on paper but is **not** formalized here, so the certified statements cover
   sorted weight vectors rather than all linear functions.

The immediate mathematical gap in the current chain is much smaller than item 1 as a whole: relate the actual event-weighted right loss to the promoted conditional proxy, combine it with Stage 79's left-gain lower bound, and obtain a corrected per-pivot drift inequality. Only after that should the global multiplicative-drift/runtime theorem be attempted.

## 4. Provenance summary

| Literature source | Headline result relevant here | Repository coverage at Stage 79 fix 1 |
|---|---|---|
| He & Yao (2001), *Artificial Intelligence* | General drift conditions for EA runtime | Reusable additive-drift / hitting-time infrastructure; not a line-by-line mechanization of the whole paper |
| Doerr, Johannsen & Winzen (2012), *Algorithmica* | Multiplicative drift; `O(n log n)` and sharper linear-function analysis | General multiplicative drift and tails formalized; linear application superseded by the sharper Witt branch |
| Böttcher, Doerr & Neumann (2010), PPSN | Exact LeadingOnes runtime for fixed `p`; optimal static/adaptive mutation rates | Exact fixed-`p` expectation fully formalized; optimal-rate/adaptive parts remain open |
| Witt (2013), *CPC* | `e n log n+O(n)` on all linear functions; tight `p=c/n`; arbitrary-`p` bounds | Sharp standard-rate upper line + tails formalized; `p=c/n` upper line formalized on `c<=log 3`; matching lower/full arbitrary-`p` theory remains open |
| Doerr (2019), *TCS* | Runtime stochastic domination, geometric-sum bounds, LeadingOnes side results | Generic domination/geometric-sum infrastructure formalized; paper's complete application suite not yet reproduced |
| Doerr, Janett & Lengler (2024), *Algorithmica* | Tight static unary-unbiased linear runtime | Corrected proof infrastructure through event-weighted left gain formalized; headline theorem not yet certified because the published conditioning step needs repair/extra control |

## 5. Literature-search methodology for the next frontier

The search was refreshed on **2026-09-25**. It combined publisher/index pages (Springer, Cambridge, ScienceDirect, MIT Press, ACM), arXiv records, DBLP-style metadata, author publication pages, and citation/reference chains from the six core sources above.

The search was intentionally biased toward results that can reuse at least one already-promoted component:

- first-hitting-time / drift infrastructure;
- stochastic domination and geometric waiting sums;
- exact LeadingOnes level/occupation structure;
- positive-linear objective and `(1+1)` EA semantics;
- static unary-unbiased mutation masks, `p_1`, `chi`, and factorial moments;
- exact pair-event symmetry and normalization;
- corrected linear-potential/anchor machinery.

Representative queries included:

```text
"tight runtime" static unary unbiased evolutionary algorithms linear functions
"linear functions" (1+1) EA adaptive drift mutation rate
"non-existence" universal drift functions evolutionary algorithms
"fixed budget" (1+1) EA linear functions
"LeadingOnes" optimal fixed adaptive mutation rates
"LeadingOnes" self-adjusting mutation rates success rule
"stochastic domination" evolutionary algorithms runtime
"lower bounds" fitness levels evolutionary algorithms LeadingOnes OneMax
"unbiased black-box" LeadingOnes OneMax
"optimal parameter choices" precise black-box OneMax
"optimal mutation strength distributions" (1+lambda) OneMax
"monotone functions" mutation rate evolutionary algorithm
"factorial moment" fast evolutionary algorithms monotone functions
"plateau" arbitrary unbiased mutation operator runtime
"heavy-tailed mutation" Jump evolutionary algorithm runtime
```

The list below is an engineering assessment of **formalization reachability**, not a claim made by the cited papers themselves.

## 6. Next-paper frontier: at least 20 closely related reachable results

The frontier below contains **35 concrete target-result entries spanning 33 distinct papers**. Two papers (Witt 2013 and Böttcher--Doerr--Neumann 2010) appear twice because they expose two materially different next theorems from the current repository state.

### Tier A -- immediate continuations of the current proof chain

#### A1. Doerr, Janett & Lengler (2024): finish the static unary-unbiased linear theorem

**Paper:** C. Doerr, D. A. Janett, J. Lengler, *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*, Algorithmica 86(10), 3115--3152, DOI `10.1007/s00453-024-01258-9`.

**Paper result:** asymptotically tight `n log n / p_1` runtime under conditions on `p_1` and expected mutation strength `chi`, with distinct upper- and lower-bound arguments.

**Why reachable:** this is the exact chain currently being reconstructed. Operator semantics, exact pair moments, accepted pivot events, `L/R` decomposition, corrected potential, gamma-tail closure, and left gain are already promoted.

**Remaining formal gap:** event-weighted right-loss unconditioning, per-pivot drift, global multiplicative drift, then reassessment of which published hypotheses suffice with the corrected factorial-moment coefficient. The lower bound remains a separate later task.

#### A2. Witt (2013): extend `p=c/n` from `c<=log 3` to all fixed `c>0`

**Paper:** C. Witt, *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*, CPC 22(2), 294--318, DOI `10.1017/S0963548312000600`.

**Target result:** for every fixed `c>0`, the `(1+1)` EA with `p=c/n` has the sharp leading runtime factor `e^c/c` on arbitrary positive linear functions.

**Why reachable:** the potential, exact singleton rate, asymptotics, tails, and finite C2/C3 decomposition are already present. The remaining obstacle is the finite drift certificate outside the current C3 interval, not basic semantics.

#### A3. Witt (2013): matching lower bound / optimality of `c=1`

**Target result:** formalize the lower side that makes `(e^c/c)n log n` tight and proves the standard mutation scale optimal among fixed `c/n` choices.

**Why reachable:** the repository already proves the exact leading-factor minimization `e^c/c >= e`; what is missing is a process-level lower-bound theorem strong enough to attach this constant to runtime.

#### A4. Doerr & Goldberg (2013): Adaptive Drift Analysis

**Paper:** B. Doerr, L. A. Goldberg, *Adaptive Drift Analysis*, Algorithmica 65(1), 224--250 (2013), DOI `10.1007/s00453-011-9585-3`; arXiv:1108.0295.

**Result:** for every constant `c>0`, the `(1+1)` EA with mutation rate `c/n` optimizes every linear objective in `Theta(n log n)`, using objective-dependent drift functions.

**Why reachable:** the current repository already supports objective-dependent linear potentials and arbitrary fixed `c/n`; this is a natural bridge beyond the frozen Witt C3 regime even before obtaining Witt's sharp constant everywhere.

#### A5. Doerr, Johannsen & Winzen (2010): Non-Existence of Linear Universal Drift Functions

**Paper:** B. Doerr, D. Johannsen, C. Winzen, *Non-Existence of Linear Universal Drift Functions*, arXiv:1011.3466.

**Result:** universal linear drift functions cease to exist once the mutation probability moves sufficiently far from the standard scale.

**Why reachable:** the repository now has explicit objective-dependent and objective-independent linear potential interfaces and can state the universal-drift property cleanly. This would complement the positive Witt results with a structural impossibility theorem.

#### A6. Jägersküpper (2008): A Blend of Markov-Chain and Drift Analysis

**Paper:** J. Jägersküpper, *A Blend of Markov-Chain and Drift Analysis*, PPSN X, LNCS 5199, 41--51, DOI `10.1007/978-3-540-87700-4_5`.

**Result:** linear-function runtime analysis via a combination of coordinate-ordering/Markov-chain structure and drift.

**Why reachable:** Markov trajectories, linear objectives, coordinate marginals, and drift are already core repository abstractions. This is a short historical bridge that can also expose reusable monotonicity lemmas for later lower bounds.

#### A7. Lengler & Spooner (2015): Fixed-Budget Performance on Linear Functions

**Paper:** J. Lengler, N. Spooner, *Fixed Budget Performance of the (1+1) EA on Linear Functions*, FOGA XIII, 52--61, DOI `10.1145/2725494.2725506`.

**Result:** a priori and a posteriori fixed-budget guarantees for general linear functions, with especially precise OneMax statements.

**Why reachable:** the repository already has finite-horizon trajectories and drift. The main new interface is to state expected potential/fitness after a fixed number of steps rather than first-hitting time.

#### A8. Einarsson et al. (2019): Linear Hidden Subset with scheduled/adaptive mutation rates

**Paper:** H. Einarsson, M. M. Gauy, J. Lengler, F. Meier, A. Mujika, A. Steger, F. Weissenberger, *The Linear Hidden Subset Problem for the (1+1) EA with Scheduled and Adaptive Mutation Rates*, TCS 785, 150--170, DOI `10.1016/j.tcs.2019.05.021`.

**Result:** optimal scheduled runtime with constant `beta≈3.552` and adaptive runtime `(1+o(1)) e n log n` when the number of relevant bits is unknown.

**Why reachable:** current linear-function semantics and `p=c/n` asymptotics can be reused. The substantial new component is a time/history-dependent mutation schedule.

### Tier B -- close extensions of existing LeadingOnes / drift machinery

#### B1. Böttcher, Doerr & Neumann (2010): optimal static mutation rate on LeadingOnes

**Target result from the already-partially-formalized paper:** optimize the exact fixed-`p` expression and prove `p≈1.59/n` with expected runtime about `0.77n^2`.

**Why reachable:** the exact finite expectation is already fully formalized. This is now primarily real asymptotic/optimization analysis, not stochastic-process work.

#### B2. Böttcher, Doerr & Neumann (2010): fitness-dependent adaptive LeadingOnes rate

**Target result:** formalize the exact adaptive-rate expression and the asymptotic `≈0.68n^2` optimum.

**Why reachable:** the difficult exact LeadingOnes entry/residence structure is already present. A state-dependent mutation kernel is the main additional semantic layer.

#### B3. Doerr, Doerr & Lengler (2019): Self-Adjusting Mutation Rates with Provably Optimal Success Rules

**Paper:** B. Doerr, C. Doerr, J. Lengler, *Self-Adjusting Mutation Rates with Provably Optimal Success Rules*, GECCO 2019, DOI `10.1145/3321707.3321733`; arXiv:1902.02588.

**Result:** on LeadingOnes, small update strength and success rate `1/e` achieve asymptotically the same runtime as the best fitness-dependent rate.

**Why reachable:** builds directly on the same LeadingOnes level structure; the new work is a dynamic rate state and success-rule update process.

#### B4. Doerr (2019): fastest unary-unbiased LeadingOnes algorithms

**Paper:** *Analyzing Randomized Search Heuristics via Stochastic Domination*, TCS 773, 115--137, DOI `10.1016/j.tcs.2018.09.024`.

**Target result:** the paper identifies fastest unbiased `(1+1)` algorithms for LeadingOnes, both general and static.

**Why reachable:** the repository has both the exact LeadingOnes chain and a static unary-unbiased mutation law. This is one of the strongest intersections of two already-developed branches.

#### B5. Kötzing & Witt (2020): Improved Fixed-Budget Results via Drift Analysis

**Paper:** T. Kötzing, C. Witt, *Improved Fixed-Budget Results via Drift Analysis*, PPSN XVI, 648--660 (2020), DOI `10.1007/978-3-030-58115-2_45`; arXiv:2006.07019.

**Result:** general fixed-budget drift tools and more precise LeadingOnes fixed-budget results.

**Why reachable:** finite-horizon path measures and LeadingOnes exact dynamics already exist; the missing generic theorem is a fixed-budget drift interface.

#### B6. Lehre & Witt (2013/2014): General Drift Analysis with Tail Bounds

**Paper:** P. K. Lehre, C. Witt, *General Drift Analysis with Tail Bounds*, arXiv:1307.2559.

**Result:** a general variable-drift theorem with upper/lower runtime tails, applied to OneMax, general linear functions, and LeadingOnes.

**Why reachable:** additive/multiplicative drift and several specialized tail bounds are already formalized. A general variable-drift-with-tails theorem would unify multiple existing modules and unlock several later papers.

#### B7. Kötzing & Krejca (2019): First-hitting times under drift

**Paper:** T. Kötzing, M. S. Krejca, *First-hitting times under drift*, TCS 796, 51--69, DOI `10.1016/j.tcs.2019.08.021`.

**Result:** highly general additive, multiplicative, and variable drift theorems with weakened state-space restrictions, plus lower-bound variants under step control.

**Why reachable:** the repository's semantics are already measure-theoretic and unrestricted enough to support these statements. This is a natural way to strengthen the generic theorem library before more lower-bound applications.

#### B8. Sudholt (2013): A New Method for Lower Bounds on the Running Time of Evolutionary Algorithms

**Paper:** D. Sudholt, IEEE Transactions on Evolutionary Computation 17(3), 418--435, DOI `10.1109/TEVC.2012.2202241`.

**Result:** fitness-level lower-bound method with near-exact results for LeadingOnes, OneMax, long paths, and unique-optimum functions, including mutation-rate dependence.

**Why reachable:** the repository already contains a rich fitness-level/geometric domination stack. Formalizing the lower-bound counterpart would immediately support the missing lower side of several already-formalized upper theorems.

#### B9. Doerr & Kötzing (2024): Lower Bounds from Fitness Levels Made Easy

**Paper:** B. Doerr, T. Kötzing, *Lower Bounds from Fitness Levels Made Easy*, Algorithmica 86, 367--395 (2024), DOI `10.1007/s00453-022-00952-w`; conference version GECCO 2021, DOI `10.1145/3449639.3459352`; arXiv:2104.03372.

**Result:** upper/lower fitness-level methods based on level-leaving and visitation probabilities; applications include the exact LeadingOnes runtime and a near-tight OneMax lower bound.

**Why reachable:** level visitation, first entry, and exact LeadingOnes occupation probabilities are already first-class objects in the repository. This may be easier to mechanize than Sudholt's viscosity-parameter method and could become the preferred lower-bound interface.

### Tier C -- unary-unbiased / OneMax / mutation-distribution results

#### C1. Lehre & Witt (2012): Black-Box Search by Unbiased Variation

**Paper:** P. K. Lehre, C. Witt, Algorithmica 64(4), 623--642, DOI `10.1007/s00453-012-9616-8`.

**Result:** formal unbiased black-box model and `Omega(n log n)` lower bounds for unique-optimum function classes, plus matching examples.

**Why reachable:** `StaticUnaryUnbiasedMutation` already captures the unary operator symmetry on bit strings. The missing layer is an algorithm/query-history black-box model rather than mutation mathematics.

#### C2. Doerr et al. (2011): Faster Black-Box Algorithms Through Higher Arity Operators

**Paper:** B. Doerr, D. Johannsen, T. Kötzing, P. K. Lehre, M. Wagner, C. Winzen, FOGA 2011, 163--172, DOI `10.1145/1967654.1967669`.

**Result:** binary unbiased operators reduce LeadingOnes complexity to `O(n log n)` and OneMax to `O(n)`; higher arity further improves OneMax.

**Why reachable:** it is a natural extension after formalizing the unary black-box model. The current bit-string/permutation symmetry infrastructure should transfer, but higher-arity operator invariance is genuinely new.

#### C3. Doerr & Winzen (2012): Breaking the `O(n log n)` barrier of LeadingOnes

**Paper:** B. Doerr, C. Winzen, *Black-Box Complexity: Breaking the O(n log n) Barrier of LeadingOnes*, Evolution Artificielle 2011 / LNCS 7401, 205--216 (2012), DOI `10.1007/978-3-642-35533-2_18`; arXiv:1210.6465.

**Result:** `O(n log n / log log n)` unrestricted and 3-ary unbiased black-box complexity for permutation-/XOR-invariant LeadingOnes.

**Why reachable:** the exact LeadingOnes objective and future higher-arity black-box model provide the base. This is more involved than C2 but stays on a benchmark already deeply formalized.

#### C4. Doerr & Lengler (2016): `(1+1)` elitist black-box complexity of LeadingOnes

**Paper:** C. Doerr, J. Lengler, GECCO 2016, 1131--1138, DOI `10.1145/2908812.2908922`.

**Result:** `Omega(n^2)` `(1+1)` elitist black-box complexity for LeadingOnes, matched by `(1+1)`-type EAs.

**Why reachable:** unlike unrestricted higher-arity results, this stays close to the repository's existing elitist transition semantics. The main missing tool is information-theoretic adversarial reasoning over a function class.

#### C5. Doerr, Doerr & Yang (2020): Optimal Parameter Choices via Precise Black-Box Analysis

**Paper:** B. Doerr, C. Doerr, J. Yang, TCS 801, 1--34, DOI `10.1016/j.tcs.2019.06.014`.

**Result:** precise unary-unbiased black-box complexity of OneMax and a fitness-dependent mutation-strength algorithm that is asymptotically optimal up to lower-order terms.

**Why reachable:** exact static unary-unbiased mask semantics are already available. The missing components are OneMax-specific exact drift optimization and black-box lower bounds.

#### C6. Buskulic & Doerr (2021): Maximizing Drift Is Not Optimal for Solving OneMax

**Paper:** N. Buskulic, C. Doerr, Evolutionary Computation 29(4), 521--541, DOI `10.1162/evco_a_00290`.

**Result:** runtime-optimal mutation strengths differ from drift-maximizing strengths on many OneMax fitness levels; similar phenomena hold for standard and resampling `(1+1)` EAs.

**Why reachable:** after C5's exact OneMax drift/dynamic-programming layer, this is a closely adjacent separation theorem rather than a new algorithm family.

#### C7. Gießen & Witt (2018): optimal mutation rates for `(1+lambda)` EA on OneMax

**Paper:** C. Gießen, C. Witt, Algorithmica 80(5), 1710--1731, DOI `10.1007/s00453-017-0360-y`.

**Result:** asymptotically tight drift analysis for constant offspring population and exact/near-exact optimal mutation rates.

**Why reachable:** requires population/offspring semantics and variable drift, but the single-offspring OneMax/linear infrastructure transfers directly.

#### C8. Buzdalov & Doerr (2020): Optimal Mutation Rates for the `(1+lambda)` EA on OneMax

**Paper:** M. Buzdalov, C. Doerr, PPSN XVI (2020), pp. 574--587, DOI `10.1007/978-3-030-58115-2_40`.

**Result:** computational/dynamic-programming characterization of runtime-optimal mutation rates for `(1+lambda)` variants.

**Why reachable:** naturally follows C7; finite-state dynamic programming can reuse the repository's Bellman/runtime infrastructure.

#### C9. Buzdalov & Doerr (2021): Optimal Static Mutation Strength Distributions for `(1+lambda)` EA on OneMax

**Paper:** M. Buzdalov, C. Doerr, *Optimal Static Mutation Strength Distributions for the (1+lambda) Evolutionary Algorithm on OneMax*, GECCO 2021, 660--668, DOI `10.1145/3449639.3459389`; arXiv:2102.04944.

**Result:** computes optimal *static distributions* over mutation strengths and shows that these distributions can be structurally nontrivial.

**Why reachable:** the repository already represents an arbitrary static unary-unbiased radius distribution. Extending from one offspring to `lambda` offspring would make this an unusually natural target.

#### C10. Doerr, Gießen, Witt & Yang (2017/2018): self-adjusting mutation rate for `(1+lambda)` EA

**Paper:** B. Doerr, C. Gießen, C. Witt, J. Yang, *The (1+lambda) Evolutionary Algorithm with Self-Adjusting Mutation Rate*, GECCO 2017, DOI `10.1145/3071178.3071279`.

**Result:** expected optimization time `O(n lambda/log lambda + n log n)` on OneMax, asymptotically optimal in the relevant parallel unbiased model.

**Why reachable:** a strong later target after population semantics and the exact `(1+lambda)` OneMax branch are available.

#### C11. Lengler (2018/2020): A General Dichotomy of Evolutionary Algorithms on Monotone Functions

**Paper:** J. Lengler, *A General Dichotomy of Evolutionary Algorithms on Monotone Functions*, IEEE Transactions on Evolutionary Computation 24(6), 995--1009 (2020), DOI `10.1109/TEVC.2019.2917014`; arXiv:1803.09227.

**Result:** a broad efficient/inefficient dichotomy for monotone functions. For fast mutation algorithms, the key parameter is the ratio `m_2/m_1` of the second and first falling moments of the mutation strength.

**Why reachable:** this is exceptionally close to the new repository interface: `meanRadius` is `m_1`, while `secondFactorialRadiusMoment` is exactly `m_2`. The pair-normalization work from Stages 70--72 therefore supplies the central mutation-distribution statistics already.

#### C12. Doerr, Jansen, Sudholt, Winzen & Zarges (2013): Mutation Rate Matters Even When Optimizing Monotonic Functions

**Paper:** Evolutionary Computation 21(1), 1--27, DOI `10.1162/EVCO_a_00055`.

**Result:** every strictly monotone function is optimized in `Theta(n log n)` for `c<1`, while sufficiently large constant mutation factors yield exponential runtime on some monotone functions.

**Why reachable:** the positive-linear branch is already a subclass of monotone functions, and the repository has fixed-`c/n` mutation semantics and drift. The difficult new object is the adversarial monotone-function construction for the lower/negative result.

### Tier D -- mutation-operator and plateau results enabled by the radius-law abstraction

#### D1. Antipov & Doerr (2021): Precise Runtime Analysis for Plateau Functions

**Paper:** D. Antipov, B. Doerr, ACM TELO 1(4), Article 13, DOI `10.1145/3469800`.

**Result:** for constant plateau width and an arbitrary unbiased mutation operator, the runtime distribution is close to geometric and is controlled primarily by the probability of flipping between one and `k` bits.

**Why reachable:** arbitrary static unary-unbiased radius laws, geometric waiting-time distributions, and stochastic domination are all already formalized. This is arguably the most direct non-linear-function application of the Stage-68 operator abstraction.

#### D2. Doerr & Kelley (2024): Fourier Analysis Meets Runtime Analysis -- Precise Runtimes on Plateaus

**Paper:** B. Doerr, A. J. Kelley, Algorithmica 86(8), 2479--2518, DOI `10.1007/s00453-024-01232-5`.

**Result:** precise plateau runtimes via discrete Fourier analysis, including a LeadingOnes-style sequence of plateaus and optimal static/fitness-dependent mutation rates.

**Why reachable:** the repository's LeadingOnes occupation machinery and arbitrary-rate formulas provide the sequential-level side. The genuinely new ingredient is finite-group Fourier analysis.

#### D3. Doerr, Le, Makhmara & Nguyen (2017): Fast Genetic Algorithms

**Paper:** GECCO 2017, 777--784, DOI `10.1145/3071178.3071301`; arXiv:1703.03334.

**Result:** heavy-tailed randomized mutation rates give robust near-instance-optimal performance on Jump and other problems.

**Why reachable:** the static unary-unbiased operator abstraction can represent heavy-tailed radius mixtures and already exposes `p_1`, `chi`, and factorial moments. Jump-function escape analysis would require a new objective but little new mutation semantics.

#### D4. Doerr & Rajabi (2023): Stagnation Detection Meets Fast Mutation

**Paper:** B. Doerr, A. Rajabi, TCS 946, 113670, DOI `10.1016/j.tcs.2022.12.020`.

**Result:** combines heavy-tailed mutation with stagnation-driven strength adaptation and proves improved probabilities for finding distant improvements.

**Why reachable:** best attempted after D3 plus a generic dynamic-parameter state interface. The current geometric waiting-time layer is useful for the stagnation periods.

#### D5. Antipov & Doerr (2020): Heavy-Tailed `(1+(lambda,lambda))` GA on Jump

**Paper:** D. Antipov, B. Doerr, *Runtime Analysis of a Heavy-Tailed (1+(lambda,lambda)) Genetic Algorithm on Jump Functions*, PPSN 2020; arXiv:2006.03523.

**Result:** instance-independent power-law parameter choices achieve performance close (within controlled polynomial factors) to tuned parameters on Jump functions.

**Why reachable:** mutation-distribution infrastructure transfers, but crossover and two-phase offspring semantics make this more distant than D1/D3.

#### D6. Friedrich, Kötzing, Neumann, Neumann & Radhakrishnan (2025): LeadingOnes with Constraints

**Paper:** Algorithmica 87, 661--689, DOI `10.1007/s00453-025-01298-9`.

**Result:** tight `Theta(nB + n(n-B) log B)` runtime for a cardinality-constrained LeadingOnes instance, plus study of stochastic constraints.

**Why reachable:** the unconstrained exact LeadingOnes chain is already one of the most mature parts of the repository. The new work is feasible-state/constraint semantics and the additional Markov-chain analysis induced by neutral bits.

## 7. Suggested formalization order after the current proof chain

If the goal is to maximize mathematical reuse and minimize the number of new semantic frameworks introduced at once, the most efficient order appears to be:

1. **Finish the corrected Stage-79-to-runtime assembly for Doerr--Janett--Lengler (2024)** and determine the exact additional moment hypothesis, if any, needed after correcting the conditioning step.
2. **Add a general lower-bound toolkit** (preferably Doerr--Kötzing's visitation-probability fitness-level theorem, followed by Sudholt's stronger method where needed). This immediately benefits Witt, LeadingOnes, and static-unary results.
3. **Complete the remaining Böttcher--Doerr--Neumann LeadingOnes optimization results**, because the exact runtime formula is already proved and only asymptotic/optimization work remains.
4. **Extend the Witt fixed-`c` proof beyond `log 3`**, potentially using ideas from Adaptive Drift Analysis when the current C3 certificate becomes too restrictive.
5. **Formalize the unary-unbiased black-box model and OneMax exact-drift branch**, opening Doerr--Doerr--Yang, Buskulic--Doerr, and Buzdalov--Doerr.
6. **Exploit the already-formalized first two falling moments** to attack Lengler's monotone-function dichotomy; this is the most direct new use of the Stage-70--72 factorial-moment machinery outside the 2024 linear paper.
7. **Use the radius-law + geometric-waiting infrastructure on Plateau_k**, then broaden to Fourier/plateau and heavy-tailed mutation papers.

This order is a repository-engineering recommendation. It is not a ranking supplied by the cited literature.

## 8. Bibliographic index used in the frontier survey

1. He, J.; Yao, X. (2001). *Drift Analysis and Average Time Complexity of Evolutionary Algorithms*. Artificial Intelligence 127(1), 57--85. DOI: `10.1016/S0004-3702(01)00058-3`.
2. Doerr, B.; Johannsen, D.; Winzen, C. (2012). *Multiplicative Drift Analysis*. Algorithmica 64(4), 673--697. DOI: `10.1007/s00453-012-9622-x`.
3. Böttcher, S.; Doerr, B.; Neumann, F. (2010). *Optimal Fixed and Adaptive Mutation Rates for the LeadingOnes Problem*. PPSN XI, 1--10. DOI: `10.1007/978-3-642-15844-5_1`.
4. Witt, C. (2013). *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*. Combinatorics, Probability and Computing 22(2), 294--318. DOI: `10.1017/S0963548312000600`.
5. Doerr, B. (2019). *Analyzing Randomized Search Heuristics via Stochastic Domination*. Theoretical Computer Science 773, 115--137. DOI: `10.1016/j.tcs.2018.09.024`.
6. Doerr, C.; Janett, D. A.; Lengler, J. (2024). *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*. Algorithmica 86(10), 3115--3152. DOI: `10.1007/s00453-024-01258-9`.
7. Doerr, B.; Goldberg, L. A. (2013). *Adaptive Drift Analysis*. Algorithmica 65(1), 224--250. DOI: `10.1007/s00453-011-9585-3`; arXiv:1108.0295.
8. Doerr, B.; Johannsen, D.; Winzen, C. *Non-Existence of Linear Universal Drift Functions*. arXiv:1011.3466.
9. Jägersküpper, J. (2008). *A Blend of Markov-Chain and Drift Analysis*. PPSN X, LNCS 5199, 41--51. DOI: `10.1007/978-3-540-87700-4_5`.
10. Lengler, J.; Spooner, N. (2015). *Fixed Budget Performance of the (1+1) EA on Linear Functions*. FOGA XIII, 52--61. DOI: `10.1145/2725494.2725506`.
11. Einarsson, H. et al. (2019). *The Linear Hidden Subset Problem for the (1+1) EA with Scheduled and Adaptive Mutation Rates*. TCS 785, 150--170. DOI: `10.1016/j.tcs.2019.05.021`.
12. Doerr, B.; Doerr, C.; Lengler, J. (2019). *Self-Adjusting Mutation Rates with Provably Optimal Success Rules*. GECCO 2019. DOI: `10.1145/3321707.3321733`; arXiv:1902.02588.
13. Kötzing, T.; Witt, C. (2020). *Improved Fixed-Budget Results via Drift Analysis*. PPSN XVI, 648--660. DOI: `10.1007/978-3-030-58115-2_45`; arXiv:2006.07019.
14. Lehre, P. K.; Witt, C. (2013). *General Drift Analysis with Tail Bounds*. arXiv:1307.2559.
15. Kötzing, T.; Krejca, M. S. (2019). *First-hitting times under drift*. TCS 796, 51--69. DOI: `10.1016/j.tcs.2019.08.021`.
16. Sudholt, D. (2013). *A New Method for Lower Bounds on the Running Time of Evolutionary Algorithms*. IEEE TEC 17(3), 418--435. DOI: `10.1109/TEVC.2012.2202241`.
17. Doerr, B.; Kötzing, T. (2024). *Lower Bounds from Fitness Levels Made Easy*. Algorithmica 86, 367--395. DOI: `10.1007/s00453-022-00952-w`; conference version GECCO 2021, DOI `10.1145/3449639.3459352`; arXiv:2104.03372.
18. Lehre, P. K.; Witt, C. (2012). *Black-Box Search by Unbiased Variation*. Algorithmica 64(4), 623--642. DOI: `10.1007/s00453-012-9616-8`.
19. Doerr, B.; Johannsen, D.; Kötzing, T.; Lehre, P. K.; Wagner, M.; Winzen, C. (2011). *Faster Black-Box Algorithms Through Higher Arity Operators*. FOGA, 163--172. DOI: `10.1145/1967654.1967669`.
20. Doerr, B.; Winzen, C. (2012). *Black-Box Complexity: Breaking the O(n log n) Barrier of LeadingOnes*. LNCS 7401, 205--216. DOI: `10.1007/978-3-642-35533-2_18`; arXiv:1210.6465.
21. Doerr, C.; Lengler, J. (2016). *The (1+1) Elitist Black-Box Complexity of LeadingOnes*. GECCO, 1131--1138. DOI: `10.1145/2908812.2908922`.
22. Doerr, B.; Doerr, C.; Yang, J. (2020). *Optimal Parameter Choices via Precise Black-Box Analysis*. TCS 801, 1--34. DOI: `10.1016/j.tcs.2019.06.014`.
23. Buskulic, N.; Doerr, C. (2021). *Maximizing Drift Is Not Optimal for Solving OneMax*. Evolutionary Computation 29(4), 521--541. DOI: `10.1162/evco_a_00290`.
24. Gießen, C.; Witt, C. (2018). *Optimal Mutation Rates for the (1+lambda) EA on OneMax Through Asymptotically Tight Drift Analysis*. Algorithmica 80(5), 1710--1731. DOI: `10.1007/s00453-017-0360-y`.
25. Buzdalov, M.; Doerr, C. (2020). *Optimal Mutation Rates for the (1+lambda) EA on OneMax*. PPSN XVI, 574--587. DOI: `10.1007/978-3-030-58115-2_40`.
26. Buzdalov, M.; Doerr, C. (2021). *Optimal Static Mutation Strength Distributions for the (1+lambda) Evolutionary Algorithm on OneMax*. GECCO 2021, 660--668. DOI: `10.1145/3449639.3459389`; arXiv:2102.04944.
27. Doerr, B.; Gießen, C.; Witt, C.; Yang, J. (2017). *The (1+lambda) Evolutionary Algorithm with Self-Adjusting Mutation Rate*. GECCO. DOI: `10.1145/3071178.3071279`.
28. Lengler, J. (2020). *A General Dichotomy of Evolutionary Algorithms on Monotone Functions*. IEEE Transactions on Evolutionary Computation 24(6), 995--1009. DOI: `10.1109/TEVC.2019.2917014`; arXiv:1803.09227.
29. Doerr, B.; Jansen, T.; Sudholt, D.; Winzen, C.; Zarges, C. (2013). *Mutation Rate Matters Even When Optimizing Monotonic Functions*. Evolutionary Computation 21(1), 1--27. DOI: `10.1162/EVCO_a_00055`.
30. Antipov, D.; Doerr, B. (2021). *Precise Runtime Analysis for Plateau Functions*. ACM TELO 1(4), Article 13. DOI: `10.1145/3469800`.
31. Doerr, B.; Kelley, A. J. (2024). *Fourier Analysis Meets Runtime Analysis: Precise Runtimes on Plateaus*. Algorithmica 86(8), 2479--2518. DOI: `10.1007/s00453-024-01232-5`.
32. Doerr, B.; Le, H. P.; Makhmara, R.; Nguyen, T. D. (2017). *Fast Genetic Algorithms*. GECCO, 777--784. DOI: `10.1145/3071178.3071301`; arXiv:1703.03334.
33. Doerr, B.; Doerr, C.; Ebel, F. (2015). *From Black-Box Complexity to Designing New Genetic Algorithms*. TCS 567, 87--104. DOI: `10.1016/j.tcs.2014.11.028`.
34. Doerr, B.; Rajabi, A. (2023). *Stagnation Detection Meets Fast Mutation*. TCS 946, 113670. DOI: `10.1016/j.tcs.2022.12.020`.
35. Antipov, D.; Doerr, B. (2020). *Runtime Analysis of a Heavy-Tailed (1+(lambda,lambda)) Genetic Algorithm on Jump Functions*. arXiv:2006.03523; PPSN 2020.
36. Friedrich, T.; Kötzing, T.; Neumann, A.; Neumann, F.; Radhakrishnan, A. (2025). *Analysis of the (1+1) EA on LeadingOnes with Constraints*. Algorithmica 87, 661--689. DOI: `10.1007/s00453-025-01298-9`.

## 9. Bottom line

At Stage 79 fix 1, ECRuntime is no longer merely a collection of generic drift lemmas. It contains three substantial application chains: an exact finite LeadingOnes expectation theorem, a sharp Witt-style linear-function upper-bound line, and a deep corrected reconstruction of the 2024 static unary-unbiased linear-function upper proof. The newest reusable insight is the exact first/second falling-moment interface for arbitrary static unary-unbiased mutation and the corrected use of `E[K(K-1)]` under coordinate conditioning.

The most efficient next proof remains the local completion of the 2024 chain, but the literature survey shows that the repository is already close to several independent publishable theorem families: lower-bound fitness levels, adaptive/fixed-budget LeadingOnes, full fixed-`c` linear functions, unary-unbiased OneMax/black-box complexity, monotone-function moment dichotomies, and arbitrary-unbiased plateau runtimes.
