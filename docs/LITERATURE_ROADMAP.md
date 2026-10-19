# Literature roadmap

For the comprehensive compiler-certified theorem catalogue, source-paper mapping, search methodology, and the 2026-09-25 survey of more than twenty reachable next papers, see `FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`. This file remains the shorter proof-order roadmap.

## Purpose

This document maps the maintained ECRuntime proof layers to literature-facing theorem families and records the next research priorities. Compiler-fix chronology is intentionally omitted.

## Current verified baseline

### Generic stochastic/runtime infrastructure

The repository covers finite/infinite trajectories, hitting times, additive and multiplicative drift, fitness levels, stochastic domination, geometric waiting-time comparisons, and high-probability tails. This infrastructure is intended for reuse across EC algorithms.

### LeadingOnes

The completed LeadingOnes line formalizes exact entry/residence/occupation structure and exact expected runtime. The public façade is `LeadingOnesMainResults.lean`.

A useful modern reference for the broader fitness-level context is:

- Benjamin Doerr and Timo Kötzing, *Multiplicative Up-Drift*, Algorithmica 86 (2024), 367--395, DOI 10.1007/s00453-022-00952-w.

### Linear functions and Witt's theorem

The main linear-function line follows:

- Carsten Witt, *Tight Bounds on the Optimization Time of a Randomized Search Heuristic on Linear Functions*, Combinatorics, Probability and Computing 22(2) (2013), 294--318, DOI 10.1017/S0963548312000600.

The repository formalizes a Witt-style potential for positive nonincreasing linear weights, the C2/C3 decomposition, exact-singleton-rate multiplicative drift, finite expectation/tail bounds, the scaled rate `p=c/n`, and fixed-scale singleton-rate asymptotics with normalized factor `exp(c)/c`.

**Stage 66 fix 6 closes the finite C3 interval exactly:**

```text
0 <= c <= log 3,    n >= 4.
```

**Stage 67 is compiler promoted.** It factors the C3-based expectation/tail consequences into `WittMutationCertifiedRuntime.lean`, exposes the final `0 < c <= log 3` runtime/tail adapter, and removes superseded numerical endpoint modules. The finite-boundary Witt branch is now frozen.

## Active priority A: static unary-unbiased mutation on linear functions

Principal target:

- Carola Doerr, Duri Andrea Janett, and Johannes Lengler, *Tight Runtime Bounds for Static Unary Unbiased Evolutionary Algorithms on Linear Functions*, Algorithmica 86(10) (2024), 3115--3152, DOI 10.1007/s00453-024-01258-9.

The literature characterizes a static unary-unbiased operator by a distribution on the number of flipped bits followed by a uniform choice of that many coordinates. The central runtime scale is

```text
(1 ± o(1)) n log n / p_1,
```

where `p_1` is the probability of flipping exactly one bit. The theorem also places conditions on `p_1` and on the expected mutation strength `χ`; the upper- and lower-bound assumptions are not identical.

### Stage 68 fix 1 promoted: operator and one-bit-mass interface

Stage 68 deliberately handles only the reusable operator layer, and fix 1 is compiler-promoted:

1. bundle a normalized mask law invariant under Hamming radius;
2. derive the radius masses `p_k` and prove they sum to one;
3. expose `oneBitMass = p_1`;
4. expose `meanRadius = χ`;
5. prove that every specified singleton mask has mass `p_1/n` for `n>0`;
6. prove that the aggregate elementary one-bit improvement mass at state `x` is `zeroCount(x) * p_1/n`;
7. embed independent bit mutation into the new abstraction;
8. expose the induced elitist stochastic transition kernel.

This is the smallest useful post-Witt stage because it creates the exact operator parameters needed by the 2024 theorem without committing to a premature generalization of the independent-bit drift proof.

### Stage 69 fix 1 promoted: exact singleton drift bridge

Stage 69 is objective-specific but still distribution-generic. Its first compiler run stopped before theorem checking because the real-valued `singletonCoordinateRate` definition required a `noncomputable` declaration. Stage 69 fix 1 made exactly that repair and then compiled warning/error-free; the theorem surface below is promoted. It formalizes exactly the portion of the 2024 upper-bound argument that uses only the specified one-bit probability `p_1/n`:

- drift of the static unary-unbiased transition as a mask-weighted finite sum;
- the per-coordinate singleton rate `p_1/n`;
- exact zero-singleton contribution `(p_1/n) V(x)` for arbitrary linear-error coefficients;
- specialization to the existing bounded rank potential;
- exact rank drift = singleton term + named non-singleton remainder;
- as a baseline, multiplicative drift of objective error itself at rate `p_1/n`.

This mirrors the positive term in the 2024 proof: flipping exactly one specified improving coordinate has probability `p_1/n`. The paper's genuinely new work starts when controlling the negative contribution of additional flipped coordinates.


### Stage 70 fix 1 promoted: exact coordinate marginal and Claim 9 audit

Stage 70 fix 1 is compiler-promoted. It formalizes Lemma 2 directly on the finite mask law: coordinate-swap invariance, finite double counting, and `Pr[i flips] = χ/n`. It also promotes the unconditional shifted radius moment and the second factorial radius moment.

The Claim 9 audit remains unchanged. Conditioning on a specified flipped coordinate size-biases the radius distribution by `k/χ`, so the displayed mean-only conditional calculation in the published proof is not valid for arbitrary static unary-unbiased laws as written.

### Stage 71 fix 1 promoted: pair-event symmetry and factorial-moment bridge

Stage 71 fix 1 is compiler-promoted. It introduces `pairFlipMass law i j`, proves that all distinct coordinate pairs have the same mass under unary unbiasedness, proves the safe subevent bound `pairFlipMass <= χ/n`, and rewrites the second factorial radius moment as the mask-weighted expectation of `|M|(|M|-1)`.

### Stage 72 fix 1 promoted: exact pair normalization

Stage 72 adds the finite double count

```text
sum_{i != j} Pr[i and j flip] = E[K(K-1)].
```

Together with the promoted Stage-71 pair symmetry, this yields the exact specified-pair probability `E[K(K-1)]/(n(n-1))` for distinct coordinates in dimension at least two. When `χ>0`, Stage 72 also states the corresponding ratio `E[K(K-1)]/(χ(n-1))`. This is the correct size-biased conditional quantity; no mean-only bound is inserted.

The first Stage-72 verification exposed only local elaboration/linter issues in this proof; Stage 72 fix 1 repaired those points, and the focused module plus complete root build then verified warning/error-free. The exact pair normalization and size-biased ratio are therefore promoted.


### Stage 73 promoted: generic event-mass bridge for the repaired Lemma 9 estimate

Stage 73 is compiler-promoted. It adds a finite event-mass interface above the promoted pair law. For any event `A` that contains the singleton `{i}` and whose masks all flip `i`, the subevent in which a distinct coordinate `j` also flips is bounded by the pair event, while `A` itself has mass at least `p₁/n`. Combining the two bounds with Stage 72 gives

```text
Pr[j flips | A] <= E[K(K-1)] / (p_1 (n-1)).
```

This is the generic corrected coefficient obtained by replacing the invalid unconditional-radius average in equation (27) by the exact factorial-moment pair law. The module deliberately keeps `A` abstract. Stage 74 fix 1 now instantiates it on the concrete accepted/leftmost-error events used by the linear-function proof. Whether acceptance permits a stronger mean-only estimate remains a separate mathematical question.

### Dependency audit for the 2024 upper bound

Reusable without independent-bit factorization:

- finite transition / push-forward expectation semantics;
- accepted-versus-rejected linear potential drops;
- specified singleton mass `p_1/n`;
- multiplicative-drift and runtime/tail infrastructure;
- finite-sum decomposition into a singleton branch and a remainder.

Independent-bit-specific machinery that should **not** be reused as if it were generic:

- Bernoulli mask factorization and erase-balance identities involving `p` and `1-p`;
- survival-power identities used by the Witt `p=c/n` potential;
- C2/C3 estimates whose coefficients are calibrated to independent coordinate survival.

New unary-unbiased ingredients required next:

1. Stage 71 fix 1 promoted: pair-event symmetry and the mask-expectation form of `E[K(K-1)]`;
2. Stage 72 fix 1 promoted: exact ordered-distinct-pair double count, specified-pair normalization, and size-biased pair/coordinate ratio;
3. Stage 73 promoted: generic finite-event bridge yielding `E[K(K-1)]/(p_1(n-1))` for the second-coordinate conditional coefficient;
4. Stage 74 fix 1 promoted: objective-specific accepted/leftmost-error pivot events, singleton/support/disjointness facts, and direct bridge instantiation;
5. Stage 75 fix 1 promoted: generic accepted-event `L/R` coordinate split, exact pointwise potential-drop decomposition, and region-wide corrected factorial-moment right-loss bound;
6. Stage 76 fix 1 promoted: corrected penalty ratio, geometric `gamma_i`, finite suffix-min objective clipping `g_i`, concrete reversed anchor, and corrected linear potential;
7. Stage 77 fix 1 promoted: anchor-candidate representation, `gamma_anchor <= g_i`, corrected-potential `L/R` instantiation, and reduction of the right-region loss to a pure gamma suffix tail;
8. Stage 78 fix 2 promoted: exact finite geometric-tail identity, anchor-scaled tail bound, and singleton-rate-scaled corrected right-loss envelope;
9. Stage 79 fix 1 promoted: corrected suffix ratio geometry, pointwise nonnegative accepted left contribution, exact singleton left gain, and event-weighted lower bound `(p_1/n) g_i`; the focused module and complete root build verified warning/error-free;
10. actual event-weighted right-loss unconditioning and per-pivot drift assembly, followed by a global multiplicative-drift lower bound and runtime/tail/asymptotic corollaries.

The lower-bound half should remain postponed: the paper explicitly shows that the standard stochastic-domination route does not transfer to arbitrary static unary-unbiased operators.

## Priority B: general drift theorems driven by a concrete application

Candidates include variable drift with explicit integral bounds, lower-bound drift theorems, stronger concentration variants, and phase/restart interfaces. Add these when a selected EC theorem requires them rather than speculatively.

## Priority C: unary-unbiased black-box complexity

This would broaden the repository from fixed-algorithm runtime analysis to complexity of algorithm classes. It requires new machinery for randomized query algorithms, information histories, admissible operator classes, and lower-bound/minimax arguments, so it should follow the nearer-term static unary-unbiased mutation extension.

## Priority D: monotone/dynamic functions

These objective classes would stress-test the current fixed-objective semantics and likely require environment/state extensions.

## Priority E: population and crossover algorithms

Algorithms such as the `(1+(lambda,lambda))` GA are high-value but structurally expensive because they require population states, multi-stage iterations, crossover kernels, and more elaborate cost accounting.

## Repository-level theorem design goal

For every new literature theorem, prefer:

```text
algorithm-independent probability/runtime lemma
        -> operator-specific transition/kernel facts
        -> objective/potential-specific progress theorem
        -> generic expectation/tail consequence
        -> asymptotic/literature-facing corollary
```

Avoid encoding proof-discovery history into permanent module dependencies.

## Near-term plan

1. Relate event mass times the promoted conditional right-loss proxy to the actual event-weighted right loss, using the pivot-event upper mass `chi/n`.
2. Combine that event-weighted right loss with the promoted Stage-79 singleton left contribution to obtain the corrected per-pivot drift inequality.
3. Determine the strongest valid global multiplicative-drift theorem under the resulting factorial-moment condition.
4. Only if an additional argument recovers a mean-only estimate should the original `χ`-only statement be reinstated.


### Stage 74 fix 1: finite accepted-event representation repair

The first Stage-74 build failed before any objective-specific theorem was tested: the finite `Finset.filter` defining the event contained the real-valued acceptance proposition, and Lean did not infer a `DecidablePred`. Fix 1 places the filter construction under an explicit classical boundary and exports a membership characterization theorem. All support, singleton, disjointness, positivity, and corrected conditional-bound statements are unchanged.

### Stage 74 fix 1 and Stage 75 fix 1 promoted

Stage 74 fix 1 promotes the concrete accepted leftmost-error pivot events. Stage 75 fix 1 promotes the generic repository-convention `L/R` split around an abstract anchor, the exact accepted weighted-error identity `Delta = Delta_L + Delta_R`, and the corrected region-wide factorial-moment right-loss bound. The only Stage-75 repair was removal of three unused simp arguments.


### Historical Stage 77-to-78 transition (both layers now promoted)

The Stage-77-fix-1 focused target and complete root build verified warning/error-free, promoting the anchor-candidate representation, `gamma_anchor <= g_i`, corrected-potential `L/R` specialization, gamma-tail reduction, and conditional right-loss theorem. Stage 78 closes the remaining geometric algebra: it reindexes the strict suffix to a finite power sum, proves `GammaTail(k) * (alpha*rho) = gamma_k - 1`, obtains `rho * GammaTail(anchor(i)) <= g_i/alpha` for positive slack, and combines this with the promoted calibration identity to bound the right-loss proxy in singleton-rate units. The next proof boundary is no longer geometric; it is the actual accepted-event mass/left-gain assembly needed for the corrected per-pivot drift inequality.

The first Stage-78 pinned build localized its only error to the inverse direction of the suffix-index equivalence: `omega` could not recover the defining arithmetic of a `Fin` value while it was being constructed. Stage 78 fix 1 moved both natural-number inequalities outside that constructor and reused them explicitly. The fix-1 pinned build then confirmed the constructor repair and localized the remaining errors to `left_inv` and `right_inv`, where the composed equivalence maps remained opaque to `omega`. Stage 78 fix 2 changes those goals to the explicit natural-number involution equalities before invoking arithmetic automation. The theorem surface and all downstream algebra are unchanged.

### Stage 78 fix 2 and Stage 79 fix 1 promoted

The Stage-78-fix-2 focused target and complete root build verified warning/error-free, promoting the closed gamma-tail identity and singleton-rate-scaled right-loss envelope. Stage 79 formalizes the prerequisite used before equation (22) of the literature argument: the accepted `L` contribution is pointwise nonnegative. For the corrected suffix-min potential, the proof is expressed through two ratio envelopes: `g_i/w_i <= g_q/w_q` for pivot-suffix coordinates `q`, and `g_j/w_j <= g_i/w_i` for coordinates `j` no more important than the corrected anchor. Objective acceptance then yields `Delta_L >= 0`. The singleton pivot mask contributes exactly `g_i`, giving the event-weighted lower bound `(p_1/n) g_i`. The first pinned build exposed only three local proof-engineering diagnostics; Stage 79 fix 1 repaired those without changing any mathematical statement, and the fix-1 focused plus complete root builds then verified warning/error-free. No mean-only pair-conditioning estimate is introduced.

