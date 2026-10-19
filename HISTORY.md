# ECRuntime milestone history

Compact mathematical milestones only. Detailed compiler-fix chronology is retained in the
per-stage verification reviews written to `.verify/stage-<N>/review.txt` by
`scripts/verify.sh`, and in archived verification bundles.

## Foundations

- Built finite-state EC semantics for bit strings, mutation, objectives, and elitist `(1+1)` transitions.
- Added finite trajectory weights, projective consistency, kernel-based infinite trajectories, finite-marginal identification, and sample-path hitting-time bridges.

## Generic runtime theory

- Formalized additive and multiplicative drift, fitness levels, stochastic domination, geometric waiting laws/sums, and high-probability tails.
- Developed level-exit/residence/coupling machinery.
- Replaced the exploratory adaptive failure-vector route by the direct Bellman/memoryless-tail route; branch-only modules were pruned in Stage 66.

## LeadingOnes

- Formalized first-crossing symmetry, exact entry distributions, residence/occupation identities, renewal, and exact expected-runtime closure.
- Added scaled-rate and standard-rate public interfaces.

## Linear functions / Witt theorem line

- Formalized the Witt potential, C2/C3 one-step decomposition, strict-tail control, and exact-singleton-rate multiplicative drift.
- Derived standard-rate expectation and high-probability results.
- Extended the theory to `p=c/n` and formalized the fixed-scale exact-rate limit with leading factor `exp(c)/c`.

## Stage 49--52: first beyond-standard-rate interval and asymptotics

- Established a finite C3 certificate through `c <= 21/20` and propagated it to expectation/tail results.
- Removed the historical `c <= 1` restriction from fixed-positive-scale singleton-rate asymptotics.
- Connected the exact-rate finite envelope to the sharp normalized coefficient `exp(c)/c`.

## Stage 57--65: numerical approach to the C3 boundary

- Advanced the finite C3 certificate through several rational endpoints, culminating in the promoted Stage-65 value `10977/10000`.
- The repeated endpoint modules were useful during proof discovery but created substantial duplicate finite checking and runtime propagation.

## Stage 66: exact analytic C3 boundary and repository consolidation

- Extracted endpoint-independent monotonicity into `WittMutationC3Envelope.lean`.
- Extracted endpoint-independent finite runtime consequences into `WittMutationCertifiedRuntime.lean`.
- Pruned superseded intermediate endpoint/runtime modules and abandoned branch-only files.
- Replaced hundreds of finite rational checks near the boundary by a dimension-uniform logarithmic proof.
- **Stage 66 fix 6 compiled warning/error-free and promoted the natural finite boundary** `0 <= c <= log 3`, `n >= 4`.

## Stage 67: final Witt runtime/tail consolidation

- Moved all C3-based finite expectation, geometric-tail, and shifted-exponential consequences into `WittMutationCertifiedRuntime.lean`.
- Added the single final `WittMutationLogThreeRuntime.lean` adapter on `0 < c <= log 3`.
- Rewrote the retained `21/20` compatibility tail API over the same generic interface.
- Removed the superseded Stage-63/64/65 numerical endpoint modules.
- **Stage 67 compiled warning/error-free and freezes the finite-boundary Witt branch.**

## Stage 68 / fix 1: static unary-unbiased mutation foundation

- Introduces a normalized mutation-mask law invariant under Hamming radius.
- Derives the radius distribution, one-bit mass `p₁`, and mean radius `χ`.
- Exposes exact `p₁/n` specified-singleton mass and `zeroCount(x) * p₁/n` aggregate one-bit improvement mass.
- Embeds independent bit mutation into the abstraction and defines its induced elitist stochastic transition.
- Initial Stage 68 verification exposed only two API/elaboration issues: the correct Mathlib emptiness theorem is `Finset.powersetCard_eq_empty`, and the independent-bit one-bit-mass theorem must instantiate the dimension explicitly. Stage 68 fix 1 repaired only those points.
- **Stage 68 fix 1 compiled warning/error-free and promotes the operator/radius/`p₁`/`χ` interface.**

## Stage 69 / fix 1: unary-unbiased singleton linear drift

- Adds a generic mask-sum drift identity for the new static unary-unbiased transition.
- Names the per-coordinate singleton rate `p₁/n`.
- Proves that zero-singleton events contribute exactly `(p₁/n) V(x)` to any linear-error potential.
- Specializes this identity to the bounded rank potential and isolates the remaining non-singleton contribution as a named remainder.
- Adds the coefficient-sensitive baseline that objective error has multiplicative drift at rate `p₁/n` for every static unary-unbiased law.
- Leaves all genuinely new multi-bit/`χ` estimates for the next stage.
## Stage 69 fix 1 — noncomputable singleton-rate repair

The Stage 69 build reached `StaticUnaryUnbiasedLinearDrift.lean` but stopped at the definition of `singletonCoordinateRate`: real division uses Mathlib's noncomputable real inverse. Fix 1 marked only this definition `noncomputable`. No theorem statement, operator definition, or mathematical argument changed. **Stage 69 fix 1 then compiled warning/error-free and promotes the exact singleton drift/remainder bridge.**

## Stage 70 candidate: coordinate-flip marginals and pair-moment audit

- Adds `StaticUnaryUnbiasedFlipMarginals.lean`.
- Defines actual coordinate-flip event mass and proves it is invariant under coordinate swaps.
- Proves the mask-cardinality expectation identity and the exact marginal `Pr[i flips] = χ/n`.
- Names the unconditional shifted radius moment and proves it is at most `χ`.
- Names the second factorial radius moment, which is the natural quantity for two-coordinate flip events.
- Records a literature-audit issue before formalizing Claim 9: conditioning on a specified bit flip size-biases the radius law, so the displayed equation (27) cannot in general average `(k-1)/(n-1)` against the original `p_k`. The conditional/pair theorem is postponed until the exact factorial-moment identity is formalized and the published argument is repaired or supplemented by an additional assumption.


## Stage 70 fix 1 — zero-warning `simp` repair

The Stage 70 focused module and complete root build both succeeded, but promotion failed because `StaticUnaryUnbiasedFlipMarginals.lean` emitted one `unnecessarySimpa` linter warning. Fix 1 replaces the warned `simpa [e] using ...` step by `simp [e]`. No theorem statement or mathematical argument changes.

## Stage 70 fix 1 — promoted coordinate marginal

The warning-only repair was verified cleanly in Lean 4.32.1: the focused `StaticUnaryUnbiasedFlipMarginals` build, complete root build, export, and zero-warning gate all passed. Stage 70 fix 1 therefore promotes `Pr[i flips] = χ/n` and the radius-moment audit layer.

## Stage 71 candidate: pair marginals and factorial-moment bridge

- Adds `StaticUnaryUnbiasedPairMarginals.lean`.
- Defines the mass of masks flipping two specified coordinates.
- Proves symmetry in the pair and equality of pair-flip mass for all distinct coordinate pairs using coordinate swaps.
- Proves pair-flip mass is a subevent of the promoted coordinate marginal and hence at most `χ/n`.
- Rewrites the second factorial radius moment as the mask expectation of `|M|(|M|-1)`.
- Deliberately postpones the final `n(n-1)` normalization to a separate finite double-counting stage; no published mean-only conditional bound is assumed.

## Stage 71 fix 1 — pair-symmetry elaboration repair

The first Stage-71 verification reached `StaticUnaryUnbiasedPairMarginals.lean` and exposed only local proof-engineering issues: the swap action on a third coordinate needed the explicit fixed-point theorem `Equiv.swap_apply_of_ne_of_ne`, one `simpa`/simp argument list was over-specified, and one disequality reversal used the invalid function-field projection `.symm`. Fix 1 supplies the explicit swap equality, uses the simpler `simp [e]` transport, and replaces disequality projections by `Ne.symm`. No theorem statement or probability claim changes.

## Stage 71 fix 1 — promoted pair marginals

The Stage 71 fix-1 verification compiled `StaticUnaryUnbiasedPairMarginals.lean` and the complete root repository warning/error-free. This promotes equality of distinct pair-flip masses under unary-unbiased symmetry, the safe pair-to-coordinate subevent bound, and the mask-expectation form of `E[K(K-1)]`.

## Stage 72 candidate — exact pair normalization

- Adds `StaticUnaryUnbiasedPairNormalization.lean`.
- Double-counts ordered distinct flipped coordinate pairs inside each mutation mask.
- Identifies aggregate ordered-pair mass with the second factorial radius moment.
- Uses Stage-71 pair exchangeability to derive `Pr[i,j flip] = E[K(K-1)]/(n(n-1))` for distinct coordinates when `n >= 2`.
- Under `χ>0`, derives the corresponding size-biased conditional ratio `E[K(K-1)]/(χ(n-1))`.
- Does not assume the disputed mean-only `χ/(n-1)` Claim-9 bound.


## Stage 72 fix 1 — local double-count proof repair

The first Stage-72 verification reached `StaticUnaryUnbiasedPairNormalization.lean` and exposed only local proof-engineering issues. In the positive membership branch of the fixed-mask count, the calculation established the numeric value but did not close the surrounding `if i ∈ mask`; fix 1 adds the final `simp [hi]`. The mask-filter equality now uses the linter-minimal `simp [Finset.mem_erase]`, and the redundant `ring` following a goal-closing `field_simp` is removed. No theorem statement, probability normalization, or Claim-9 audit conclusion changes.

## Stage 72 fix 1 — promoted exact pair normalization

The Stage 72 fix-1 verification compiled `StaticUnaryUnbiasedPairNormalization.lean` and the complete root repository warning/error-free. This promotes the ordered-distinct-pair double count, the exact specified-pair mass `E[K(K-1)]/(n(n-1))`, and the corresponding size-biased pair/coordinate ratio.

## Stage 73 candidate — generic accepted-event mass bridge

- Adds `StaticUnaryUnbiasedAcceptedEventBridge.lean`.
- Introduces finite mask-event mass and monotonicity under event inclusion.
- Shows that if an event is supported on masks flipping `i`, its `j`-slice is bounded by the unconditional pair-flip mass.
- Shows that an event containing the singleton `{i}` has denominator mass at least the singleton mass `p₁/n`.
- Combines these facts with Stage 72 to obtain the corrected generic conditional coefficient `E[K(K-1)]/(p₁(n-1))` for distinct `i,j` when `p₁>0`.
- Does not assert the published mean-only `χ/(n-1)` replacement; objective-specific accepted/leftmost event instantiation is postponed to the next stage.

## Stage 73 — promoted generic accepted-event bridge

The Stage 73 verification compiled `StaticUnaryUnbiasedAcceptedEventBridge.lean` and the complete root repository warning/error-free. This promotes finite mask-event mass, monotonicity, singleton denominator control, and the corrected generic conditional coefficient `E[K(K-1)]/(p₁(n-1))` for events containing `{i}` and supported on masks flipping `i`.

## Stage 74 candidate — objective-specific accepted pivot events

- Adds `StaticUnaryUnbiasedLinearAcceptedEvents.lean`.
- Defines the concrete accepted leftmost-error pivot event for positive linear functions in the repository's reversed maximization convention.
- Proves every event mask flips its pivot, records the pivot zero status and acceptance, and proves the pivot is the most-important zero-to-one flip.
- Proves the specified singleton zero-to-one mutation belongs to its pivot event.
- Proves distinct pivot events are disjoint.
- Proves pivot-event mass is positive under `p₁>0`.
- Instantiates the promoted Stage-73 bridge to obtain the corrected second-coordinate coefficient `E[K(K-1)]/(p₁(n-1))` for the concrete event.
- Does not reintroduce the unsupported mean-only `χ/(n-1)` estimate.


## Stage 74 fix 1 — accepted-event decidability/elaboration repair

The first Stage-74 verification reached `StaticUnaryUnbiasedLinearAcceptedEvents.lean` and failed first at the `Finset.filter` definition of the accepted pivot event: Lean could not synthesize a `DecidablePred` because the predicate contains real-valued elitist acceptance. The remaining `mem_filter` projection/type errors were downstream elaboration fallout from that failed definition. Fix 1 constructs the finite filter inside an explicit `classical` block and adds `mem_acceptedLeftmostZeroEvent_iff`; all downstream proofs use that theorem rather than unfolding the filter. The event semantics, singleton inclusion, disjointness, positive-mass theorem, and corrected factorial-moment conditional bound are unchanged.

## Stage 74 fix 1 — promoted concrete accepted pivot events

The Stage 74 fix-1 verification compiled `StaticUnaryUnbiasedLinearAcceptedEvents.lean` and the complete root repository warning/error-free. This promotes the concrete accepted leftmost-error pivot events in the repository's reversed maximization convention, their support/singleton/disjointness/positive-mass facts, and the direct corrected conditional bound based on `E[K(K-1)]/(p₁(n-1))`.

## Stage 75 candidate — accepted-event left/right loss decomposition

- Adds `StaticUnaryUnbiasedLinearLossDecomposition.lean`.
- Keeps the literature anchor coordinate abstract and partitions currently-one coordinates into a more-important/equal left region and a less-important right region in the repository convention.
- Proves the exact pointwise accepted weighted-error decomposition `Delta = Delta_L + Delta_R`.
- Defines the finite conditional right-loss proxy `sum_{j in R} g_j Pr[j flips | A_i]`.
- Sums the promoted Stage-74 per-coordinate conditional estimate to bound that proxy with the exact factorial-moment coefficient `E[K(K-1)]/(p₁(n-1))`.
- Deliberately postpones the recursive literature-specific `gamma_i`, `g_i`, and reversed anchor `k(i)` construction to the next stage.

## Stage 75 fix 1 — warning-only simp cleanup

The Stage-75 focused module and complete root build both compiled successfully, but the zero-warning gate rejected promotion because three `simp` calls in `oneToZero_sum_eq_acceptedLeftLoss_add_acceptedRightLoss` supplied the branch equation `hx` even though simplification did not use it. Fix 1 removes only those three redundant simp arguments. No theorem statement, accepted-event decomposition, right-loss proxy, or factorial-moment coefficient changes.


## Stage 75 fix 1 — promoted accepted-event loss decomposition

The Stage 75 fix-1 verification compiled `StaticUnaryUnbiasedLinearLossDecomposition.lean` and the complete root repository warning/error-free. This promotes the generic accepted-event `L/R` split, exact pointwise `Delta = Delta_L + Delta_R`, and the region-wide corrected factorial-moment right-loss bound.

## Stage 76 candidate — corrected factorial-moment potential calibration

- Adds `StaticUnaryUnbiasedCorrectedPotential.lean`.
- Defines `rho = chi * E[K(K-1)] / ((n-1) p₁^2)` and proves the exact calibration identity relating the Stage-75 right-loss term to the singleton rate.
- Defines the corrected geometric baseline `1 + alpha*rho` and reversed-index coefficients `gamma_i`.
- Defines objective-clipped coefficients by the finite suffix minimum `min_{j >= i} gamma_j w_i / w_j`.
- Retains a concrete minimizing suffix coordinate as the reversed anchor.
- Proves anchor membership/minimality, clipping below the geometric baseline, coefficient lower bounds for positive nonincreasing objectives, and the all-ones target characterization.
- Leaves the one-step recurrence/contact theorem and final drift assembly to the next stage.

## Stage 76 fix 1 — suffix finiteness / tactic cleanup

The first Stage-76 build localized all failures to `StaticUnaryUnbiasedCorrectedPotential.lean`: typeclass search could not synthesize `Finite (CorrectedSuffixIndex i)` at the two uses of `Finite.exists_min`, and `field_simp` already closed the calibration identity before a trailing `ring`. Fix 1 adds an explicit `Finite` instance by unfolding `CorrectedSuffixIndex` and invoking the generic subtype instance, and removes the unreachable `ring`. No mathematical definition or theorem statement changes. Stage 75 fix 1 remains the latest promoted checkpoint until Fix 1 verifies warning/error-free.

## Stage 76 fix 1 — promoted corrected potential calibration

The Stage 76 fix-1 verification compiled `StaticUnaryUnbiasedCorrectedPotential.lean` and the complete root repository warning/error-free. This promotes the corrected penalty ratio `rho = chi E[K(K-1)] / ((n-1)p₁^2)`, geometric baseline, finite suffix-min clipping, concrete reversed anchor, coefficient bounds, and corrected linear potential.

## Stage 77 candidate — corrected anchor envelope and gamma-tail reduction

- Adds `StaticUnaryUnbiasedCorrectedPotentialEnvelope.lean`.
- Exposes the exact anchor-candidate formula for the clipped coefficient.
- Proves `gamma_anchor <= g_i` under positive nonincreasing objective weights.
- Defines the pure gamma suffix tail strictly to the right of an anchor.
- Bounds the entire accepted right-region corrected-weight sum by this gamma tail.
- Instantiates the promoted Stage-75 accepted `L/R` decomposition at the corrected anchor and corrected potential.
- Instantiates the promoted right-loss proxy and reduces it to the pure gamma tail times the verified factorial-moment coefficient.
- Leaves only the closed-form geometric-tail calculation and the resulting per-pivot drift inequality to the next stage.

## Stage 77 fix 1 — right-region suffix membership repair

The first Stage-77 pinned build localized all diagnostics to `StaticUnaryUnbiasedCorrectedPotentialEnvelope.lean`. The right-region subset proof had already extracted `k.val < j.val` from `mem_acceptedRightRegion_iff`, but `simp` left the equivalent `Fin` order goal `k < j` unsolved and also reported the inequality as an unused simp argument. Fix 1 replaces that simplification with an explicit `Finset.mem_filter.mpr` construction using `Finset.mem_univ` and the extracted inequality. No anchor, gamma-tail, loss-proxy, coefficient, or theorem statement changes. Stage 76 fix 1 remains the latest promoted checkpoint until this repair verifies warning/error-free.


## Stage 77 fix 1 — promoted anchor envelope

The Stage-77-fix-1 focused target and complete root build verified warning/error-free in Lean 4.32.1. This promotes the exact anchor-candidate formula, `gamma_anchor <= g_i`, the corrected-potential accepted `L/R` specialization, and the pure gamma-tail right-loss envelope.

## Stage 78 candidate — closed corrected gamma tail and singleton-rate right-loss scaling

- Adds `StaticUnaryUnbiasedCorrectedGammaTail.lean`.
- Reindexes the strict suffix after an anchor to `Fin (n-1-k)` and evaluates the promoted gamma tail as a finite geometric sum.
- Proves `GammaTail(k) * (alpha*rho) = gamma_k - 1`.
- For positive slack, derives `rho * GammaTail(anchor(i)) <= g_i / alpha`.
- Combines the Stage-77 right-loss envelope with the Stage-76 calibration identity to express the negative term in singleton-rate units.
- Leaves actual pivot-event mass and left-gain assembly, followed by global multiplicative drift, to the next stage.


## Stage 78 fix 1 — suffix inverse arithmetic repair

The first Stage-78 pinned build localized the only error to `correctedTailIndexEquiv.invFun` in `StaticUnaryUnbiasedCorrectedGammaTail.lean`. The inverse index is `n - 1 - r.val`; inside the nested `Fin` constructor, `omega` abstracted that value and could not prove the strict-suffix side condition. Fix 1 first proves `n - 1 - r.val < n` and `k.val < n - 1 - r.val` as explicit natural-number facts and only then constructs the `Fin` value. No geometric identity, calibrated tail bound, right-loss theorem, or public theorem statement changes. Stage 77 fix 1 remains the latest promoted checkpoint until this repair verifies warning/error-free.

## Stage 78 fix 2 — suffix equivalence inverse-law repair

The Stage-78-fix-1 pinned build confirmed that the repaired inverse constructor elaborates, but localized the remaining two errors to `correctedTailIndexEquiv.left_inv` and `.right_inv`. In both proofs `omega` saw opaque composed `toFun`/`invFun` lambda applications rather than the concrete natural-number involution. Fix 2 changes the goals explicitly to `n - 1 - (n - 1 - j.val) = j.val` and `n - 1 - (n - 1 - r.val) = r.val` before invoking `omega`. No equivalence, gamma-tail identity, calibrated loss bound, or public theorem statement changes. Stage 77 fix 1 remains the latest promoted checkpoint until this repair verifies warning/error-free.

## Stage 78 fix 2 promoted / Stage 79 candidate

Stage 78 fix 2 verified warning/error-free in the focused `StaticUnaryUnbiasedCorrectedGammaTail` build and complete root build, so the corrected closed gamma-tail layer is promoted. Stage 79 adds `StaticUnaryUnbiasedCorrectedLeftGain.lean`: suffix monotonicity of `g_i/w_i`, the anchor-side left envelope, pointwise `Delta_L >= 0` on accepted pivot masks, the exact singleton `Delta_L = g_i`, and the event-weighted lower bound `(p_1/n) g_i`. The next boundary is event-weighted right-loss unconditioning and per-pivot drift assembly.

## Stage 79 fix 1 — corrected-left-gain proof elaboration repair

The first Stage-79 pinned build reached `StaticUnaryUnbiasedCorrectedLeftGain.lean` and localized all diagnostics to three proof-engineering points. Fix 1 removes one unused `simp` argument, derives `n > 0` from the existing pivot index bound `i.isLt` before invoking `omega`, and states the singleton lower-bound step with `Finset.single_le_sum` as a fully elaborated expression instead of through `apply`. No corrected-ratio, left-loss, singleton-gain, event-weighted contribution, or public theorem statement changes. Stage 78 fix 2 remains the latest promoted checkpoint until this repair verifies warning/error-free.

## Stage 79 fix 1 — promoted corrected left gain and literature-frontier checkpoint

The Stage-79-fix-1 focused `StaticUnaryUnbiasedCorrectedLeftGain` build and the complete root build verified warning/error-free in Lean 4.32.1. This promotes the suffix-ratio geometry, pointwise nonnegative accepted left contribution, exact singleton left gain, and event-weighted lower bound `(p₁/n) g_i`. The repository is paused at this clean boundary before Stage 80. A comprehensive provenance/literature document, `docs/FORMALIZED_RESULTS_AND_LITERATURE_FRONTIER.md`, records the major machine-checked statements, their source papers, explicit gaps/limitations, search methodology, and a refreshed frontier of more than twenty closely related next papers.
