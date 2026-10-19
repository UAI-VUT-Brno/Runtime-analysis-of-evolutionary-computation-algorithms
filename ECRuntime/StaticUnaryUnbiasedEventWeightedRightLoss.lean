import ECRuntime.StaticUnaryUnbiasedCorrectedGammaTail
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Event-weighted right loss: unconditioning the corrected right-loss proxy

Stage 78 fix 2 promoted the *conditional* right-loss estimate

`(chi/n) * acceptedRightConditionalLossProxy A_i <= (p_1/n) * (g_i / alpha)`,

in which `acceptedRightConditionalLossProxy` is a weighted sum of conditional flip
probabilities `Pr[j flips | A_i]`.  The drift assembly needs the *event-weighted*
quantity

`sum_{M in A_i} Pr(M) * RightLoss(M)`,

which is integrated against the unconditioned mask law restricted to the event.  This
module performs exactly that change of measure, and nothing else.

## Which measure is which

All three measures involved are finite sums against the promoted mask law `law.weight`,
which is nonnegative and sums to one over `MutationMask n`.

* `law.maskEventMass A = sum_{M in A} law.weight M` is the law-measure of the event `A`.
* `acceptedRightWeightedLoss A g x k = sum_{M in A} law.weight M * acceptedRightLoss g x M k`
  integrates the pointwise right loss against the law **restricted** to `A` (an
  unnormalized measure).  This is the quantity the per-pivot drift needs.
* `acceptedRightConditionalLossProxy A g x k = sum_{j in R} g_j * (mass(slice_j) / mass(A))`
  integrates the same pointwise right loss against the **normalized conditional** law
  `law(.|A)`.

The two differ by exactly the factor `law.maskEventMass A`, and
`maskEventMass_mul_acceptedRightConditionalLossProxy_eq_acceptedRightWeightedLoss`
proves that identity with no positivity side condition at all: when the event has zero
mass both sides vanish, because nonnegative weights force every sub-slice to vanish too.
The conditional object is therefore never manipulated as an unexplained literature step;
it is pinned to the restricted measure by a proved finite identity, which is what
`DEVELOPMENT.md` section 4 requires before a conditional step may be encoded.

## Direction of the inequality

The pivot-event mass enters as an **upper** bound: every mask in
`acceptedLeftmostZeroEvent w x i` flips `i`, so

`maskEventMass (acceptedLeftmostZeroEvent w x i) <= coordinateFlipMass i = chi/n`.

Multiplying the exact identity by this upper bound is legitimate only because the proxy
is nonnegative, which needs nonnegative right-region coefficients; that hypothesis is
therefore load-bearing and is stated explicitly rather than assumed.  The result is an
**upper** bound on the event-weighted right loss -- the direction needed, since the
right loss enters the drift negatively.

No per-pivot drift assembly, no multiplicative-drift theorem, and no mean-only
`chi/(n-1)` estimate appears here.
-/

/--
Any finite mask event supported on masks that flip a specified coordinate has mass at
most that coordinate's flip mass.
-/
theorem maskEventMass_le_coordinateFlipMass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (i : Fin n)
    (hsupp : ∀ mask ∈ event, i ∈ mask) :
    law.maskEventMass event ≤ law.coordinateFlipMass i := by
  sorry

/--
The promoted exact marginal `Pr[i flips] = chi/n` turns the previous bound into the
dimension-free upper mass `chi/n`.  Positive dimension is automatic from `i : Fin n`.
-/
theorem maskEventMass_le_meanRadius_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (i : Fin n)
    (hsupp : ∀ mask ∈ event, i ∈ mask) :
    law.maskEventMass event ≤ law.meanRadius / (n : ℝ) := by
  sorry

/--
The concrete accepted leftmost-zero pivot event has mass at most `chi/n`.

This is the upper half of the pivot-event mass sandwich; the promoted
`acceptedLeftmostZeroEvent_mass_pos` is the lower half.  It needs no hypothesis: every
mask in the event flips the pivot by `acceptedLeftmostZeroEvent_supports_pivot`.
-/
theorem acceptedLeftmostZeroEvent_mass_le_meanRadius_div {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    law.maskEventMass (acceptedLeftmostZeroEvent w x i) ≤
      law.meanRadius / (n : ℝ) := by
  sorry

/--
Event-weighted right loss: the Stage-75 pointwise right loss integrated against the mask
law restricted to a finite event.

This is the unnormalized `R`-side counterpart of the promoted Stage-79
`acceptedLeftWeightedContribution`.
-/
noncomputable def acceptedRightWeightedLoss {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) : ℝ :=
  ∑ mask ∈ event, law.weight mask * acceptedRightLoss g x mask k

/--
Event-weighted `R` contribution, sign-normalized exactly like the Stage-79 `L`
contribution so that the two can later be added under the promoted `Delta_L + Delta_R`
identity.
-/
noncomputable def acceptedRightWeightedContribution {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) : ℝ :=
  ∑ mask ∈ event, law.weight mask * acceptedRightDelta g x mask k

/-- The event-weighted `R` contribution is the negated event-weighted right loss. -/
theorem acceptedRightWeightedContribution_eq_neg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) :
    law.acceptedRightWeightedContribution event g x k =
      -law.acceptedRightWeightedLoss event g x k := by
  sorry

/--
Finite Fubini identity: summing the pointwise right loss against the restricted law is
the same as charging each right-region coordinate by the mass of the sub-event on which
that coordinate also flips.

This identity is exact and needs no hypothesis whatsoever -- in particular no sign
condition on `g` and no positivity of the event mass.
-/
theorem acceptedRightWeightedLoss_eq_sum_secondCoordinateSlice_mass {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) :
    law.acceptedRightWeightedLoss event g x k =
      ∑ j ∈ acceptedRightRegion x k,
        g j * law.maskEventMass (secondCoordinateSlice event j) := by
  sorry

/--
Exact change of measure: event mass times the promoted conditional right-loss proxy is
the event-weighted right loss.

This is the central statement of the stage.  It is deliberately a **product** identity
rather than a quotient, so no caller is forced to carry a positivity hypothesis.  The
degenerate case is genuine content, not an artifact: if `maskEventMass event = 0` then
nonnegativity of the mask weights forces every `secondCoordinateSlice` mass to vanish,
so the right-hand side is `0` and the left-hand side is `0 * proxy = 0`.
-/
theorem maskEventMass_mul_acceptedRightConditionalLossProxy_eq_acceptedRightWeightedLoss
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) :
    law.maskEventMass event *
        law.acceptedRightConditionalLossProxy event g x k =
      law.acceptedRightWeightedLoss event g x k := by
  sorry

/--
On an event of positive mass, the promoted proxy is exactly the conditional expectation
of the pointwise right loss under the normalized law `law(.|event)`.

This is the audit-facing form of the previous identity: it states in one line which
measure the word "conditional" refers to in `acceptedRightConditionalLossProxy`.  The
positivity hypothesis is genuinely needed, because the statement divides.
-/
theorem acceptedRightConditionalLossProxy_eq_div_of_mass_pos {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (hmass : 0 < law.maskEventMass event)
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) :
    law.acceptedRightConditionalLossProxy event g x k =
      law.acceptedRightWeightedLoss event g x k / law.maskEventMass event := by
  sorry

/--
With nonnegative right-region coefficients the conditional right-loss proxy is
nonnegative.  This is what makes multiplication by an upper mass bound valid.
-/
theorem acceptedRightConditionalLossProxy_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n)
    (hg : ∀ j ∈ acceptedRightRegion x k, 0 ≤ g j) :
    0 ≤ law.acceptedRightConditionalLossProxy event g x k := by
  sorry

/--
Generic unconditioning bound: for an event supported on masks flipping a specified
coordinate, the event-weighted right loss is at most the coordinate's flip rate `chi/n`
times the conditional proxy.

Both hypotheses are used: `hsupp` supplies the upper mass bound `chi/n`, and `hg`
supplies nonnegativity of the proxy, without which multiplying by an upper bound would
reverse the inequality.
-/
theorem acceptedRightWeightedLoss_le_meanFlipRate_mul_proxy {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (i : Fin n)
    (hsupp : ∀ mask ∈ event, i ∈ mask)
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n)
    (hg : ∀ j ∈ acceptedRightRegion x k, 0 ≤ g j) :
    law.acceptedRightWeightedLoss event g x k ≤
      (law.meanRadius / (n : ℝ)) *
        law.acceptedRightConditionalLossProxy event g x k := by
  sorry

/-- The same unconditioning bound on the concrete accepted leftmost-zero pivot event. -/
theorem acceptedLeftmostZeroEvent_rightWeightedLoss_le_meanFlipRate_mul_proxy {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (x : BitString n) (i k : Fin n)
    (hg : ∀ j ∈ acceptedRightRegion x k, 0 ≤ g j) :
    law.acceptedRightWeightedLoss (acceptedLeftmostZeroEvent w x i) g x k ≤
      (law.meanRadius / (n : ℝ)) *
        law.acceptedRightConditionalLossProxy
          (acceptedLeftmostZeroEvent w x i) g x k := by
  sorry

/--
Drift-ready event-weighted right loss in singleton-rate units.

Chaining the unconditioning bound with the promoted Stage-78 endpoint
`meanFlipRate_mul_correctedRightConditionalLossProxy_le_singletonRate_weight_div`
replaces the conditional proxy by the corrected geometric envelope, giving

`sum_{M in A_i} Pr(M) * RightLoss(M) <= (p_1/n) * (g_i / alpha)`.

This is the `R`-side counterpart of the promoted Stage-79 `L`-side lower bound
`(p_1/n) * g_i <= sum_{M in A_i} Pr(M) * Delta_L(M)`.  Combining the two is deliberately
left to the next stage.
-/
theorem acceptedLeftmostZeroEvent_correctedRightWeightedLoss_le_singletonRate_weight_div
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    law.acceptedRightWeightedLoss
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) ≤
      (law.oneBitMass / (n : ℝ)) *
        (law.correctedPotentialWeight alpha w i / alpha) := by
  sorry

/--
Sign-normalized form of the previous bound: the event-weighted `R` contribution of the
accepted pivot event is at least `-(p_1/n) * (g_i / alpha)`.

This is the form the per-pivot drift assembly will add to the promoted Stage-79 left
bound under the exact `Delta = Delta_L + Delta_R` decomposition.
-/
theorem neg_singletonRate_correctedWeight_div_le_acceptedRightWeightedContribution
    {n : ℕ} (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    {alpha : ℝ} (halpha : 0 < alpha)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    -((law.oneBitMass / (n : ℝ)) *
        (law.correctedPotentialWeight alpha w i / alpha)) ≤
      law.acceptedRightWeightedContribution
        (acceptedLeftmostZeroEvent w x i)
        (law.correctedPotentialWeight alpha w) x
        (law.correctedAnchor alpha w i) := by
  sorry

end StaticUnaryUnbiasedMutation
end ECRuntime
