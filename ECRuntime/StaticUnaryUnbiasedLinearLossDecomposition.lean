import ECRuntime.StaticUnaryUnbiasedLinearAcceptedEvents
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Accepted-event left/right loss decomposition for static unary-unbiased linear functions

The published upper-bound proof splits the potential change inside a pivot event `A_i`
into a positive `L(i)` contribution and a negative `R(i)` contribution.  This repository
uses the reversed convention: positive linear functions are maximized toward `allOnes`
and coordinate `0` is the most important coordinate.

This module keeps the anchor coordinate abstract.  For an anchor `k`, currently-one
coordinates are partitioned into

* `acceptedLeftRegion x k`: coordinates at least as important as `k` (`j.val <= k.val`),
* `acceptedRightRegion x k`: coordinates less important than `k` (`k.val < j.val`).

The module proves an exact pointwise decomposition of every accepted weighted-error drop
through these two regions.  It also packages the Stage-74 corrected second-coordinate
bound into the weighted `R`-loss proxy

`sum_{j in R} g_j * Pr[j flips | A_i]`,

bounded coordinatewise by the factorial-moment coefficient
`E[K(K-1)] / (p₁ (n-1))`.

The recursive literature-specific construction of `gamma`, `g`, and the anchor `k(i)`
is deliberately postponed.  No mean-only `chi/(n-1)` estimate is used.
-/

/-- Currently-one coordinates at least as important as the chosen anchor. -/
def acceptedLeftRegion {n : ℕ} (x : BitString n) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = true ∧ j.val ≤ k.val)

/-- Currently-one coordinates less important than the chosen anchor. -/
def acceptedRightRegion {n : ℕ} (x : BitString n) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => x j = true ∧ k.val < j.val)

@[simp] theorem mem_acceptedLeftRegion_iff {n : ℕ}
    (x : BitString n) (k j : Fin n) :
    j ∈ acceptedLeftRegion x k ↔ x j = true ∧ j.val ≤ k.val := by
  simp [acceptedLeftRegion]

@[simp] theorem mem_acceptedRightRegion_iff {n : ℕ}
    (x : BitString n) (k j : Fin n) :
    j ∈ acceptedRightRegion x k ↔ x j = true ∧ k.val < j.val := by
  simp [acceptedRightRegion]

/-- The left and right currently-one regions are disjoint. -/
theorem acceptedLeftRegion_disjoint_rightRegion {n : ℕ}
    (x : BitString n) (k : Fin n) :
    Disjoint (acceptedLeftRegion x k) (acceptedRightRegion x k) := by
  rw [Finset.disjoint_left]
  intro j hjL hjR
  have hL := (mem_acceptedLeftRegion_iff x k j).1 hjL
  have hR := (mem_acceptedRightRegion_iff x k j).1 hjR
  omega

/-- Positive potential gain from zero-to-one flips. -/
noncomputable def acceptedGain {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) : ℝ :=
  ∑ j ∈ zeroToOneFlips x mask, g j

/-- Potential loss from one-to-zero flips in the left region. -/
noncomputable def acceptedLeftLoss {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (k : Fin n) : ℝ :=
  ∑ j : Fin n,
    if j ∈ mask ∧ x j = true ∧ j.val ≤ k.val then g j else 0

/-- Potential loss from one-to-zero flips in the right region. -/
noncomputable def acceptedRightLoss {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (k : Fin n) : ℝ :=
  ∑ j : Fin n,
    if j ∈ mask ∧ x j = true ∧ k.val < j.val then g j else 0

/-- Literature-style `L` contribution in the repository convention. -/
noncomputable def acceptedLeftDelta {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (k : Fin n) : ℝ :=
  acceptedGain g x mask - acceptedLeftLoss g x mask k

/-- Literature-style `R` contribution in the repository convention. -/
noncomputable def acceptedRightDelta {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (k : Fin n) : ℝ :=
  -acceptedRightLoss g x mask k

/-- One-to-zero loss splits exactly across the left and right regions. -/
theorem oneToZero_sum_eq_acceptedLeftLoss_add_acceptedRightLoss {n : ℕ}
    (g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (k : Fin n) :
    (∑ j ∈ oneToZeroFlips x mask, g j) =
      acceptedLeftLoss g x mask k + acceptedRightLoss g x mask k := by
  classical
  unfold oneToZeroFlips acceptedLeftLoss acceptedRightLoss
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hm : j ∈ mask
  · cases hx : x j with
    | false =>
        simp [hm]
    | true =>
        by_cases hle : j.val ≤ k.val
        · have hnlt : ¬ k.val < j.val := Nat.not_lt_of_ge hle
          simp [hm, hle, hnlt]
        · have hlt : k.val < j.val := Nat.lt_of_not_ge hle
          simp [hm, hle, hlt]
  · simp [hm]

/-- Exact accepted weighted-error drop as `L + R` for any anchor coordinate. -/
theorem linearErrorPotential_selected_drop_eq_leftDelta_add_rightDelta_of_accepts {n : ℕ}
    (w g : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (k : Fin n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) =
      acceptedLeftDelta g x mask k + acceptedRightDelta g x mask k := by
  rw [linearErrorPotential_selected_drop_of_accepts w g x mask hacc]
  rw [flipContribution_sum_eq_flip_sums]
  rw [oneToZero_sum_eq_acceptedLeftLoss_add_acceptedRightLoss]
  unfold acceptedLeftDelta acceptedRightDelta acceptedGain
  ring

/-- The exact `L + R` decomposition specialized to a concrete accepted pivot event. -/
theorem acceptedLeftmostZeroEvent_selected_drop_eq_leftDelta_add_rightDelta {n : ℕ}
    (w g : Fin n → ℝ) (x : BitString n) (i k : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) =
      acceptedLeftDelta g x mask k + acceptedRightDelta g x mask k := by
  exact linearErrorPotential_selected_drop_eq_leftDelta_add_rightDelta_of_accepts
    w g x mask k (acceptedLeftmostZeroEvent_accepts w x i mask hmask)

/--
Weighted conditional right-loss proxy for a finite mask event.

For a genuine probability event this is exactly the sum over right-region coordinates
of `g_j * Pr[j flips | event]` whenever the event mass is positive.
-/
noncomputable def acceptedRightConditionalLossProxy {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (g : Fin n → ℝ) (x : BitString n) (k : Fin n) : ℝ :=
  ∑ j ∈ acceptedRightRegion x k,
    g j * (law.maskEventMass (secondCoordinateSlice event j) /
      law.maskEventMass event)

/--
Stage-74 summed over the whole right region: every nonnegative right-region coefficient
is charged by at most the corrected factorial-moment conditional coefficient.
-/
theorem acceptedLeftmostZeroEvent_rightConditionalLossProxy_le {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false)
    (g : Fin n → ℝ) (hg : ∀ j, 0 ≤ g j) (k : Fin n) :
    law.acceptedRightConditionalLossProxy
        (acceptedLeftmostZeroEvent w x i) g x k ≤
      ∑ j ∈ acceptedRightRegion x k,
        g j * (law.secondFactorialRadiusMoment /
          (law.oneBitMass * ((n - 1 : ℕ) : ℝ))) := by
  unfold acceptedRightConditionalLossProxy
  apply Finset.sum_le_sum
  intro j hj
  have hjdata := (mem_acceptedRightRegion_iff x k j).1 hj
  have hjtrue : x j = true := hjdata.1
  have hij : i ≠ j := by
    intro hijEq
    subst j
    rw [hi] at hjtrue
    simp at hjtrue
  have hcond := law.acceptedLeftmostZeroEvent_secondCoordinateSlice_bound
    hn hp1 w hw x i j hi hij
  exact mul_le_mul_of_nonneg_left hcond (hg j)

end StaticUnaryUnbiasedMutation
end ECRuntime
