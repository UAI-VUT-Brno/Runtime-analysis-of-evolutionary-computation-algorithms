import ECRuntime.AdaptiveLeadingOnesFiniteLevelOccupationPartition
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01. Finite-time uniform-initialization version of the true path-measure
level partition in approved Stage 304. No finite-horizon surrogate is used. -/

/-- The nonoptimal survival mass at a fixed time, averaged over every initial
bitstring, is exactly the finite sum of the corresponding exact-level masses. -/
theorem proposed_leadingOnesAdaptive_uniformNonoptimalTimeMass_eq_levelSum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (t : Nat) :
    (∑ x : BitString n,
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) < n}) =
      ∑ i : Fin n,
        ∑ x : BitString n,
          transitionTrajectoryMeasure
            (leadingOnesAdaptiveTransition rate)
            (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
            {path : Nat → BitString n |
              leadingOnes (transitionTrajectoryState x path t) = i.val} := by
  classical
  -- Stage 304 must be compiler-promoted before this theorem is elaborated.
  simp_rw [proposed_leadingOnesAdaptive_nonoptimalMass_eq_sumExactLevels
    n rate hrate]
  rw [Finset.sum_comm]

end ECRuntime
