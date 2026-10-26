import ECRuntime.AdaptiveLeadingOnesAbsorbingExpectation
import ECRuntime.LeadingOnesAdaptiveAbsorbingPath
import ECRuntime.LeadingOnesExpectedRuntimeAssembly
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
Stage 282 (P01, research candidate). This is the important remaining
infinite-trajectory measure bridge, rather than another identity about a
surrogate finite sum.  For an elitist LeadingOnes process, the state
is nonoptimal exactly until the first hitting time.  Showing this
pathwise and interchanging the time sum with the lintegral will identify
actual optimization time with the countable nonoptimal occupation mass.
The proof is deliberately open and this candidate must never be imported
into the certified root until the statement and its full proof pass gates.
-/

/-- Genuine adaptive fixed-initial expected first hitting time equals
the countable sum of exact-time nonoptimal occupation probabilities. -/
theorem proposed_leadingOnesAdaptive_fixedInitial_runtime_eq_nonoptimalOccupation
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) :
    (∫⁻ path : Nat → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x) =
    ∑' t : Nat,
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) < n} := by
  classical
  rw [proposed_leadingOnesAdaptive_fixedInitial_runtime_eq_survivalTsum
    n rate hrate x]
  apply tsum_congr
  intro t
  congr 1
  apply Set.ext
  intro path
  exact (proposed_leadingOnes_lt_dim_iff_not_target
    (transitionTrajectoryState x path t)).symm

end ECRuntime
