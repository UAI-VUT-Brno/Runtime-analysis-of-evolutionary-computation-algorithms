import ECRuntime.LeadingOnesBoundaryEventualCrossing
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesBoundaryRuntimeToAlmostSure
import ECRuntime.AdaptiveLeadingOnesBoundaryFiniteRuntime
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
Stage 225 (NEW, unapproved): the outstanding adaptive a.s. boundary
crossing result. The current statement is a legitimate mathematical
obligation, not an assumption. A finite-state uniform positive-progress
argument or adaptive harmonic-fitness-level theorem must close the proof.
Its presence as a pending `sorry` NEVER authorizes promotion.
-/

/-- Every boundary is crossed almost surely when all attainable
nonterminal LeadingOnes levels use a mutation rate strictly between zero
and one, even when the rate depends on the current level. -/
theorem proposed_leadingOnesAdaptive_eventuallyCrossesBoundary_ae
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat -> Real)
    (hrate : ∀ j : Nat, j ≤ n -> 0 < rate j ∧ rate j < 1)
    (i : Fin n) (x : BitString n) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate
        (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩))
      x (leadingOnesEventuallyCrossesBoundarySet i x) = 1 := by
  exact proposed_leadingOnesAdaptive_boundaryAE_of_runtimeFinite
    rate (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)
    i x (proposed_leadingOnesAdaptive_boundaryRuntime_ne_top rate hrate i x)

end ECRuntime
