import ECRuntime.AdaptiveLeadingOnesFirstCrossingFixedInitialAverage
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 224 (NEW, unapproved): nonnegativity of the statewise adaptive
first-crossing weights. The theorem is kept independent of the
almost-sure eventual-crossing normalization, but supplies the positivity
needed for extended-real countable sums and finite/infinite interchange.
-/

/-- Every fixed-initial-state finite first-crossing mass is nonnegative
under an admissible adaptive mutation schedule. -/
theorem proposed_leadingOnesAdaptive_fixedInitialFirstCrossingMass_nonneg
    {n t : Nat} (rate : Nat -> Real)
    (hrate : ∀ j : Nat, j ≤ n -> 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (x : BitString n) :
    0 ≤ leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x := by
  classical
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  have hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  unfold leadingOnesAdaptiveFixedInitialFirstCrossingMass
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hcross : path ∈ leadingOnesFiniteFirstCrossingSet i x t
  · simp only [hcross, if_true]
    exact finiteTrajectoryWeight_nonneg P hP t x path
  · simp [hcross]

end ECRuntime
