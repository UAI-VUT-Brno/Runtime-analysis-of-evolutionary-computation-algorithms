import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.LeadingOnesTrajectoryMonotonicity
import Mathlib

namespace ECRuntime

/-!
# Stage 171 — approved candidate: adaptive LeadingOnes support

Source direction: Böttcher--Doerr--Neumann (2010), optimal fitness-dependent
mutation rates on LeadingOnes. The promoted Stage 168 kernel is stochastic and
has exact one-level geometric survival. The next probabilistic task is to
prove uniform visitation probabilities at level entry under adaptive rates.
This elementary kernel-support result allows the existing generic trajectory
monotonicity theorem to be reused for those occupation arguments.

The statement was approved by the user after successful statement elaboration.
Promotion still requires an admission-free proof, a transitive-axiom check,
and all eight official verifier gates.
-/

/-- Every supported adaptive (1+1)-EA step weakly improves LeadingOnes,
regardless of the state-dependent choice of rate. The statement concerns
support, not a distributional independence claim or the adaptive optimum. -/
theorem proposed_leadingOnesAdaptive_potentialNonincreasingSupport
    {n : ℕ} (rate : ℕ → ℝ) :
    HasPotentialNonincreasingTransitionSupport
      (leadingOnesAdaptiveTransition (n := n) rate)
      (leadingOnesPotential (n := n)) := by
  intro x y hxy
  exact
    onePlusOneTransition_leadingOnes_hasPotentialNonincreasingTransitionSupport
      (rate (leadingOnes x)) x y hxy

end ECRuntime
