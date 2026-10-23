import ECRuntime.UnrestrictedRuntime
import ECRuntime.LevelExitTail
import ECRuntime.FiniteRuntimeSurvivalSupport
import Mathlib

open Filter
namespace ECRuntime

/-!
Stage 133: approved statement, provisional public integration.
For finite-state stochastic kernels, finite expected first-hitting time implies
that survival at each starting state tends to zero. This is the missing
logical step for the general finite-mean Bellman theorem (Stage 127). Do not
assume any geometric tail: it is stronger than the stated hypothesis.
-/

/-- Finite unrestricted expected hitting time forces the finite-horizon
non-target survival mass to vanish, without a geometric assumption. -/
theorem proposed_finiteSurvival_tendsto_zero_of_finite_runtime
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P)
    (hFinite : ∀ x, runtimeSup P target x ≠ ⊤)
    (x : alpha) :
    Tendsto (fun t : Nat => finiteLevelSurvival P targetᶜ t x)
      atTop (nhds (0 : Real)) := by
  exact candidate_finiteSurvival_tendsto_zero_of_finite_runtime
    P target hP hFinite x

end ECRuntime
