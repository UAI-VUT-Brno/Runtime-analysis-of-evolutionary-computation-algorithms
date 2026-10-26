import ECRuntime.GenericCountableGeometricSurvival
import ECRuntime.ConstantExitRuntime
import Mathlib

attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
namespace ECRuntime

/-! P07. Connect the certified generic Markov self-loop geometric
survival inequality to the *actual* extended expected hitting time.
This is reusable beyond the standard-bit-mutation EA. -/

/-- A stochastic kernel's self-loop gives a lower bound on genuine
expected time to reach any target not containing the initial state. -/
theorem proposed_genericRuntimeSup_ge_selfLoopGeometric
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (target : Set α) (x : α) (hx : x ∉ target)
    (q : Real) (hq : 0 ≤ q) (hself : q ≤ P x x) :
    (∑' t : Nat, ENNReal.ofReal (q ^ t)) ≤ runtimeSup P target x := by
  classical
  rw [candidate_runtimeSup_eq_survival_tsum P target hP x]
  exact proposed_genericTotalSurvival_ge_selfLoopGeometric
    P hP targetᶜ x hx q hq hself

end ECRuntime
