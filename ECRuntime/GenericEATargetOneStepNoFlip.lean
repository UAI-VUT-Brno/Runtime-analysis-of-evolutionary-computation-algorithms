import ECRuntime.GenericEASelfLoopFromEmptyMask
import ECRuntime.LevelExitTail
import Mathlib

attribute [local instance] Classical.propDecidable

namespace ECRuntime

/-! P07: general finite-state one-step fixed-target survival lower bound for
standard-bit mutation, independent of the fitness function and target shape.
This is the operator-level version of the OneMax-specific Stage 307 claim. -/

/-- From any state outside the target, survival for one more iteration is at
least the probability of flipping no bits. -/
theorem proposed_onePlusOne_oneStepSurvival_ge_emptyMask
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fitness : BitString n → Real) (target : Set (BitString n))
    (x : BitString n) (hx : x ∉ target) :
    (1 - p) ^ n ≤
      finiteLevelSurvival (onePlusOneTransition p fitness) targetᶜ 1 x := by
  classical
  let P : TransitionMatrix (BitString n) := onePlusOneTransition p fitness
  let level : Set (BitString n) := targetᶜ
  have hP : IsStochastic P := onePlusOneTransition_stochastic hp0 hp1 fitness
  have hxlevel : x ∈ level := hx
  have hsingle :
      P x x * finiteLevelSurvival P level 0 x ≤
        ∑ y : BitString n, P x y * finiteLevelSurvival P level 0 y := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun y : BitString n =>
        P x y * finiteLevelSurvival P level 0 y)
      (fun y _ => mul_nonneg (hP.1 x y)
        (finiteLevelSurvival_nonneg P level hP 0 y))
      (Finset.mem_univ x)
  have hstay : P x x ≤ finiteLevelSurvival P level 1 x := by
    simpa [finiteLevelSurvival_succ_of_mem P level 0 x hxlevel,
      finiteLevelSurvival_zero_of_mem P level x hxlevel] using hsingle
  exact (proposed_onePlusOne_selfTransition_ge_emptyMask
    p hp0 hp1 fitness x).trans hstay

end ECRuntime
