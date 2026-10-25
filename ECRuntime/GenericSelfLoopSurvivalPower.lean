import ECRuntime.LevelExitTail
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P07. A purely stochastic fixed-target survival result, separating
operator self-loop mass from the choice of objective and target. -/

/-- A statewise lower bound on the self-loop probability guarantees
geometric survival for any target that does not contain the start state. -/
theorem proposed_finiteLevelSurvival_ge_selfLoopPower
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (level : Set α) [DecidablePred (fun y : α => y ∈ level)]
    (x : α) (hx : x ∈ level)
    (q : Real) (hq : 0 ≤ q) (hself : q ≤ P x x) (t : Nat) :
    q ^ t ≤ finiteLevelSurvival P level t x := by
  classical
  induction t with
  | zero =>
      simp [finiteLevelSurvival_zero_of_mem P level x hx]
  | succ t ih =>
      have hsingle :
          P x x * finiteLevelSurvival P level t x ≤
            ∑ y : α, P x y * finiteLevelSurvival P level t y := by
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun y : α => P x y * finiteLevelSurvival P level t y)
          (fun y _ => mul_nonneg (hP.1 x y)
            (finiteLevelSurvival_nonneg P level hP t y))
          (Finset.mem_univ x)
      calc
        q ^ (t + 1) = q * q ^ t := by rw [pow_succ]; ring
        _ ≤ P x x * finiteLevelSurvival P level t x :=
          mul_le_mul hself ih (pow_nonneg hq t) (hP.1 x x)
        _ ≤ finiteLevelSurvival P level (t + 1) x := by
          simpa only [finiteLevelSurvival_succ_of_mem P level t x hx]
            using hsingle

end ECRuntime
