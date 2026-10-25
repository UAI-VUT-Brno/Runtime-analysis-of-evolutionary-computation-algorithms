import ECRuntime.GenericEASelfLoopFromEmptyMask
import ECRuntime.OneMaxEAOneStepTargetSurvivalLowerBound
import Mathlib

namespace ECRuntime

/-! P07: extend the one-step quantitative lower bound to all fixed horizons.
This requires a verified Markov recursion that keeps the unchanged-parent
branch separate. The exact bound is recorded for the next proof cycle. -/

/-- If the parent has not reached the OneMax target, surviving `t` rounds
has probability at least the event of making no flips in all `t` rounds. -/
theorem proposed_oneMaxEA_survival_ge_noFlipPower
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Nat) (x : BitString n) (hx : r < oneMaxPotential x) (t : Nat) :
    ((1 - p) ^ n) ^ t ≤
      finiteLevelSurvival
        (onePlusOneTransition p (oneMaxReal (n := n)))
        (oneMaxEAZeroAtMost (n := n) r)ᶜ t x := by
  classical
  let fitness := oneMaxReal (n := n)
  let P : TransitionMatrix (BitString n) := onePlusOneTransition p fitness
  let level : Set (BitString n) := (oneMaxEAZeroAtMost (n := n) r)ᶜ
  have hP : IsStochastic P := onePlusOneTransition_stochastic hp0 hp1 fitness
  have hxlevel : x ∈ level := by
    change ¬ oneMaxPotential x ≤ r
    exact Nat.not_le.mpr hx
  have hq : 0 ≤ (1 - p) ^ n := pow_nonneg (sub_nonneg.mpr hp1) n
  have hself : (1 - p) ^ n ≤ P x x :=
    proposed_onePlusOne_selfTransition_ge_emptyMask p hp0 hp1 fitness x
  change ((1 - p) ^ n) ^ t ≤ finiteLevelSurvival P level t x
  induction t with
  | zero =>
      simp [finiteLevelSurvival_zero_of_mem P level x hxlevel]
  | succ t ih =>
      have hsingle :
          P x x * finiteLevelSurvival P level t x ≤
            ∑ y : BitString n,
              P x y * finiteLevelSurvival P level t y := by
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun y : BitString n =>
            P x y * finiteLevelSurvival P level t y)
          (fun y _ => mul_nonneg (hP.1 x y)
            (finiteLevelSurvival_nonneg P level hP t y))
          (Finset.mem_univ x)
      calc
        ((1 - p) ^ n) ^ (t + 1) =
            ((1 - p) ^ n) * (((1 - p) ^ n) ^ t) := by ring
        _ ≤ P x x * finiteLevelSurvival P level t x :=
          mul_le_mul hself ih (pow_nonneg hq t) (hP.1 x x)
        _ ≤ finiteLevelSurvival P level (t + 1) x := by
          simpa only [finiteLevelSurvival_succ_of_mem P level t x hxlevel]
            using hsingle

end ECRuntime
