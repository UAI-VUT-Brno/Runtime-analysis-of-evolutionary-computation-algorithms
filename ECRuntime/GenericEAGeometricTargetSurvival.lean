import ECRuntime.GenericEATargetOneStepNoFlip
import Mathlib

attribute [local instance] Classical.propDecidable

namespace ECRuntime

/-! P07: a target-independent multi-step quantitative survival bound for
standard-bit mutation, valid for an arbitrary objective and arbitrary target. -/

/-- An elitist `(1+1)` EA can survive at least by making no mutation at
every step, from any starting point outside the target. -/
theorem proposed_onePlusOne_anyTargetSurvival_ge_noFlipPower
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (fitness : BitString n → Real) (target : Set (BitString n))
    (x : BitString n) (hx : x ∉ target) (t : Nat) :
    ((1 - p) ^ n) ^ t ≤
      finiteLevelSurvival (onePlusOneTransition p fitness) targetᶜ t x := by
  classical
  let P : TransitionMatrix (BitString n) := onePlusOneTransition p fitness
  let level : Set (BitString n) := targetᶜ
  have hP : IsStochastic P := onePlusOneTransition_stochastic hp0 hp1 fitness
  have hxlevel : x ∈ level := hx
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
            ∑ y : BitString n, P x y * finiteLevelSurvival P level t y := by
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
