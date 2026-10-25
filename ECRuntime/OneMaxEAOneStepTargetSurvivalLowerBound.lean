import ECRuntime.OneMaxEAAdmissibleTargetRuntimeMonotonicity
import ECRuntime.RLSMonotoneFixedTargetSurvivalInvariant
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-! Stage 307 (P07 research). First nontrivial quantitative fixed-target
bound for standard-bit-mutation OneMax (1+1)-EA, beyond target inclusion.
An unchanged mutation mask supplies a concrete event keeping a subtarget
state outside the target for one step. -/

/-- If the initial OneMax zero count exceeds the threshold, one-step
survival is at least the probability that no bit was flipped. -/
theorem proposed_oneMaxEA_oneStepSurvival_ge_noFlipProbability
    {n : Nat} (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (r : Nat) (x : BitString n) (hx : r < oneMaxPotential x) :
    (1 - p) ^ n ≤
      finiteLevelSurvival
        (onePlusOneTransition p (oneMaxReal (n := n)))
        (oneMaxEAZeroAtMost (n := n) r)ᶜ 1 x := by
  classical
  let fitness := oneMaxReal (n := n)
  let P : TransitionMatrix (BitString n) := onePlusOneTransition p fitness
  let level : Set (BitString n) := (oneMaxEAZeroAtMost (n := n) r)ᶜ
  have hP : IsStochastic P := onePlusOneTransition_stochastic hp0 hp1 fitness
  have hxlevel : x ∈ level := by
    change ¬ oneMaxPotential x ≤ r
    exact Nat.not_le.mpr hx
  have hstay_nonneg (y : BitString n) :
      0 ≤ P x y * finiteLevelSurvival P level 0 y :=
    mul_nonneg (hP.1 x y)
      (finiteLevelSurvival_nonneg P level hP 0 y)
  have hsurvival : P x x ≤ finiteLevelSurvival P level 1 x := by
    have hsingle :
        P x x * finiteLevelSurvival P level 0 x ≤
          ∑ y : BitString n, P x y * finiteLevelSurvival P level 0 y :=
      Finset.single_le_sum
        (s := Finset.univ)
        (f := fun y : BitString n =>
          P x y * finiteLevelSurvival P level 0 y)
        (fun y _ => hstay_nonneg y)
        (Finset.mem_univ x)
    simpa [finiteLevelSurvival_succ_of_mem P level 0 x hxlevel,
      finiteLevelSurvival_zero_of_mem P level x hxlevel] using hsingle
  have hempty : selectedAfterMask fitness x (∅ : MutationMask n) = x := by
    simp [selectedAfterMask, elitistSelect]
  have hmask : mutationMaskWeight p (∅ : MutationMask n) ≤ P x x := by
    have hsingle :
        (if selectedAfterMask fitness x (∅ : MutationMask n) = x then
            mutationMaskWeight p (∅ : MutationMask n) else 0) ≤
          ∑ mask : MutationMask n,
            if selectedAfterMask fitness x mask = x then
              mutationMaskWeight p mask else 0 := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun mask : MutationMask n =>
          if selectedAfterMask fitness x mask = x then
            mutationMaskWeight p mask else 0)
        (fun mask _ => by
          split_ifs
          · exact mutationMaskWeight_nonneg hp0 hp1 mask
          · exact le_refl 0)
        (Finset.mem_univ (∅ : MutationMask n))
    simpa [P, onePlusOneTransition, pushforwardWeight, hempty] using hsingle
  have hweight : mutationMaskWeight p (∅ : MutationMask n) = (1-p)^n := by
    simp [mutationMaskWeight]
  calc
    (1-p)^n = mutationMaskWeight p (∅ : MutationMask n) := hweight.symm
    _ ≤ P x x := hmask
    _ ≤ finiteLevelSurvival P level 1 x := hsurvival

end ECRuntime
