import ECRuntime.RLSUniformInitialCouponTail
import ECRuntime.RLSFiniteSurvivalCouponBound
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LevelExitTail
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-!
Stage 165 -- approved statement, Round 45 proof repair and gate preparation.
The preceding certified tail estimate bounds survival by `(n/2)*(1-1/n)^t`.
The additional probability-one cap makes it useful even at small budgets.
This is a first bridge to distributional random-start results of the
Doerr--Doerr (2013) coupon collector paper, NOT its complete limit law.
This public module passed the Round 45 eight-gate compiler verification.
-/

/-- For a stochastic finite transition matrix, finite-horizon survival
is a sub-probability, uniformly bounded above by one. -/
private theorem stage165_survival_le_one
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (level : Set alpha)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) :
    ∀ t (x : alpha), finiteLevelSurvival P level t x ≤ 1 := by
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ level
      · simp [finiteLevelSurvival_zero_of_mem P level x hx]
      · simp [finiteLevelSurvival_zero_of_not_mem P level x hx]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvival_succ_of_mem P level t x hx]
        calc
          (∑ y, P x y * finiteLevelSurvival P level t y) ≤
              ∑ y, P x y * (1 : Real) := by
                apply Finset.sum_le_sum
                intro y _
                exact mul_le_mul_of_nonneg_left (ih y) (hP.1 x y)
          _ = 1 := by simpa using hP.2 x
      · rw [finiteLevelSurvival_succ_of_not_mem P level t x hx]
        norm_num

/-- A dimension-uniform finite-budget survival envelope, capped by the
probability bound one, for one-bit RLS with a uniformly random start.
No independence assumption is made between optimization steps. -/
theorem proposed_rlsLinear_uniformInitial_couponSurvivalCapped
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (t : Nat) :
    (Finset.univ.sum (fun x : BitString n =>
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n))ᶜ t x)) /
      (2 : Real) ^ n ≤ 1 ∧
    (Finset.univ.sum (fun x : BitString n =>
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n))ᶜ t x)) /
      (2 : Real) ^ n ≤
        ((n : Real) / 2) * (1 - 1 / (n : Real)) ^ t := by
  classical
  let P : TransitionMatrix (BitString n) :=
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
      (linearFitness w)
  have hP : IsStochastic P :=
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition_stochastic
      (linearFitness w)
  have hs (x : BitString n) :
      finiteLevelSurvival P ({allOnes n} : Set (BitString n))ᶜ t x ≤ 1 :=
    stage165_survival_le_one P ({allOnes n} : Set (BitString n))ᶜ hP t x
  have hcard :
      (∑ _x : BitString n, (1 : Real)) = (2 : Real) ^ n := by
    simp [BitString]
  have hsum :
      (Finset.univ.sum (fun x : BitString n =>
        finiteLevelSurvival P ({allOnes n} : Set (BitString n))ᶜ t x)) ≤
      (2 : Real) ^ n := by
    calc
      _ ≤ (∑ _x : BitString n, (1 : Real)) := by
        apply Finset.sum_le_sum
        intro x _
        exact hs x
      _ = _ := hcard
  have hden : (0 : Real) < (2 : Real) ^ n := by positivity
  constructor
  · change (Finset.univ.sum (fun x : BitString n =>
        finiteLevelSurvival P ({allOnes n} : Set (BitString n))ᶜ t x)) /
      (2 : Real) ^ n ≤ 1
    exact (div_le_iff₀ hden).2 (by simpa only [one_mul] using hsum)
  · exact proposed_rlsLinear_uniformInitial_couponSurvivalAverage hn w hw t

end ECRuntime
