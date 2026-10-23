import ECRuntime.RLSFiniteSurvivalCouponBound
import ECRuntime.RLSPositiveLinearCouponTail
import ECRuntime.RLSRandomStart
import ECRuntime.RLSLinearExact
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-!
Stage 135, promoted after the complete Round 22 eight-gate verification.
Average the conditional coupon-collector tail over all initial bit strings.
The expected initial zero count is n/2. This is a finite-n result aligned
with the random-initial-stake viewpoint of Doerr and Doerr (2013).
This is NOT the full distributional analysis in that paper.
-/

/-- Uniform-start RLS survival probability on a positive linear function
is bounded by the half-dimension coupon-collector envelope. -/
theorem proposed_rlsLinear_uniformInitial_couponSurvivalAverage
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (t : Nat) :
    (Finset.univ.sum (fun x : BitString n =>
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n))ᶜ t x)) /
      (2 : Real) ^ n ≤
        ((n : Real) / 2) * (1 - 1 / (n : Real)) ^ t := by
  classical
  let toggle : BitString n ≃ BitString n :=
    { toFun := fun x i => !(x i)
      invFun := fun x i => !(x i)
      left_inv := by
        intro x
        funext i
        simp only [Bool.not_not]
      right_inv := by
        intro x
        funext i
        simp only [Bool.not_not] }
  have htoggle (x : BitString n) :
      zeroCount x = oneCount (toggle x) := by
    unfold zeroCount oneCount
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hzeroOne :
      (∑ x : BitString n, (zeroCount x : Real)) =
        ∑ x : BitString n, (oneCount x : Real) := by
    refine Fintype.sum_equiv toggle
      (fun x : BitString n => (zeroCount x : Real))
      (fun x : BitString n => (oneCount x : Real)) ?_
    intro x
    exact congrArg (fun m : Nat => (m : Real)) (htoggle x)
  have htotal :
      (∑ x : BitString n,
        ((zeroCount x : Real) + (oneCount x : Real))) =
          (n : Real) * (2 : Real) ^ n := by
    calc
      _ = ∑ _x : BitString n, (n : Real) := by
        apply Finset.sum_congr rfl
        intro x _
        exact_mod_cast (by simpa only [add_comm] using
          (oneCount_add_zeroCount x) :
          zeroCount x + oneCount x = n)
      _ = (n : Real) * (2 : Real) ^ n := by
        simp; ring
  have hmean :
      (∑ x : BitString n, (zeroCount x : Real)) =
        ((n : Real) / 2) * (2 : Real) ^ n := by
    rw [Finset.sum_add_distrib, ← hzeroOne] at htotal
    linarith
  have hsum :
      (∑ x : BitString n,
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
            (linearFitness w))
          ({allOnes n} : Set (BitString n))ᶜ t x) ≤
      (∑ x : BitString n,
        (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t) := by
    apply Finset.sum_le_sum
    intro x _
    exact proposed_rlsLinear_finiteSurvival_couponBound hn w hw x t
  have hden : (0 : Real) < (2 : Real) ^ n := by positivity
  calc
    _ ≤ (∑ x : BitString n,
        (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t) /
        (2 : Real) ^ n :=
          div_le_div_of_nonneg_right hsum (le_of_lt hden)
    _ = ((n : Real) / 2) * (1 - 1 / (n : Real)) ^ t := by
      rw [← Finset.sum_mul, hmean]
      field_simp [ne_of_gt hden]

end ECRuntime
