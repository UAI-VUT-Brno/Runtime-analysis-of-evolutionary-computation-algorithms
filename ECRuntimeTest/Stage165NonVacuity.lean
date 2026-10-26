import ECRuntime.RLSUniformInitialCouponSurvivalCapped
import Mathlib

namespace ECRuntimeTest
open ECRuntime

/-!
Certified Round 45 concrete witness for the approved Stage 165 statement.
The uniform-start survival mass has both the probability-one and geometric
upper bounds for a one-bit positive linear objective, for every budget.
-/
private theorem stage165_oneBit_survivalCapped (t : Nat) :
    (Finset.univ.sum (fun x : BitString 1 =>
       finiteLevelSurvival
         ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
            (by norm_num : 0 < (1 : Nat))).transition
            (linearFitness (fun _ : Fin 1 => (1 : Real))))
         ({allOnes 1} : Set (BitString 1))ᶜ t x)) /
       (2 : Real) ^ (1 : Nat) ≤ 1 ∧
    (Finset.univ.sum (fun x : BitString 1 =>
       finiteLevelSurvival
         ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
            (by norm_num : 0 < (1 : Nat))).transition
            (linearFitness (fun _ : Fin 1 => (1 : Real))))
         ({allOnes 1} : Set (BitString 1))ᶜ t x)) /
       (2 : Real) ^ (1 : Nat) ≤
         ((1 : Nat) : Real) / 2 *
           (1 - 1 / ((1 : Nat) : Real)) ^ t := by
  have hw : PositiveLinearWeights (fun _ : Fin 1 => (1 : Real)) := by
    intro i
    norm_num
  exact proposed_rlsLinear_uniformInitial_couponSurvivalCapped
    (by norm_num : 0 < (1 : Nat))
    (fun _ : Fin 1 => (1 : Real)) hw t

end ECRuntimeTest
