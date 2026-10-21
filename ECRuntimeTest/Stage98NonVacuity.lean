import ECRuntime.StaticUnaryUnbiasedHighestMaskPivot
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 98 integration: positive-mass accepted nonsingleton mask

The maximum-index partition has a genuine nonempty class even for a
nontrivial elitist accepted event. This test also exercises both the exact
radius-charge theorem and its accepted-subevent inequality in the actual
operator API. All probabilities are under the unconditioned mutation law.
-/

/-- An inhabited accepted two-bit event with strictly positive probability,
assigned to the unique maximum numerical pivot. -/
example : ∃ (mask : MutationMask 2),
    mask.card = 2 ∧
      mask ∈ StaticUnaryUnbiasedMutation.highestMaskEvent (1 : Fin 2) ∧
      0 < mutationMaskWeight (1 / 2 : Real) mask ∧
      0 < (mask.card : Real) * mutationMaskWeight (1 / 2 : Real) mask ∧
      Accepts (linearFitness (fun k : Fin 2 => if k = 0 then 2 else 1))
        (fun k : Fin 2 => decide (k = (1 : Fin 2)))
        (mutateWithMask (fun k : Fin 2 => decide (k = (1 : Fin 2))) mask) := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : Real)
      (by norm_num) (by norm_num)
  let w : Fin 2 → Real := fun k => if k = 0 then 2 else 1
  let g : Fin 2 → Real := fun k => if k = 0 then 2 else 3
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let pair : MutationMask 2 := Finset.univ
  have hhigh : pair ∈
      StaticUnaryUnbiasedMutation.highestMaskEvent (1 : Fin 2) := by
    apply (StaticUnaryUnbiasedMutation.mem_highestMaskEvent_iff
      (1 : Fin 2) pair).2
    constructor
    · simp [pair]
    · intro j _
      fin_cases j <;> norm_num
  have hmass : 0 < mutationMaskWeight (1 / 2 : Real) pair := by
    norm_num [mutationMaskWeight, pair]
  have hzset : zeroToOneFlips x pair = ({0} : Finset (Fin 2)) := by
    ext k
    fin_cases k <;> decide
  have hoset : oneToZeroFlips x pair = ({1} : Finset (Fin 2)) := by
    ext k
    fin_cases k <;> decide
  have hacc : Accepts (linearFitness w) x (mutateWithMask x pair) := by
    apply (accepts_linearFitness_iff_flip_sums w x pair).2
    rw [hoset, hzset]
    norm_num [w]
  have hcount : pair.card = 2 := by simp [pair]
  have hpositiveCharge :
      (0 : Real) < (pair.card : Real) * mutationMaskWeight (1 / 2 : Real) pair := by
    rw [hcount]
    exact mul_pos (by norm_num) hmass
  have _hpart :=
    law.sum_highestMaskEvent_radius_charge_eq_meanRadius
  have _hsub :=
    law.sum_highestMaskEvent_restricted_radius_charge_le_meanRadius
      ({pair} : Finset (MutationMask 2))
  have _hsigned :=
    law.acceptedEventWeightedPotentialDrop_eq_sum_highestMaskEvent
      ({pair} : Finset (MutationMask 2)) w g x
  exact ⟨pair, hcount, hhigh, hmass, hpositiveCharge, hacc⟩

end ECRuntimeTest
