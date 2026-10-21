import ECRuntime.StaticUnaryUnbiasedLowestPivotTailCharge
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 100 integration: a real positive-probability non-pivot charge

An accepted two-bit mutation has one minimum pivot and one genuinely
flipped non-pivot bit. Its non-pivot cost is positive under the original,
normalized mutation law; it is neither an empty mask nor a zero-weight
potential. The Stage 100 global drift theorem is instantiated at the
same superincreasing objective and nonnegative bounded potential.
-/

example : ∃ mask : MutationMask 2,
    mask.card = 2 /\
      mask ∈ StaticUnaryUnbiasedMutation.lowestMaskEvent (0 : Fin 2) /\
      0 < mutationMaskWeight (1 / 2 : Real) mask /\
      0 < mutationMaskWeight (1 / 2 : Real) mask *
        (∑ _j ∈ mask.erase (0 : Fin 2), (1 : Real)) /\
      Accepts (linearFitness (fun k : Fin 2 => if k = 0 then 3 else 1))
        (fun k : Fin 2 => decide (k = (1 : Fin 2)))
        (mutateWithMask (fun k : Fin 2 => decide (k = (1 : Fin 2))) mask) := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : Real)
      (by norm_num) (by norm_num)
  let w : Fin 2 -> Real := fun k => if k = 0 then 3 else 1
  let g : Fin 2 -> Real := fun _ => 1
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let pair : MutationMask 2 := Finset.univ
  have hw : StaticUnaryUnbiasedMutation.SuperincreasingLinearWeights w := by
    constructor
    · intro k
      fin_cases k <;> norm_num [w]
    · intro k
      fin_cases k <;> norm_num [Finset.sum_filter, Fin.sum_univ_succ, w]
  have hpivot : pair ∈
      StaticUnaryUnbiasedMutation.lowestMaskEvent (0 : Fin 2) := by
    apply (StaticUnaryUnbiasedMutation.mem_lowestMaskEvent_iff
      (0 : Fin 2) pair).2
    constructor
    · simp [pair]
    · intro k _
      fin_cases k <;> norm_num
  have hzero : x (0 : Fin 2) = false := by decide
  have hacc : Accepts (linearFitness w) x (mutateWithMask x pair) :=
    (StaticUnaryUnbiasedMutation.superincreasing_accepts_iff_lowest_pivot_zero
      w hw x (0 : Fin 2) pair hpivot).2 hzero
  have hmass : 0 < law.weight pair := by
    change 0 < mutationMaskWeight (1 / 2 : Real) pair
    norm_num [mutationMaskWeight, pair]
  have htail : pair.erase (0 : Fin 2) = {(1 : Fin 2)} := by
    decide
  have hcharge : 0 < law.weight pair *
      (∑ j ∈ pair.erase (0 : Fin 2), g j) := by
    have hsum : (∑ j ∈ pair.erase (0 : Fin 2), g j) = 1 := by
      rw [htail]
      simp [g]
    rw [hsum]
    simpa using hmass
  have hg : ∀ j, 0 <= g j /\ g j <= (1 : Real) := by
    intro j
    norm_num [g]
  have _hfirstMoment :=
    law.sum_lowestPivotExcessRadiusCharge_add_nonempty_eq_meanRadius
  have _hmain :=
    law.acceptedEventWeightedPotentialDrop_ge_pivotCredit_sub_cap_meanRadius
      w g hw 1 (by norm_num) hg x
  have hcard : pair.card = 2 := by simp [pair]
  exact ⟨pair, hcard, hpivot, hmass, hcharge, hacc⟩

end ECRuntimeTest
