import ECRuntime.StaticUnaryUnbiasedLowestMaskBinVal
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 99 integration: non-vacuous superincreasing two-bit acceptance

An accepted non-singleton mask of positive original-law probability belongs
only to the minimum numerical pivot class. The rejected case is witnessed
by changing the parent pivot bit, not by an empty mutation event.
-/

/-- A positive-mass, accepted two-bit mutation with most-important pivot zero. -/
example : ∃ (mask : MutationMask 2),
    mask.card = 2 ∧
      mask ∈ StaticUnaryUnbiasedMutation.lowestMaskEvent (0 : Fin 2) ∧
      0 < mutationMaskWeight (1 / 2 : Real) mask ∧
      Accepts (linearFitness (fun k : Fin 2 => if k = 0 then 3 else 1))
        (fun k : Fin 2 => decide (k = (1 : Fin 2)))
        (mutateWithMask (fun k : Fin 2 => decide (k = (1 : Fin 2))) mask) := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : Real)
      (by norm_num) (by norm_num)
  let w : Fin 2 → Real := fun k => if k = 0 then 3 else 1
  let g : Fin 2 → Real := fun k => if k = 0 then 2 else 3
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let pair : MutationMask 2 := Finset.univ
  have hw : StaticUnaryUnbiasedMutation.SuperincreasingLinearWeights w := by
    constructor
    · intro k
      fin_cases k <;> norm_num [w]
    · intro k
      fin_cases k <;>
        norm_num [Finset.sum_filter, Fin.sum_univ_succ, w]
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
  let y : BitString 2 := fun _ => true
  have _hrejected :
      ¬ Accepts (linearFitness w) y (mutateWithMask y pair) := by
    intro haccept
    have hbad := (StaticUnaryUnbiasedMutation.superincreasing_accepts_iff_lowest_pivot_zero
      w hw y (0 : Fin 2) pair hpivot).1 haccept
    norm_num [y] at hbad
  have hmass : 0 < law.weight pair := by
    change 0 < mutationMaskWeight (1 / 2 : Real) pair
    norm_num [mutationMaskWeight, pair]
  have _hexact := law.accepted_lowestMaskEvent_mass_eq_if_zero
    w hw x (0 : Fin 2)
  have _hpartition := law.acceptedEventWeightedPotentialDrop_eq_sum_lowest_zeros
    w g hw x
  have hcount : pair.card = 2 := by simp [pair]
  exact ⟨pair, hcount, hpivot, hmass, hacc⟩

end ECRuntimeTest
