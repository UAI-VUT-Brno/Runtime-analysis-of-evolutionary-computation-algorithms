import ECRuntime.StaticUnaryUnbiasedFirstZeroResidence
import Mathlib

open ECRuntime
open ECRuntime.StaticUnaryUnbiasedMutation
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 101 integration: an occupied first-zero level with genuine exit

The first-zero residence hypotheses are satisfied on two-bit BinVal with
weights (3,1). A two-bit mutation has strictly positive probability, and
its minimum pivot at bit zero causes the selected transition to exit the
level. The compiler-promoted exact two-step geometric survival theorem is
instantiated at this nondegenerate state.
-/

section Stage101NonVacuityDecidability
attribute [local instance] Classical.propDecidable

example : ∃ (w : Fin 2 → Real) (x : BitString 2)
    (law : StaticUnaryUnbiasedMutation 2) (mask : MutationMask 2),
    SuperincreasingLinearWeights w ∧
      firstZeroAt x (0 : Fin 2) ∧
      mask ∈ lowestMaskEvent (0 : Fin 2) ∧
      0 < law.weight mask ∧
      selectedAfterMask (linearFitness w) x mask ∉ firstZeroLevel (0 : Fin 2) ∧
      finiteLevelSurvival (law.transition (linearFitness w))
          (firstZeroLevel (0 : Fin 2)) 2 x =
        (1 - law.maskEventMass (lowestMaskEvent (0 : Fin 2))) ^ 2 := by
  classical
  let w : Fin 2 → Real := fun k => if k = 0 then 3 else 1
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : Real)
      (by norm_num) (by norm_num)
  let mask : MutationMask 2 := Finset.univ
  have hw : SuperincreasingLinearWeights w := by
    constructor
    · intro k
      fin_cases k <;> norm_num [w]
    · intro k
      fin_cases k <;> norm_num [Finset.sum_filter, Fin.sum_univ_succ, w]
  have hx : firstZeroAt x (0 : Fin 2) := by
    constructor
    · intro j hj
      have hnot : ¬ j.val < (0 : Fin 2).val := by omega
      exact False.elim (hnot hj)
    · decide
  have hmask : mask ∈ lowestMaskEvent (0 : Fin 2) := by
    apply (mem_lowestMaskEvent_iff (0 : Fin 2) mask).2
    constructor
    · simp [mask]
    · intro j hj
      exact Nat.zero_le _
  have hpos : 0 < law.weight mask := by
    change 0 < mutationMaskWeight (1 / 2 : Real) mask
    norm_num [mutationMaskWeight, mask]
  have hexit := (firstZeroAt_selected_exits_iff w hw x
    (0 : Fin 2) hx mask).2 hmask
  have hresidence := firstZeroAt_finiteLevelSurvival_eq_pow law w hw x
    (0 : Fin 2) hx 2
  exact ⟨w, x, law, mask, hw, hx, hmask, hpos, hexit, hresidence⟩

end Stage101NonVacuityDecidability

end ECRuntimeTest
