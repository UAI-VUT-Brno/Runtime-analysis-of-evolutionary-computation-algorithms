import ECRuntime.StaticUnaryUnbiasedFirstZeroWeightedVisits
import Mathlib

open ECRuntime
open ECRuntime.StaticUnaryUnbiasedMutation
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 103 promotion witness: concrete nonzero cumulative entry mass

For superincreasing `(3,1)` and genuine independent bit mutation at rate
`1/2`, the initial state `(0,1)` lies in first-zero level zero.  Its entry
mass at time zero is one, and the verified finite-horizon budget holds for
horizon two. This guards against an accidentally vacuous theorem premise.
-/

section Stage103NonVacuityDecidability
attribute [local instance] Classical.propDecidable

example : ∃ (w : Fin 2 → Real) (x : BitString 2)
    (law : StaticUnaryUnbiasedMutation 2),
    SuperincreasingLinearWeights w ∧
      0 < law.oneBitMass ∧
      firstZeroCumulativeEntryMass law w x (0 : Fin 2) 0 = 1 ∧
      firstZeroCumulativeEntryMass law w x (0 : Fin 2) 2 =
        firstZeroOccupationMass law w x (0 : Fin 2) 2 +
          law.maskEventMass (lowestMaskEvent (0 : Fin 2)) *
            (∑ t ∈ Finset.range 2,
              firstZeroOccupationMass law w x (0 : Fin 2) t) := by
  classical
  let w : Fin 2 → Real := fun k => if k = 0 then 3 else 1
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : Real)
      (by norm_num) (by norm_num)
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
  have hp1 : 0 < law.oneBitMass := by
    change 0 < (StaticUnaryUnbiasedMutation.independentBitLaw (n := 2)
      (1 / 2 : Real) (by norm_num) (by norm_num)).oneBitMass
    rw [StaticUnaryUnbiasedMutation.independentBitLaw_oneBitMass]
    norm_num
  have hentry : firstZeroCumulativeEntryMass law w x (0 : Fin 2) 0 = 1 := by
    simp [firstZeroCumulativeEntryMass, firstZeroEntryMass,
      show x ∈ firstZeroLevel (0 : Fin 2) from hx]
  have hbudget := firstZeroCumulativeEntryMass_eq_terminal_add_exit
    law w hw x (0 : Fin 2) 2
  exact ⟨w, x, law, hw, hp1, hentry, hbudget⟩

end Stage103NonVacuityDecidability
end ECRuntimeTest
