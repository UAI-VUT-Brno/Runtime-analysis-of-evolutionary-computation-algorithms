import ECRuntime.StaticUnaryUnbiasedFirstZeroPathVisits
import Mathlib

open ECRuntime
open ECRuntime.StaticUnaryUnbiasedMutation
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 104 promotion witness: genuine visit probability and nonzero initial entry

For weights (3,1), independent mutation at rate 1/2 and initial state (0,1),
level zero is visited at time zero with probability one. The Stage 104
finite-path identity also holds at a nonzero horizon for this same model.
The independent mutation law has strictly positive singleton mass; the
superincreasing condition is exhibited concretely, not postulated vacuously.
-/

section Stage104NonVacuityDecidability
attribute [local instance] Classical.propDecidable

example : ∃ (w : Fin 2 → Real) (x : BitString 2)
    (law : StaticUnaryUnbiasedMutation 2),
    SuperincreasingLinearWeights w ∧
      0 < law.oneBitMass ∧
      firstZeroTrajectoryVisitMass law w x (0 : Fin 2) 0 = 1 ∧
      firstZeroTrajectoryVisitMass law w x (0 : Fin 2) 2 =
        firstZeroCumulativeEntryMass law w x (0 : Fin 2) 2 := by
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
  have hvisit0 : firstZeroTrajectoryVisitMass law w x (0 : Fin 2) 0 = 1 := by
    rw [firstZeroTrajectoryVisitMass_eq_cumulativeEntryMass law w hw x
      (0 : Fin 2) 0]
    exact hentry
  have hvisit2 := firstZeroTrajectoryVisitMass_eq_cumulativeEntryMass
    law w hw x (0 : Fin 2) 2
  exact ⟨w, x, law, hw, hp1, hvisit0, hvisit2⟩

end Stage104NonVacuityDecidability
end ECRuntimeTest
