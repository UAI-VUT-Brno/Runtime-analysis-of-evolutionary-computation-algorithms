import ECRuntime.StaticUnaryUnbiasedFirstZeroOccupationRenewal
import Mathlib

open ECRuntime
open ECRuntime.StaticUnaryUnbiasedMutation
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 102 integration: positive-mass first-zero entry and occupation

For superincreasing two-bit weights `(3,1)` and independent bit mutation
with `p=1/2`, the initial state `(0,1)` genuinely starts in level zero and
its entry mass is exactly one. The singleton mass is strictly positive,
so the Stage-102 horizon cap is instantiated in a nondegenerate case.
-/

section Stage102NonVacuityDecidability
attribute [local instance] Classical.propDecidable

example : ∃ (w : Fin 2 → Real) (x : BitString 2)
    (law : StaticUnaryUnbiasedMutation 2),
    SuperincreasingLinearWeights w ∧
      firstZeroAt x (0 : Fin 2) ∧
      0 < law.oneBitMass ∧
      0 < firstZeroEntryMass law w x (0 : Fin 2) 0 ∧
      (∑ t ∈ Finset.range 2,
        firstZeroOccupationMass law w x (0 : Fin 2) t) ≤
        ((2 : Real) / law.oneBitMass) *
          (∑ s ∈ Finset.range 2,
            firstZeroEntryMass law w x (0 : Fin 2) s) := by
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
  have hentry : 0 < firstZeroEntryMass law w x (0 : Fin 2) 0 := by
    change 0 < (if x ∈ firstZeroLevel (0 : Fin 2) then (1 : Real) else 0)
    simp [show x ∈ firstZeroLevel (0 : Fin 2) from hx]
  have hcap := firstZeroOccupationMass_horizon_le_entry_cap
    law w hw x (0 : Fin 2) 2 hp1
  exact ⟨w, x, law, hw, hx, hp1, hentry, hcap⟩

end Stage102NonVacuityDecidability

end ECRuntimeTest
