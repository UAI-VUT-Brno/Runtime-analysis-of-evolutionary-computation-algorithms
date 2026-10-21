import ECRuntime.StaticUnaryUnbiasedFirstZeroFiniteRuntime
import Mathlib

namespace ECRuntimeTest
open ECRuntime
open ECRuntime.StaticUnaryUnbiasedMutation

/-!
# Stage 105 non-vacuity regression

The concrete superincreasing two-bit objective and independent mutation law
satisfy every hypothesis of the Stage 105 finite-horizon cap. The initial
point is deliberately nonoptimal; the regression is not an all-ones witness.
-/

section Stage105NonVacuityDecidability
attribute [local instance] Classical.propDecidable

/-- A concrete law, objective and nonoptimal point satisfy the Stage 105
hazard-cap theorem at a positive horizon. -/
example : ∃ (w : Fin 2 → Real) (x : BitString 2)
    (law : StaticUnaryUnbiasedMutation 2),
    SuperincreasingLinearWeights w ∧
      0 < law.oneBitMass ∧
      ¬ firstZeroAllOnes x ∧
      firstZeroFiniteRuntimeMass law w x 1 ≤
        ∑ i : Fin 2, 1 / law.maskEventMass (lowestMaskEvent i) := by
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
  have hp1 : 0 < law.oneBitMass := by
    change 0 < (StaticUnaryUnbiasedMutation.independentBitLaw (n := 2)
      (1 / 2 : Real) (by norm_num) (by norm_num)).oneBitMass
    rw [StaticUnaryUnbiasedMutation.independentBitLaw_oneBitMass]
    norm_num
  have hx : ¬ firstZeroAllOnes x := by
    intro hall
    have hzero : x (0 : Fin 2) = true := hall 0
    have hfalse : x (0 : Fin 2) = false := by decide
    simp [hfalse] at hzero
  have hcap := firstZeroFiniteRuntimeMass_le_hazardCap
    law w hw x 1 hp1
  exact ⟨w, x, law, hw, hp1, hx, hcap⟩

end Stage105NonVacuityDecidability
end ECRuntimeTest
