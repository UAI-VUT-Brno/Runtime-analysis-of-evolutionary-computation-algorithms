import ECRuntime.StaticUnaryUnbiasedFirstZeroUnrestrictedRuntime
import Mathlib

namespace ECRuntimeTest
open ECRuntime
open ECRuntime.StaticUnaryUnbiasedMutation

/-!
# A nontrivial unrestricted-runtime witness

A concrete two-bit superincreasing objective, a nonoptimal starting point,
and a genuine independent-bit mutation law with positive singleton mass
satisfy the hypotheses of the unrestricted expected-runtime bound.
The example therefore does not discharge the theorem using an empty class
of instances or an already optimal initial state.
-/

section UnrestrictedRuntimeNonVacuityDecidability
attribute [local instance] Classical.propDecidable

/-- A concrete nonoptimal instance of the proved infinite-horizon hazard cap. -/
example : ∃ (w : Fin 2 → Real) (x : BitString 2)
    (law : StaticUnaryUnbiasedMutation 2),
    SuperincreasingLinearWeights w ∧
      0 < law.oneBitMass ∧
      ¬ firstZeroAllOnes x ∧
      runtimeSup (law.transition (linearFitness w))
        (firstZeroOptimalSet (n := 2)) x ≤
        ENNReal.ofReal
          (∑ i : Fin 2, 1 / law.maskEventMass (lowestMaskEvent i)) := by
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
  have hcap := firstZeroRuntimeSup_le_hazardCap law w hw x hp1
  exact ⟨w, x, law, hw, hp1, hx, hcap⟩

end UnrestrictedRuntimeNonVacuityDecidability
end ECRuntimeTest
