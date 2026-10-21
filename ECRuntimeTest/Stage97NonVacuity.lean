import ECRuntime.StaticUnaryUnbiasedResidualLossBudget
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 97 root-integration regression: genuinely positive residual loss

At parent 01, the 2-bit mutation is accepted under weights (2,1) but has
potential-weight drop -1 under (2,3). At scale=1, residual weights are
(0,2), so the lost one-bit incurs strictly positive residual loss.
The positive-probability mask is a real member of an accepted event.

This is a NEW, UNVERIFIED regression test; no certified theorem is changed.
-/

/-- A genuine non-singleton accepted mutation satisfies the Stage 97
coefficient premises and incurs positive coordinatewise residual loss. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : Real)
      (by norm_num) (by norm_num)
  let w : Fin 2 -> Real := fun k => if k = 0 then 2 else 1
  let g : Fin 2 -> Real := fun k => if k = 0 then 2 else 3
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let pair : MutationMask 2 := Finset.univ
  let r : Fin 2 -> Real :=
    StaticUnaryUnbiasedMutation.residualPotentialWeights w g 1
  have hres : ∀ j : Fin 2, (1 : Real) * w j ≤ g j := by
    intro j
    fin_cases j <;> norm_num [w, g]
  have hr0 : r (0 : Fin 2) = 0 := by
    norm_num [r, StaticUnaryUnbiasedMutation.residualPotentialWeights, w, g]
  have hr1 : r (1 : Fin 2) = 2 := by
    norm_num [r, StaticUnaryUnbiasedMutation.residualPotentialWeights, w, g]
  have hpositiveResidual : 0 < r (1 : Fin 2) := by
    rw [hr1]
    norm_num
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
  have haccEvent : ∀ mask ∈ ({pair} : Finset (MutationMask 2)),
      Accepts (linearFitness w) x (mutateWithMask x mask) := by
    intro mask hm
    have heq : mask = pair := Finset.mem_singleton.mp hm
    subst mask
    exact hacc
  have hpairMass : 0 < law.weight pair := by
    change 0 < mutationMaskWeight (1 / 2 : Real) pair
    norm_num [mutationMaskWeight, pair]
  have hactualLoss : 0 < law.weight pair * r (1 : Fin 2) := by
    rw [hr1]
    positivity
  have _hnonneg :=
    StaticUnaryUnbiasedMutation.residualPotentialWeights_nonneg w g 1 hres
  have _hbound := law.acceptedEventWeightedPotentialDrop_ge_neg_residualLoss_of_accepts
    ({pair} : Finset (MutationMask 2)) w g x 1 (by norm_num) hres haccEvent
  have _hdetail : 0 < law.weight pair *
      (Finset.sum (oneToZeroFlips x pair) r) := by
    rw [hoset]
    simpa using hactualLoss
  trivial

end ECRuntimeTest
