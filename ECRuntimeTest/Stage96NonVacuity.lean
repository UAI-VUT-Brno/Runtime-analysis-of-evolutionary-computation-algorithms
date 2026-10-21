import ECRuntime.StaticUnaryUnbiasedAcceptedGainAlignment
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 96 non-vacuity: an accepted mask with negative potential change

This parent has an accepted two-coordinate objective improvement but a
strictly negative potential gain: objective weights (2,1), potential weights
(2,3), and parent 01. Thus the distortion term is essential, not an
empty-event or zero-distortion artifact. The normalized bit-flip law gives
this non-singleton mask positive probability. All nine theorem interfaces
are instantiated at this nontrivial objective/potential pair.

This regression requires strict compiler verification on the user's Lean.
-/

/-- A concrete accepted non-singleton event with positive objective margin,
positive original-law probability, and a negative potential change. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : ℝ)
      (by norm_num) (by norm_num)
  let w : Fin 2 → ℝ := fun k => if k = 0 then 2 else 1
  let g : Fin 2 → ℝ := fun k => if k = 0 then 2 else 3
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let i : Fin 2 := 0
  let j : Fin 2 := 1
  let pair : MutationMask 2 := Finset.univ
  let b : ℕ := 3
  have hn : 2 ≤ (2 : ℕ) := by norm_num
  have hpos : 0 < (2 : ℕ) := by omega
  have hb : 2 ≤ b := by norm_num [b]
  have hlower : (0 : ℝ) ≤ 1 := by norm_num
  have hw : PositiveLinearWeights w := by
    intro k
    fin_cases k <;> norm_num [w]
  have hband : StaticUnaryUnbiasedMutation.PotentialWeightSandwich w g 1 3 := by
    intro k
    fin_cases k <;> constructor <;> norm_num [w, g]
  have hi : x i = false := by decide
  have hxj : x j = true := by decide
  have hzset : zeroToOneFlips x pair = {i} := by
    ext k
    fin_cases k <;> decide
  have hoset : oneToZeroFlips x pair = {j} := by
    ext k
    fin_cases k <;> decide
  have hacc : Accepts (linearFitness w) x (mutateWithMask x pair) := by
    apply (accepts_linearFitness_iff_flip_sums w x pair).2
    rw [hoset, hzset]
    norm_num [w, i, j]
  have hpotentialOpposite :
      (∑ k ∈ zeroToOneFlips x pair, g k) <
        (∑ k ∈ oneToZeroFlips x pair, g k) := by
    rw [hzset, hoset]
    norm_num [g, i, j]
  have hpairMass : 0 < law.weight pair := by
    change 0 < mutationMaskWeight (1 / 2 : ℝ) pair
    norm_num [mutationMaskWeight, pair]
  have hpositiveObjectiveLoss :
      0 < law.weight pair * (∑ k ∈ oneToZeroFlips x pair, w k) := by
    rw [hoset]
    simpa [w, j] using hpairMass
  have hpivot : pair ∈
      StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i := by
    apply (StaticUnaryUnbiasedMutation.mem_acceptedLeftmostZeroEvent_iff w x i pair).2
    refine ⟨?_, ?_, hacc⟩
    · exact (mem_zeroToOneFlips x pair i).2 ⟨Finset.mem_univ _, hi⟩
    · intro k _
      change 0 ≤ k.val
      exact Nat.zero_le _
  have hshort : pair ∈
      StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) b := by
    change pair ∈ (Finset.univ : Finset (MutationMask 2)).filter
      (fun mask => mask.card < b)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by norm_num [pair, b]⟩
  have hshortPivot : pair ∈
      StaticUnaryUnbiasedMutation.shortAcceptedPivotEvent w x b i := by
    change pair ∈ (StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) b).filter
      (fun mask => mask ∈ StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i)
    exact Finset.mem_filter.mpr ⟨hshort, hpivot⟩
  have hnotSingleton : pair ≠ ({i} : MutationMask 2) := by
    intro h
    have hcard : pair.card = 2 := by simp [pair]
    rw [h] at hcard
    simp at hcard
  have hrem : pair ∈
      StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b i :=
    Finset.mem_erase.mpr ⟨hnotSingleton, hshortPivot⟩
  have hnonempty :
      (StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b i).Nonempty :=
    ⟨pair, hrem⟩
  have haccEvent : ∀ mask ∈ ({pair} : Finset (MutationMask 2)),
      Accepts (linearFitness w) x (mutateWithMask x mask) := by
    intro mask hm
    have hmp : mask = pair := Finset.mem_singleton.mp hm
    subst mask
    exact hacc
  have _gainSandwich := law.acceptedEventFlippedZeroGain_ge_scaledObjectiveGain
    ({pair} : Finset (MutationMask 2)) w g x 1 3 hband
  have _lossSandwich := law.acceptedEventFlippedOneLoss_le_scaledObjectiveLoss
    ({pair} : Finset (MutationMask 2)) w g x 1 3 hband
  have _objectiveAccepted := law.acceptedEventFlippedZeroGain_ge_oneLoss_of_accepts
    ({pair} : Finset (MutationMask 2)) w x haccEvent
  have _margin := law.acceptedEventWeightedPotentialDrop_ge_objectiveMargin_sub_distortionLoss
    ({pair} : Finset (MutationMask 2)) w g x 1 3 hband haccEvent
  have _eventDistortion := law.acceptedEventWeightedPotentialDrop_ge_neg_distortionLoss_of_accepts
    ({pair} : Finset (MutationMask 2)) w g x 1 3 hlower hband haccEvent
  have _pivotDistortion := law.shortPivotRemainderEvent_drop_ge_neg_distortionLoss
    w g x b i 1 3 hlower hband
  have _shortDistortion := law.acceptedEventWeightedPotentialDrop_short_ge_singleton_sub_distortionLoss
    hpos w g hw x b hb 1 3 hlower hband
  have _globalDistortion := law.linearErrorPotential_drift_ge_singleton_sub_distortionLoss_sub_tail
    hpos w g hw x b hb 1 3 hlower hband
  have _globalPair := law.linearErrorPotential_drift_ge_singleton_sub_distortionPairBudget_sub_tail
    hn w g hw x b hb 1 3 hlower hband
  trivial

end ECRuntimeTest
