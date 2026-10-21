import ECRuntime.StaticUnaryUnbiasedShortPivotGainRecovery
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 95 root integration: non-vacuity

The parent `01`, with equal positive objective and potential weights, accepts
flipping *both* coordinates. Hence the accepted short-pivot non-singleton
remainder is inhabited, rather than all new estimates being exercised on an
empty event. The law is independent-bit mutation with `p = 1/2`.

This integration regression is not compiled until the user's strict run.
-/

/-- All nine Stage 95 theorem interfaces can be instantiated with a concrete
normalized mutation law and an accepted two-coordinate pivot remainder. -/
example : True := by
  classical
  let law : StaticUnaryUnbiasedMutation 2 :=
    StaticUnaryUnbiasedMutation.independentBitLaw (1 / 2 : ℝ)
      (by norm_num) (by norm_num)
  let w : Fin 2 → ℝ := fun _ => 1
  let g : Fin 2 → ℝ := fun _ => 1
  let x : BitString 2 := fun k => decide (k = (1 : Fin 2))
  let i : Fin 2 := 0
  let j : Fin 2 := 1
  let pair : MutationMask 2 := Finset.univ
  let b : ℕ := 3
  have hn : 2 ≤ (2 : ℕ) := by norm_num
  have hpos : 0 < (2 : ℕ) := by omega
  have hb : 2 ≤ b := by norm_num [b]
  have hi : x i = false := by decide
  have hxj : x j = true := by decide
  have hw : PositiveLinearWeights w := by
    intro k
    norm_num [w]
  have hg : ∀ k : Fin 2, 0 ≤ g k := by
    intro k
    norm_num [g]
  have hzero : i ∈ zeroToOneFlips x pair :=
    (mem_zeroToOneFlips x pair i).2 ⟨Finset.mem_univ _, hi⟩
  have hone : j ∈ oneToZeroFlips x pair :=
    (mem_oneToZeroFlips x pair j).2 ⟨Finset.mem_univ _, hxj⟩
  have hzset : zeroToOneFlips x pair = {i} := by
    ext k
    fin_cases k <;> decide
  have hoset : oneToZeroFlips x pair = {j} := by
    ext k
    fin_cases k <;> decide
  have hacc : Accepts (linearFitness w) x (mutateWithMask x pair) := by
    apply (accepts_linearFitness_iff_flip_sums w x pair).2
    rw [hoset, hzset]
    simp [w]
  have hmin : ∀ k ∈ zeroToOneFlips x pair, i.val ≤ k.val := by
    intro k hk
    change 0 ≤ k.val
    exact Nat.zero_le _
  have hpivot : pair ∈
      StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i :=
    (StaticUnaryUnbiasedMutation.mem_acceptedLeftmostZeroEvent_iff w x i pair).2
      ⟨hzero, hmin, hacc⟩
  have hshort : pair ∈ StaticUnaryUnbiasedMutation.shortRadiusMaskEvent (n := 2) b := by
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
  have hrem : pair ∈ StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b i :=
    Finset.mem_erase.mpr ⟨hnotSingleton, hshortPivot⟩
  have hnonempty :
      (StaticUnaryUnbiasedMutation.shortPivotRemainderEvent w x b i).Nonempty :=
    ⟨pair, hrem⟩
  have hpairMass : 0 < law.weight pair := by
    change 0 < mutationMaskWeight (1 / 2 : ℝ) pair
    norm_num [mutationMaskWeight, pair]
  have hpairGain : 0 <
      law.weight pair * (∑ k ∈ zeroToOneFlips x pair, g k) := by
    rw [hzset]
    simpa [g] using hpairMass
  have haccEvent : ∀ mask ∈ ({pair} : Finset (MutationMask 2)),
      Accepts (linearFitness w) x (mutateWithMask x mask) := by
    intro mask hm
    have hmp : mask = pair := Finset.mem_singleton.mp hm
    subst mask
    exact hacc
  have _gainSlices := law.acceptedEventFlippedZeroGain_eq_coordinateSlices
    ({pair} : Finset (MutationMask 2)) g x
  have _gainNonneg := law.acceptedEventFlippedZeroGain_nonneg
    ({pair} : Finset (MutationMask 2)) g x hg
  have _exactDrop := law.acceptedEventWeightedPotentialDrop_eq_zeroGain_sub_oneLoss_of_accepts
    ({pair} : Finset (MutationMask 2)) w g x haccEvent
  have _pivotGain := law.shortPivotRemainderEvent_zeroGain_ge_pivotMass
    w g x b i hi hg
  have _pivotDrop := law.shortPivotRemainderEvent_drop_ge_pivotMass_sub_oneLoss
    w g x b i hi hg
  have _shortExact := law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_gains_sub_losses
    hpos w g hw x b hb
  have _shortLower := law.acceptedEventWeightedPotentialDrop_short_ge_singleton_add_pivotMass_sub_losses
    hpos w g hw x b hb hg
  have _globalExact := law.linearErrorPotential_drift_ge_singleton_add_pivotMass_sub_losses_sub_tailMeanRadius
    hpos w g hw x b hb hg
  have _globalPair := law.linearErrorPotential_drift_ge_singleton_add_pivotMass_sub_pairBudget_sub_tailMeanRadius
    hn w g hw x b hb hg
  trivial

end ECRuntimeTest
