import ECRuntime.StaticUnaryUnbiasedShortPivotPairBudget
import Mathlib

open ECRuntime
open scoped BigOperators

namespace ECRuntimeTest

/-!
# Stage 94 integration-candidate non-vacuity witness

A two-bit parent with precisely one zero coordinate accepts the two-bit
mutation when its positive linear objective coefficients are equal. The
accepted short-pivot *remainder* therefore contains a genuine two-bit mask,
with a one-to-zero loss coordinate distinct from its improving pivot.
The mutation law is normalized independent-bit mutation at rate one half.
This proof is NEW in the integration candidate and needs user-side Lean
verification; it is not a compiler-certified promotion guard yet.
-/

/-- The hypotheses of all nine Stage 94 results can be realized on the same
mixed parent, a nonempty accepted two-bit remainder, and an unbiased law. -/
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
  have hb : 2 ≤ b := by norm_num [b]
  have hi : x i = false := by decide
  have hjx : x j = true := by decide
  have hij : i ≠ j := by decide
  have hw : PositiveLinearWeights w := by
    intro k
    norm_num [w]
  have hg : ∀ k : Fin 2, 0 ≤ g k := by
    intro k
    norm_num [g]
  have hzero : i ∈ zeroToOneFlips x pair :=
    (mem_zeroToOneFlips x pair i).2 ⟨Finset.mem_univ _, hi⟩
  have hone : j ∈ oneToZeroFlips x pair :=
    (mem_oneToZeroFlips x pair j).2 ⟨Finset.mem_univ _, hjx⟩
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
  have hpivot : pair ∈ StaticUnaryUnbiasedMutation.acceptedLeftmostZeroEvent w x i :=
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
  have _cardLower := StaticUnaryUnbiasedMutation.shortPivotRemainderEvent_card_ge_two
    w x b i pair hrem
  have _cardUpper := StaticUnaryUnbiasedMutation.shortPivotRemainderEvent_card_lt_cutoff
    w x b i pair hrem
  have _jointFlip := StaticUnaryUnbiasedMutation.shortPivotRemainderEvent_pair_membership
    w x b i pair hrem j hone
  have _exactPairMass := law.shortRadiusPairFlipMass_eq_truncatedSecondFactorialRadiusMoment_div
    hn b i j hij
  have _meanPairBudget := law.shortRadiusPairFlipMass_le_cutoffMeanRadius_div
    hn b i j hij
  have _slice := law.shortPivotRemainderEvent_coordinateSlice_mass_le_shortRadiusPairFlipMass
    w x b i j
  have _pairLoss := law.shortPivotRemainderEvent_flippedOneLoss_le_pairMomentBudget
    hn w g x b i hi hg
  have _meanLoss := law.shortPivotRemainderEvent_flippedOneLoss_le_cutoffMeanBudget
    hn w g x b i hi hg
  have _driftBound := law.linearErrorPotential_drift_ge_shortPairMomentBudget_sub_tailMeanRadius
    hn w g hw x b hb hg
  trivial

end ECRuntimeTest
