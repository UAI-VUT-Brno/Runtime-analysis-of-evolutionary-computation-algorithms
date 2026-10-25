import ECRuntime.AdaptiveLeadingOnesExpectedExactLevelResidence
import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import ECRuntime.AdaptiveLeadingOnesUniformOccupationLift
import ECRuntime.LeadingOnesCountableLevelOccupationAssembly
import ECRuntime.AdaptiveLeadingOnesUniformExpectedOccupationHalf
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.UnrestrictedRuntime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-- Nonnegative countable sums commute with finite sums. This uses Mathlib's
`ENNReal.tsum_comm` and `tsum_fintype`, with no summability hypotheses. -/
private theorem proof67_finiteSum_tsum_swap
    {α : Type*} [Fintype α] (f : α → Nat → ENNReal) :
    (∑ x : α, ∑' t : Nat, f x t) =
      ∑' t : Nat, ∑ x : α, f x t := by
  classical
  calc
    (∑ x : α, ∑' t : Nat, f x t) =
        ∑' x : α, ∑' t : Nat, f x t := by rw [tsum_fintype]
    _ = ∑' t : Nat, ∑' x : α, f x t := ENNReal.tsum_comm
    _ = ∑' t : Nat, ∑ x : α, f x t := by
      apply tsum_congr
      intro t
      rw [tsum_fintype]

/-! P01: paper-level target, not an auxiliary conditional-residence theorem.
The remaining bridge is between the Bellman expected runtime and the sum of
nonterminal exact-score occupation measures, with a valid exchange of the
finite level sum and monotone countable time sum. The occupation terms are
already independently formalized in the certified Stage 305/388 chain.
No assertion about the equality below is promoted before Lean discharges it. -/

/-- Exact uniform-initial expected optimization time for an arbitrary
strictly interior fitness-dependent LeadingOnes mutation schedule. -/
theorem proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition rate)
          (leadingOnesTarget n) x) =
      ∑ i : Fin n,
        (1 / 2 : ENNReal) *
          ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  let hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1 :=
    fun j hj => ⟨(hinterior j hj).1.le, (hinterior j hj).2.le⟩
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  let mass (x : BitString n) (t : Nat) (i : Fin n) : ENNReal :=
    transitionTrajectoryMeasure P hP x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) = i.val}
  let nonoptimal (x : BitString n) (t : Nat) : ENNReal :=
    transitionTrajectoryMeasure P hP x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) < n}
  have hpath (x : BitString n) :
      runtimeSup P (leadingOnesTarget n) x =
        ∫⁻ path : Nat → BitString n,
          transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
          ∂transitionTrajectoryMeasure P hP x := by
    exact runtimeSup_eq_lintegral_transitionTrajectoryFirstHittingTime
      P (leadingOnesTarget n) hP x
  have hlevel (i : Fin n) :
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, ∑' t : Nat, mass x t i) =
      (1 / 2 : ENNReal) *
        ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
    exact proposed_leadingOnesAdaptive_uniformOccupation_eq_halfResidence
      n rate hinterior i
  calc
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n, runtimeSup P (leadingOnesTarget n) x) =
        ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ x : BitString n,
            ∫⁻ path : Nat → BitString n,
              transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
              ∂transitionTrajectoryMeasure P hP x) := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            exact hpath x
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ x : BitString n, ∑' t : Nat, nonoptimal x t) := by
            congr 1
            exact proposed_leadingOnesAdaptive_uniformPathExpected_eq_uniformOccupation
              n rate hrate
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑' t : Nat, ∑ x : BitString n, nonoptimal x t) := by
            rw [proof67_finiteSum_tsum_swap]
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
          (∑ i : Fin n, ∑' t : Nat, ∑ x : BitString n, mass x t i) := by
            congr 1
            exact proposed_leadingOnesAdaptive_uniformOccupation_eq_sumExactLevelOccupations
              n rate hrate
    _ = ∑ i : Fin n,
          ((Fintype.card (BitString n) : ENNReal)⁻¹) *
            (∑ x : BitString n, ∑' t : Nat, mass x t i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [proof67_finiteSum_tsum_swap]
    _ = ∑ i : Fin n, (1 / 2 : ENNReal) *
          ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
            apply Finset.sum_congr rfl
            intro i _
            exact hlevel i

end ECRuntime
