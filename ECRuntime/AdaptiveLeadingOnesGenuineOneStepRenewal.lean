import ECRuntime.FirstEntryFiniteMarginalBridge
import ECRuntime.AdaptiveLeadingOnesGenuineExactLevelFiniteMarginal
import ECRuntime.AdaptiveLeadingOnesFiniteOccupationRenewal
import ECRuntime.AdaptiveLeadingOnesFiniteStayMeasure
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01 substantive remaining Markov-law bridge. Finite weighted trajectory
renewal is already certified. The unresolved step is transferring that real
recurrence to genuine ENNReal path masses with the correct local residence
coefficient. This will support an induction proving Stage 321. -/

/-- Genuine exact-level occupation obeys first-entry plus local residence. -/
theorem proposed_leadingOnesAdaptive_genuineExactLevel_oneStepRenewal
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val} =
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
          ∀ s : Nat, s < t + 1 →
            leadingOnes (transitionTrajectoryState x path s) ≠ i.val} +
      ENNReal.ofReal (1 - rate i.val * (1 - rate i.val) ^ i.val) *
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) = i.val} := by
  classical
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  let q : Real := 1 - rate i.val * (1 - rate i.val) ^ i.val
  have hi := hrate i.val (Nat.le_of_lt i.isLt)
  have hq : 0 ≤ q := by
    change 0 ≤ 1 - leadingOnesLevelExitProbability (rate i.val) i
    exact sub_nonneg.mpr
      (leadingOnesLevelExitProbability_le_one_of_mem_Icc hi.1 hi.2 i)
  have hentry :
      transitionTrajectoryMeasure P hP x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
          ∀ s : Nat, s < t + 1 →
            leadingOnes (transitionTrajectoryState x path s) ≠ i.val} =
        finiteTrajectoryMeasure P hP (t + 1) x
          (leadingOnesFiniteBelowThenExactAtNextSet x i t) := by
    simpa only [Nat.lt_succ_iff] using
      (proposed_leadingOnesAdaptive_firstVisitCylinder_eq_finiteEntryMeasure
        rate hrate x i t)
  have hnext :=
    proposed_leadingOnesAdaptive_exactLevelMass_eq_finiteMarginal
      rate hrate x i (t + 1)
  have hprev :=
    proposed_leadingOnesAdaptive_exactLevelMass_eq_finiteMarginal
      rate hrate x i t
  have hreal :=
    proposed_leadingOnesAdaptive_finiteOccupation_oneStep_renewal
      rate hrate x i t
  have hbelow :
      0 ≤ finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteBelowThenExactAtNextSet x i t) :=
    finiteTrajectorySetWeight_nonneg P hP (t + 1) x _
  have hprevious :
      0 ≤ finiteTrajectorySetWeight P t x
        (leadingOnesFiniteScoreLevelAtHorizonSet x i t) :=
    finiteTrajectorySetWeight_nonneg P hP t x _
  calc
    transitionTrajectoryMeasure P hP x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val} =
      finiteTrajectoryMeasure P hP (t + 1) x
        (leadingOnesFiniteExactAtNextSet x i t) := by
          simpa only [leadingOnesFiniteScoreLevelAtHorizonSet,
            leadingOnesFiniteExactAtNextSet] using hnext
    _ = ENNReal.ofReal
        (finiteTrajectorySetWeight P (t + 1) x
          (leadingOnesFiniteExactAtNextSet x i t)) :=
      finiteTrajectoryMeasure_apply_eq_ofReal_setWeight P hP (t + 1) x _
    _ = ENNReal.ofReal
          (finiteTrajectorySetWeight P (t + 1) x
            (leadingOnesFiniteBelowThenExactAtNextSet x i t)) +
        ENNReal.ofReal q * ENNReal.ofReal
          (finiteTrajectorySetWeight P t x
            (leadingOnesFiniteScoreLevelAtHorizonSet x i t)) := by
      rw [hreal]
      rw [ENNReal.ofReal_add hbelow (mul_nonneg hq hprevious)]
      rw [ENNReal.ofReal_mul hq]
    _ = transitionTrajectoryMeasure P hP x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ∧
            ∀ s : Nat, s < t + 1 →
              leadingOnes (transitionTrajectoryState x path s) ≠ i.val} +
        ENNReal.ofReal q *
          transitionTrajectoryMeasure P hP x
            {path : Nat → BitString n |
              leadingOnes (transitionTrajectoryState x path t) = i.val} := by
      rw [← finiteTrajectoryMeasure_apply_eq_ofReal_setWeight
        P hP (t + 1) x (leadingOnesFiniteBelowThenExactAtNextSet x i t)]
      rw [← finiteTrajectoryMeasure_apply_eq_ofReal_setWeight
        P hP t x (leadingOnesFiniteScoreLevelAtHorizonSet x i t)]
      rw [← hentry, ← hprev]

end ECRuntime
