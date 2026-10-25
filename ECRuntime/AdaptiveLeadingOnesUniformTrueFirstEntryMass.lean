import ECRuntime.AdaptiveLeadingOnesFirstVisitMassEntry
import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import ECRuntime.AdaptiveLeadingOnesFirstVisitExactCrossingCylinder
import ECRuntime.AdaptiveLeadingOnesUniformExactCrossingCylinderBridge
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: bridge between the certified uniform first-crossing history
sums and genuine first visits at an exact score. This is the missing
rate-invariant probability mass identification for Stage 305. -/

/-- The probability of ever visiting an exact nonterminal level,
averaged over uniform initial states, equals the certified eventual
exact-entry mass. This is a genuine infinite-path event assertion. -/
theorem proposed_leadingOnesAdaptive_uniformTrueFirstVisitMass_eq_eventualExactEntry
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      ∑ x : BitString n, ∑' k : Nat,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate
            (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path k) = i.val ∧
            ∀ s : Nat, s < k →
              leadingOnes (transitionTrajectoryState x path s) ≠ i.val} =
      leadingOnesAdaptiveEventualFirstCrossingExactMass rate i := by
  classical
  -- This reduces the countable uniform first-visit identity to the
  -- single-time *exact* finite-history cylinder identity (Stage 377).
  -- The finite-history total-crossing average (Stage 222) is insufficient:
  -- it includes paths that skip i, and would overcount by a factor two.
  have hrate0 : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1 :=
    fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate0
  let c : ENNReal := (Fintype.card (BitString n) : ENNReal)⁻¹
  let visit : Nat → BitString n → ENNReal := fun t x =>
    transitionTrajectoryMeasure P hP x
      (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i t)
  have htime (t : Nat) :
      c * (∑ x : BitString n, visit t x) =
        ENNReal.ofReal
          (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i) := by
    calc
      c * (∑ x : BitString n, visit t x) =
          c * (∑ x : BitString n,
            transitionTrajectoryMeasure P hP x
              (leadingOnesTrajectoryFirstCrossingExactSet i x t)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro x _
        exact proposed_leadingOnesAdaptive_firstVisitMass_eq_exactCrossingCylinder
          rate hrate0 x i t
      _ = ENNReal.ofReal
            (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i) :=
          proposed_leadingOnesAdaptive_uniformExactCrossingCylinder_eq_historyMass
            n rate hrate0 i t
  change c * (∑ x : BitString n, ∑' t : Nat, visit t x) =
    ∑' t : Nat,
      ENNReal.ofReal
        (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i)
  calc
    c * (∑ x : BitString n, ∑' t : Nat, visit t x) =
        c * (∑' t : Nat, ∑ x : BitString n, visit t x) := by
      congr 1
      calc
        (∑ x : BitString n, ∑' t : Nat, visit t x) =
            ∑' x : BitString n, ∑' t : Nat, visit t x := by
              rw [tsum_fintype]
        _ = ∑' t : Nat, ∑' x : BitString n, visit t x :=
              ENNReal.tsum_comm
        _ = ∑' t : Nat, ∑ x : BitString n, visit t x := by
              apply tsum_congr
              intro t
              rw [tsum_fintype]
    _ = ∑' t : Nat, c * (∑ x : BitString n, visit t x) := by
          exact (ENNReal.tsum_mul_left).symm
    _ = ∑' t : Nat,
          ENNReal.ofReal
            (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i) := by
          apply tsum_congr
          intro t
          exact htime t

end ECRuntime
