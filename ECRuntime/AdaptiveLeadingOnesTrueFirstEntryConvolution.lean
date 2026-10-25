import ECRuntime.AdaptiveLeadingOnesGenuineOneStepRenewal
import ECRuntime.AdaptiveLeadingOnesFirstVisitAtZeroMass
import ECRuntime.AdaptiveLeadingOnesFiniteOccupationRenewal
import ECRuntime.LeadingOnesCountableLevelOccupationAssembly
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-!
P01: the main remaining probabilistic bridge. First entrance is expressed
using an actual infinite trajectory, including a possible entrance at time
zero. The expected convolution follows from the strong Markov property,
the no-return property, and the exact local stay probability. Earlier
certified real-weight finite renewal results are not by themselves this
ENNReal path-measure statement.
-/

/-- First visit to exact LeadingOnes level `i` at trajectory time `k`. -/
def proposed_leadingOnesAdaptive_firstVisitAtTimeSet
    {n : Nat} (x : BitString n) (i : Fin n) (k : Nat) :
    Set (Nat → BitString n) :=
  {path | leadingOnes (transitionTrajectoryState x path k) = i.val ∧
    ∀ s : Nat, s < k →
      leadingOnes (transitionTrajectoryState x path s) ≠ i.val}

/-- At time zero, the exact-level event is literally its first-visit event.
This verifies the base case of the eventual strong Markov renewal argument
without a conditional-independence assumption. -/
theorem proposed_leadingOnesAdaptive_firstVisitAtZero_set
    {n : Nat} (x : BitString n) (i : Fin n) :
    proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i 0 =
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path 0) = i.val} := by
  ext path
  simp [proposed_leadingOnesAdaptive_firstVisitAtTimeSet]

/-- Genuine finite-horizon exact-level occupation as a convolution of
first-entrance masses with conditional geometric residence probabilities.
No claim is made that this currently follows by algebraic rewriting alone. -/
theorem proposed_leadingOnesAdaptive_exactLevelMeasure_eq_firstVisitConvolution
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) = i.val} =
      ∑ k ∈ Finset.range (t + 1),
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i k) *
        (ENNReal.ofReal
          (1 - rate i.val * (1 - rate i.val) ^ i.val)) ^ (t - k) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  let occupation : Nat → ENNReal := fun k =>
    transitionTrajectoryMeasure P hP x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path k) = i.val}
  let entry : Nat → ENNReal := fun k =>
    transitionTrajectoryMeasure P hP x
      (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i k)
  let stay : ENNReal :=
    ENNReal.ofReal (1 - rate i.val * (1 - rate i.val) ^ i.val)
  have hzero : occupation 0 = entry 0 := by
    exact (proposed_leadingOnesAdaptive_firstVisitAtZeroMass_eq_occupation
      rate hrate x i).symm
  have hstep : ∀ k, occupation (k + 1) =
      entry (k + 1) + stay * occupation k := by
    intro k
    exact proposed_leadingOnesAdaptive_genuineExactLevel_oneStepRenewal
      rate hrate x i k
  have hsolution : ∀ k : Nat,
      occupation k =
        ∑ j ∈ Finset.range (k + 1),
          entry j * stay ^ (k - j) := by
    intro k
    induction k with
    | zero =>
        simpa [Finset.sum_range_succ] using hzero
    | succ k ih =>
        have hscale :
            stay * (∑ j ∈ Finset.range (k + 1),
              entry j * stay ^ (k - j)) =
            ∑ j ∈ Finset.range (k + 1),
              entry j * stay ^ (k + 1 - j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hjk : j < k + 1 := Finset.mem_range.mp hj
          have hexp : k + 1 - j = (k - j) + 1 := by omega
          rw [hexp, pow_succ]
          ac_rfl
        calc
          occupation (k + 1) = entry (k + 1) + stay * occupation k :=
            hstep k
          _ = entry (k + 1) + stay *
                (∑ j ∈ Finset.range (k + 1),
                  entry j * stay ^ (k - j)) := by rw [ih]
          _ = entry (k + 1) +
                ∑ j ∈ Finset.range (k + 1),
                  entry j * stay ^ (k + 1 - j) := by rw [hscale]
          _ = ∑ j ∈ Finset.range (k + 2),
                entry j * stay ^ (k + 1 - j) := by
            conv_rhs => rw [Finset.sum_range_succ]
            simp only [Nat.sub_self, pow_zero, mul_one]
            ac_rfl
  exact hsolution t

end ECRuntime
