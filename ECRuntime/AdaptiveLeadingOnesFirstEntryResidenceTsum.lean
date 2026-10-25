import ECRuntime.AdaptiveLeadingOnesGenuineOneStepRenewal
import ECRuntime.AdaptiveLeadingOnesResidenceGeometricSeries
import ECRuntime.ExactOccupationConvolutionFactorization
import ECRuntime.AdaptiveLeadingOnesTrueFirstEntryConvolution
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: countable first-entry/residence factorization at a fixed start
and exact score, after the finite-horizon strong Markov convolution
has been certified as Stage 321. Unlike the scalar convolution theorem,
this is a genuine probabilistic path-measure identity. -/

/-- Expected occupation of one exact LeadingOnes level factors into the
probability of first visiting that level and the geometric residence mean. -/
theorem proposed_leadingOnesAdaptive_fixedStartLevelOccupation_eq_firstVisitMass_mul_residence
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (x : BitString n) (i : Fin n) :
    (∑' t : Nat,
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate
          (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) = i.val}) =
      (∑' k : Nat,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate
            (fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩)) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path k) = i.val ∧
            ∀ s : Nat, s < k →
              leadingOnes (transitionTrajectoryState x path s) ≠ i.val}) *
        ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  let hrate0 : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1 :=
    fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate0
  let occupation : Nat → ENNReal := fun t =>
    transitionTrajectoryMeasure P hP x
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) = i.val}
  let entry : Nat → ENNReal := fun k =>
    transitionTrajectoryMeasure P hP x
      (proposed_leadingOnesAdaptive_firstVisitAtTimeSet x i k)
  let q : ENNReal :=
    ENNReal.ofReal (1 - rate i.val * (1 - rate i.val) ^ i.val)
  have hconv : ∀ t : Nat, occupation t =
      ∑ k ∈ Finset.range (t + 1), entry k * q ^ (t - k) := by
    intro t
    exact proposed_leadingOnesAdaptive_exactLevelMeasure_eq_firstVisitConvolution
      n rate hrate0 x i t
  have hprod := proposed_ennreal_trueOccupation_total_of_firstEntryConvolution
    occupation entry q hconv
  have hi := hrate i.val (Nat.le_of_lt i.isLt)
  have hgeo := proposed_leadingOnesAdaptive_levelResidenceGeometricSeries
    rate i hi.1 hi.2
  change (∑' t : Nat, occupation t) =
      (∑' k : Nat, entry k) *
        (∑' j : Nat,
          (ENNReal.ofReal (1 - rate i.val * (1 - rate i.val) ^ i.val)) ^ j)
    at hprod
  rw [hgeo] at hprod
  simpa only [occupation, entry, P, hP, hrate0,
    proposed_leadingOnesAdaptive_firstVisitAtTimeSet] using hprod

end ECRuntime
