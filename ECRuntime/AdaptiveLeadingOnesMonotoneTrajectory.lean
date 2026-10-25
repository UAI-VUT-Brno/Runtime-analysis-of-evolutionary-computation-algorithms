import ECRuntime.LeadingOnesTrajectoryMonotonicity
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
Stage 294 (P01, proposed). The generic positive-support monotonicity theorem
already certified for stochastic finite kernels applies unchanged to the
fitness-dependent mutation schedule. No independence of suffix bits is used.
-/

/-- Positive-mass adaptive LeadingOnes transitions cannot increase the
canonical distance-to-optimum potential. The argument is deterministic
elitist selection and does not require bounds on the mutation rate. -/
theorem proposed_leadingOnesAdaptive_hasPotentialNonincreasingTransitionSupport
    {n : Nat} (rate : Nat → Real) :
    HasPotentialNonincreasingTransitionSupport
      (leadingOnesAdaptiveTransition (n := n) rate)
      (leadingOnesPotential (n := n)) := by
  intro x y hxy
  change 0 < onePlusOneTransition (rate (leadingOnes x))
    (leadingOnesReal (n := n)) x y at hxy
  exact (onePlusOneTransition_leadingOnes_hasPotentialNonincreasingTransitionSupport
    (rate (leadingOnes x))) x y hxy

/-- A bounded fitness-dependent rate schedule yields an almost-sure
nonincreasing genuine infinite LeadingOnes trajectory. This specializes
the already certified generic Markov support theorem. -/
theorem proposed_leadingOnesAdaptive_ae_potentialNonincreasing
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) :
    ∀ᵐ path ∂transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x,
      IsPotentialNonincreasingAlong (leadingOnesPotential (n := n)) x path := by
  exact transitionTrajectoryMeasure_ae_potentialNonincreasing_of_support
    (leadingOnesAdaptiveTransition rate)
    (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
    (leadingOnesPotential (n := n))
    (proposed_leadingOnesAdaptive_hasPotentialNonincreasingTransitionSupport rate)
    x

/-- On almost every adaptive trajectory the optimum target stays reached
once entered, because its potential is zero and potentials are natural. -/
theorem proposed_leadingOnesAdaptive_ae_optimumAbsorbing
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) :
    ∀ᵐ path ∂transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x,
      ∀ t : Nat,
        transitionTrajectoryState x path t ∈ leadingOnesTarget n →
        transitionTrajectoryState x path (t + 1) ∈ leadingOnesTarget n := by
  filter_upwards [proposed_leadingOnesAdaptive_ae_potentialNonincreasing
    rate hrate x] with path hmono
  intro t ht
  have hzero : leadingOnesPotential (transitionTrajectoryState x path t) = 0 :=
    ((leadingOnesPotential_isTarget n) _).mp ht
  have hnext : leadingOnesPotential (transitionTrajectoryState x path (t + 1)) ≤
      leadingOnesPotential (transitionTrajectoryState x path t) := hmono t
  have hnextzero :
      leadingOnesPotential (transitionTrajectoryState x path (t + 1)) = 0 := by
    omega
  exact ((leadingOnesPotential_isTarget n) _).mpr hnextzero

end ECRuntime
