import ECRuntime.AdaptiveLeadingOnesFiniteStayWeightFactor
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 267 (P01, proposed). Convert the genuine nonconstant adaptive
finite-trajectory stay-weight factorization into an identity of finite
trajectory *measures*. Unlike a conditional-independence assertion, this
is a direct consequence of the explicit finite-state path law.
-/

/-- At adjacent observation times, the adaptive finite-trajectory law
assigns exactly the local stay factor times the preceding occupation mass
to the event of remaining at a visited LeadingOnes level. -/
theorem proposed_leadingOnesAdaptive_finiteSameLevel_measure_factor
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    finiteTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
        (t + 1) x
        (leadingOnesFiniteEqualThenExactAtNextSet x i t) =
      ENNReal.ofReal (1 - rate i.val * (1 - rate i.val) ^ i.val) *
        finiteTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
          t x (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  have hi := hrate i.val (Nat.le_of_lt i.isLt)
  have hstay0 : 0 ≤ 1 - rate i.val * (1 - rate i.val) ^ i.val := by
    change 0 ≤ 1 - leadingOnesLevelExitProbability (rate i.val) i
    exact sub_nonneg.mpr
      (leadingOnesLevelExitProbability_le_one_of_mem_Icc hi.1 hi.2 i)
  change finiteTrajectoryMeasure P hP (t + 1) x
      (leadingOnesFiniteEqualThenExactAtNextSet x i t) =
    ENNReal.ofReal (1 - rate i.val * (1 - rate i.val) ^ i.val) *
      finiteTrajectoryMeasure P hP t x
        (leadingOnesFiniteScoreLevelAtHorizonSet x i t)
  rw [finiteTrajectoryMeasure_apply_eq_ofReal_setWeight P hP (t + 1) x
    (leadingOnesFiniteEqualThenExactAtNextSet x i t)]
  rw [proposed_leadingOnesAdaptive_finiteSameLevel_setWeight_factor
    rate hrate x i t]
  rw [ENNReal.ofReal_mul hstay0]
  rw [finiteTrajectoryMeasure_apply_eq_ofReal_setWeight P hP t x
    (leadingOnesFiniteScoreLevelAtHorizonSet x i t)]

end ECRuntime
