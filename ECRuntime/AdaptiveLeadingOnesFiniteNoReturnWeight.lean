import ECRuntime.AdaptiveLeadingOnesLocalRenewalKernel
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 270 (P01, new proposal). Exact path-weight exclusion of an
above-level-to-exact-level transition under a nonconstant adaptive
mutation schedule. This supplies the third, zero-mass branch needed
for a genuine occupation/entry recurrence at a fixed LeadingOnes level.
-/

/-- Paths whose score is already strictly above level `i` at time `t`,
but exactly `i` at time `t+1`. -/
def leadingOnesFiniteAboveThenExactAtNextSet
    {n : Nat} (x : BitString n) (i : Fin n) (t : Nat) :
    Set (FiniteTrajectory (BitString n) (t + 1)) :=
  {path | i.val < leadingOnes (finiteTrajectoryEndpoint x t (Fin.init path)) ∧
    leadingOnes (finiteTrajectoryEndpoint x (t + 1) path) = i.val}

/-- No finite trajectory of positive adaptive path weight can return
from a strictly higher LeadingOnes level to the fixed lower level. -/
theorem proposed_leadingOnesAdaptive_finiteAboveThenExact_setWeight_zero
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    finiteTrajectorySetWeight
        (leadingOnesAdaptiveTransition rate) (t + 1) x
        (leadingOnesFiniteAboveThenExactAtNextSet x i t) = 0 := by
  classical
  let P : TransitionMatrix (BitString n) :=
    leadingOnesAdaptiveTransition rate
  change finiteTrajectorySetWeight P (t + 1) x
    (leadingOnesFiniteAboveThenExactAtNextSet x i t) = 0
  unfold finiteTrajectorySetWeight
  rw [sum_finiteTrajectory_snoc, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro pref _hpref
  by_cases habove : i.val < leadingOnes (finiteTrajectoryEndpoint x t pref)
  · calc
      (∑ y : BitString n,
          if Fin.snoc pref y ∈ leadingOnesFiniteAboveThenExactAtNextSet x i t
          then finiteTrajectoryWeight P (t + 1) x (Fin.snoc pref y)
          else 0) =
          ∑ y : BitString n,
            if leadingOnes y = i.val then
              finiteTrajectoryWeight P t x pref *
                P (finiteTrajectoryEndpoint x t pref) y
            else 0 := by
              apply Finset.sum_congr rfl
              intro y _hy
              rw [finiteTrajectoryWeight_snoc P]
              simp only [leadingOnesFiniteAboveThenExactAtNextSet,
                Set.mem_setOf_eq, Fin.init_snoc,
                finiteTrajectoryEndpoint_snoc, habove, true_and]
      _ = finiteTrajectoryWeight P t x pref *
            finiteEventMass (P (finiteTrajectoryEndpoint x t pref))
              (fun y => leadingOnes y = i.val) := by
              unfold finiteEventMass
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _hy
              by_cases hy : leadingOnes y = i.val
              · simp [hy]
              · simp [hy]
      _ = finiteTrajectoryWeight P t x pref * 0 := by
              rw [proposed_leadingOnesAdaptive_aboveLevel_returnMass_zero
                rate hrate i (finiteTrajectoryEndpoint x t pref) habove]
      _ = 0 := by simp
  · simp [leadingOnesFiniteAboveThenExactAtNextSet, habove]


/-- Under the genuine finite-trajectory probability measure, a transition
from strictly above level `i` back to `i` has measure zero. -/
theorem proposed_leadingOnesAdaptive_finiteAboveThenExact_measure_zero
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    finiteTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
      (t + 1) x (leadingOnesFiniteAboveThenExactAtNextSet x i t) = 0 := by
  classical
  rw [finiteTrajectoryMeasure_apply_eq_ofReal_setWeight]
  rw [proposed_leadingOnesAdaptive_finiteAboveThenExact_setWeight_zero
    rate hrate x i t]
  simp

end ECRuntime
