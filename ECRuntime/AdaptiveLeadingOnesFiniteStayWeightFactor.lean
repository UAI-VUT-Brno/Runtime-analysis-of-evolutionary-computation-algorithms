import ECRuntime.AdaptiveLeadingOnesLocalRenewalKernel
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 264 (P01). This is a concrete finite-trajectory factorization for the
adaptive LeadingOnes kernel, not an independence assumption. It is the
adaptive counterpart of the certified fixed-rate finite-path stay lemma.
It conditions only on the current score and handles the complete suffix
through an exact sum over next states.
-/

/-- The finite path weight of occupying level `i` at two consecutive times
is exactly the level-dependent stay probability times the weight of
occupying that level at the previous time. The mutation schedule may vary
arbitrarily at other fitness levels. -/
theorem proposed_leadingOnesAdaptive_finiteSameLevel_setWeight_factor
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    finiteTrajectorySetWeight
        (leadingOnesAdaptiveTransition rate) (t + 1) x
        (leadingOnesFiniteEqualThenExactAtNextSet x i t) =
      (1 - rate i.val * (1 - rate i.val) ^ i.val) *
        finiteTrajectorySetWeight
          (leadingOnesAdaptiveTransition rate) t x
          (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    leadingOnesAdaptiveTransition rate
  change finiteTrajectorySetWeight P (t + 1) x
      (leadingOnesFiniteEqualThenExactAtNextSet x i t) =
    (1 - rate i.val * (1 - rate i.val) ^ i.val) *
      finiteTrajectorySetWeight P t x
        (leadingOnesFiniteScoreLevelAtHorizonSet x i t)
  unfold finiteTrajectorySetWeight
  rw [sum_finiteTrajectory_snoc]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pref _hpref
  by_cases hlevel : leadingOnes (finiteTrajectoryEndpoint x t pref) = i.val
  · have hstay := proposed_leadingOnesAdaptive_exactLevel_stayMass
      rate hrate i (finiteTrajectoryEndpoint x t pref) hlevel
    calc
      (∑ y : BitString n,
          if Fin.snoc pref y ∈ leadingOnesFiniteEqualThenExactAtNextSet x i t then
            finiteTrajectoryWeight P (t + 1) x (Fin.snoc pref y)
          else 0) =
          ∑ y : BitString n,
            if leadingOnes y = i.val then
              finiteTrajectoryWeight P t x pref *
                P (finiteTrajectoryEndpoint x t pref) y
            else 0 := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [finiteTrajectoryWeight_snoc P]
        simp only [leadingOnesFiniteEqualThenExactAtNextSet,
          Set.mem_setOf_eq, Fin.init_snoc, finiteTrajectoryEndpoint_snoc,
          hlevel, true_and]
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
      _ = finiteTrajectoryWeight P t x pref *
          (1 - rate i.val * (1 - rate i.val) ^ i.val) := by
        rw [hstay]
      _ = (1 - rate i.val * (1 - rate i.val) ^ i.val) *
          (if pref ∈ leadingOnesFiniteScoreLevelAtHorizonSet x i t then
            finiteTrajectoryWeight P t x pref else 0) := by
        simp [leadingOnesFiniteScoreLevelAtHorizonSet, hlevel, mul_comm]
  · simp [leadingOnesFiniteEqualThenExactAtNextSet,
      leadingOnesFiniteScoreLevelAtHorizonSet, hlevel]

end ECRuntime
