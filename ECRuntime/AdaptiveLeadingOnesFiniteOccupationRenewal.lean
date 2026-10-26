import ECRuntime.AdaptiveLeadingOnesFiniteNoReturnWeight
import ECRuntime.AdaptiveLeadingOnesFiniteStayWeightFactor
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Stage 273 (P01, dependent research candidate). This is the finite-
horizon renewal equation that still separates genuine first entry from
geometric residence. Its proof must be elaborated only after Stage 270
is fully certified. It deliberately does not assert Stage 245's
countable expected-runtime identity.
-/

/-- Paths ending exactly at `i` at time `t+1`. -/
def leadingOnesFiniteExactAtNextSet
    {n : Nat} (x : BitString n) (i : Fin n) (t : Nat) :
    Set (FiniteTrajectory (BitString n) (t + 1)) :=
  {path | leadingOnes (finiteTrajectoryEndpoint x (t + 1) path) = i.val}

/-- Paths entering `i` at time `t+1` from a strictly lower level. -/
def leadingOnesFiniteBelowThenExactAtNextSet
    {n : Nat} (x : BitString n) (i : Fin n) (t : Nat) :
    Set (FiniteTrajectory (BitString n) (t + 1)) :=
  {path | leadingOnes (finiteTrajectoryEndpoint x t (Fin.init path)) < i.val ∧
    leadingOnes (finiteTrajectoryEndpoint x (t + 1) path) = i.val}

/-- Exact finite-horizon adaptive occupation renewal: occupation at
`t+1` is first entry from below plus same-level residence. The branch
from above vanishes by the certified no-return lemma. -/
theorem proposed_leadingOnesAdaptive_finiteOccupation_oneStep_renewal
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (i : Fin n) (t : Nat) :
    finiteTrajectorySetWeight (leadingOnesAdaptiveTransition rate) (t + 1) x
      (leadingOnesFiniteExactAtNextSet x i t) =
    finiteTrajectorySetWeight (leadingOnesAdaptiveTransition rate) (t + 1) x
      (leadingOnesFiniteBelowThenExactAtNextSet x i t) +
    (1 - rate i.val * (1 - rate i.val) ^ i.val) *
      finiteTrajectorySetWeight (leadingOnesAdaptiveTransition rate) t x
        (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    leadingOnesAdaptiveTransition rate
  have hpartition :
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteExactAtNextSet x i t) =
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteBelowThenExactAtNextSet x i t) +
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteEqualThenExactAtNextSet x i t) +
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteAboveThenExactAtNextSet x i t) := by
    unfold finiteTrajectorySetWeight
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro path _hpath
    -- This is a *pointwise* partition.  Normalize both endpoint notations
    -- to the same last-state expression before splitting the cases.
    -- In particular, the negated next-level case requires no probabilistic
    -- argument: each of the four indicators is identically zero.
    simp only [leadingOnesFiniteExactAtNextSet,
      leadingOnesFiniteBelowThenExactAtNextSet,
      leadingOnesFiniteEqualThenExactAtNextSet,
      leadingOnesFiniteAboveThenExactAtNextSet,
      Set.mem_setOf_eq, finiteTrajectoryEndpoint_succ]
    split_ifs <;> simp_all <;> omega
  change finiteTrajectorySetWeight P (t + 1) x
      (leadingOnesFiniteExactAtNextSet x i t) =
    finiteTrajectorySetWeight P (t + 1) x
      (leadingOnesFiniteBelowThenExactAtNextSet x i t) +
      (1 - rate i.val * (1 - rate i.val) ^ i.val) *
      finiteTrajectorySetWeight P t x
        (leadingOnesFiniteScoreLevelAtHorizonSet x i t)
  calc
    finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteExactAtNextSet x i t) =
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteBelowThenExactAtNextSet x i t) +
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteEqualThenExactAtNextSet x i t) +
      finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteAboveThenExactAtNextSet x i t) := hpartition
    _ = finiteTrajectorySetWeight P (t + 1) x
          (leadingOnesFiniteBelowThenExactAtNextSet x i t) +
        (1 - rate i.val * (1 - rate i.val) ^ i.val) *
          finiteTrajectorySetWeight P t x
            (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
          rw [proposed_leadingOnesAdaptive_finiteSameLevel_setWeight_factor
              rate hrate x i t,
              proposed_leadingOnesAdaptive_finiteAboveThenExact_setWeight_zero
              rate hrate x i t]
          ring

end ECRuntime
