import ECRuntime.BoundedExactLevelEntryMass
import ECRuntime.MultiLevelCoupledTrajectory
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 39: bounded exact-level entry mass in the adaptive coupled law

Stage 26 fix 38 is compiler verified warning-free.  It defines the bounded probability
mass of finite state trajectories that visit exact level `i+1` by horizon `T`, together
with the complementary no-entry mass.

The adaptive multi-level coupling already has an exact finite state-path marginal:
for every fixed state path, summing over all vector-valued Bernoulli label paths gives
back the original finite trajectory weight.  This module applies that marginal theorem
to the bounded exact-level event.

We define coupled entry and no-entry masses by summing the adaptive coupled path weight
over all state paths and all label-vector paths, with the event depending only on the
state path.  Marginalizing the complete label path then gives exactly the fix-38 state
entry/no-entry masses.  Consequently the coupled event partition is normalized under
a stochastic transition matrix.

This is the concrete finite coupled-history bridge needed before refining the entry
branch by its first-entry time and marginalizing the inactive coordinate locally as in
fixes 35--37.
-/

/-- Bounded mass, in the adaptive multi-level coupled finite law, of state trajectories
that visit exact level `i+1` by horizon `T`.  All vector-label trajectories are summed
out explicitly. -/
noncomputable def boundedCoupledExactLevelEntryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) : Real := by
  classical
  exact Finset.univ.sum fun states : FiniteTrajectory alpha T =>
    Finset.univ.sum fun labels : FiniteTrajectory (Fin m -> Bool) T =>
      if finiteTrajectoryVisitsExactLevel V x states i
      then finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x (zipFiniteTrajectories states labels)
      else 0

/-- Complementary bounded mass, in the adaptive coupled finite law, of state
trajectories that have not visited exact level `i+1` by horizon `T`. -/
noncomputable def boundedCoupledExactLevelNoEntryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) : Real := by
  classical
  exact Finset.univ.sum fun states : FiniteTrajectory alpha T =>
    Finset.univ.sum fun labels : FiniteTrajectory (Fin m -> Bool) T =>
      if finiteTrajectoryVisitsExactLevel V x states i
      then 0
      else finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x (zipFiniteTrajectories states labels)

/-- Marginalizing every vector-label path from the bounded coupled entry event recovers
exactly the bounded state-path entry mass from fix 38.  No stochastic or exit-bound
assumptions are needed because the finite state marginal of the coupling is algebraic. -/
theorem boundedCoupledExactLevelEntryMass_eq_boundedExactLevelEntryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    boundedCoupledExactLevelEntryMass P V hbound p x i T =
      boundedExactLevelEntryMass P V x i T := by
  classical
  unfold boundedCoupledExactLevelEntryMass boundedExactLevelEntryMass
  apply Finset.sum_congr rfl
  intro states _hstates
  by_cases hentry : finiteTrajectoryVisitsExactLevel V x states i
  · simp only [if_pos hentry]
    exact finiteMultiLevelBernoulliCoupledWeight_state_marginal
      P V hbound p T x states
  · simp [hentry]

/-- Marginalizing every vector-label path from the bounded coupled no-entry event
recovers exactly the bounded state-path no-entry mass from fix 38. -/
theorem boundedCoupledExactLevelNoEntryMass_eq_boundedExactLevelNoEntryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    boundedCoupledExactLevelNoEntryMass P V hbound p x i T =
      boundedExactLevelNoEntryMass P V x i T := by
  classical
  unfold boundedCoupledExactLevelNoEntryMass boundedExactLevelNoEntryMass
  apply Finset.sum_congr rfl
  intro states _hstates
  by_cases hentry : finiteTrajectoryVisitsExactLevel V x states i
  · simp [hentry]
  · simp only [if_neg hentry]
    exact finiteMultiLevelBernoulliCoupledWeight_state_marginal
      P V hbound p T x states

/-- Under a stochastic transition matrix, the bounded coupled entry and no-entry
branches form a normalized partition. -/
theorem boundedCoupledExactLevelEntryMass_add_noEntryMass_eq_one
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    boundedCoupledExactLevelEntryMass P V hbound p x i T +
        boundedCoupledExactLevelNoEntryMass P V hbound p x i T = 1 := by
  rw [boundedCoupledExactLevelEntryMass_eq_boundedExactLevelEntryMass
    P V hbound p x i T]
  rw [boundedCoupledExactLevelNoEntryMass_eq_boundedExactLevelNoEntryMass
    P V hbound p x i T]
  exact boundedExactLevelEntryMass_add_noEntryMass_eq_one P hP V x i T

/-- The bounded coupled entry mass inherits the fix-38 nonnegativity bound. -/
theorem boundedCoupledExactLevelEntryMass_nonneg
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    0 <= boundedCoupledExactLevelEntryMass P V hbound p x i T := by
  rw [boundedCoupledExactLevelEntryMass_eq_boundedExactLevelEntryMass
    P V hbound p x i T]
  exact boundedExactLevelEntryMass_nonneg P hP V x i T

/-- The bounded coupled entry mass inherits the fix-38 unit upper bound. -/
theorem boundedCoupledExactLevelEntryMass_le_one
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    boundedCoupledExactLevelEntryMass P V hbound p x i T <= 1 := by
  rw [boundedCoupledExactLevelEntryMass_eq_boundedExactLevelEntryMass
    P V hbound p x i T]
  exact boundedExactLevelEntryMass_le_one P hP V x i T

end ECRuntime
