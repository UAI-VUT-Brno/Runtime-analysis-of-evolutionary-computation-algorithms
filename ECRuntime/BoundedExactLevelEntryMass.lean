import ECRuntime.FirstEntryHistoryMixture
import ECRuntime.FiniteTrajectory
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 38: bounded exact-level entry and no-entry masses

Stage 26 fix 37 compiler-verifies the finite first-entry-history mixture with an
explicit total history mass `M`.  The next task is to identify the scalar represented
by `M` without assuming that an exact positive level must be reached.  The existing
finite-trajectory semantics already provide the right normalized finite probability
space for a first concrete bridge.

For a fixed horizon `T`, this module partitions every finite state trajectory according
to whether the supplied initial state or one of the next `T` states visits exact level
`i+1`.  It defines the corresponding entry-by-horizon and no-entry-by-horizon masses
under `finiteTrajectoryWeight`, proves that the two masses add to the total finite-path
mass, and specializes the result to a stochastic transition matrix, where the total is
one.  Nonnegativity then yields the expected `[0,1]` bounds.

This is deliberately a bounded statement.  The no-entry branch contains trajectories
that have not reached the exact level by time `T`; some may enter later and some may
skip the exact level forever.  A later slice can identify the coordinate-deleted
first-entry-history mass from fix 37 with the bounded entry mass constructed here,
before passing to increasing horizons or the infinite trajectory law.
-/

/-- A finite state trajectory visits exact positive level `i+1` by horizon `T` when
that level is already present at time zero or occurs among one of its next `T` states. -/
def finiteTrajectoryVisitsExactLevel
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha)
    (path : FiniteTrajectory alpha T) (i : Fin m) : Prop :=
  V x = i.val + 1 ∨ ∃ t : Fin T, V (path t) = i.val + 1

/-- Probability mass of finite trajectories that visit exact level `i+1` by the
specified horizon. -/
noncomputable def boundedExactLevelEntryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) : Real := by
  classical
  exact Finset.univ.sum fun path : FiniteTrajectory alpha T =>
    if finiteTrajectoryVisitsExactLevel V x path i
    then finiteTrajectoryWeight P T x path
    else 0

/-- Complementary finite-horizon mass of trajectories that have not visited exact level
`i+1` by time `T`.  This is a bounded no-entry event, not yet the event of skipping the
level forever. -/
noncomputable def boundedExactLevelNoEntryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) : Real := by
  classical
  exact Finset.univ.sum fun path : FiniteTrajectory alpha T =>
    if finiteTrajectoryVisitsExactLevel V x path i
    then 0
    else finiteTrajectoryWeight P T x path

/-- Entry and no-entry branches partition the complete finite path sum exactly, without
requiring stochastic normalization. -/
theorem boundedExactLevelEntryMass_add_noEntryMass_eq_total
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    boundedExactLevelEntryMass P V x i T +
        boundedExactLevelNoEntryMass P V x i T =
      Finset.univ.sum fun path : FiniteTrajectory alpha T =>
        finiteTrajectoryWeight P T x path := by
  classical
  unfold boundedExactLevelEntryMass boundedExactLevelNoEntryMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro path _hpath
  by_cases hentry : finiteTrajectoryVisitsExactLevel V x path i
  · simp [hentry]
  · simp [hentry]

/-- For a stochastic transition matrix, bounded exact-level entry and bounded no-entry
masses form a normalized partition. -/
theorem boundedExactLevelEntryMass_add_noEntryMass_eq_one
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    boundedExactLevelEntryMass P V x i T +
        boundedExactLevelNoEntryMass P V x i T = 1 := by
  rw [boundedExactLevelEntryMass_add_noEntryMass_eq_total P V x i T]
  exact finiteTrajectoryWeight_sum P hP T x

/-- The bounded entry mass is nonnegative under stochastic finite-path weights. -/
theorem boundedExactLevelEntryMass_nonneg
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    0 <= boundedExactLevelEntryMass P V x i T := by
  classical
  unfold boundedExactLevelEntryMass
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hentry : finiteTrajectoryVisitsExactLevel V x path i
  · simpa [hentry] using finiteTrajectoryWeight_nonneg P hP T x path
  · simp [hentry]

/-- The bounded no-entry mass is nonnegative under stochastic finite-path weights. -/
theorem boundedExactLevelNoEntryMass_nonneg
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    0 <= boundedExactLevelNoEntryMass P V x i T := by
  classical
  unfold boundedExactLevelNoEntryMass
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hentry : finiteTrajectoryVisitsExactLevel V x path i
  · simp [hentry]
  · simpa [hentry] using finiteTrajectoryWeight_nonneg P hP T x path

/-- The bounded exact-level entry mass is at most one. -/
theorem boundedExactLevelEntryMass_le_one
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    boundedExactLevelEntryMass P V x i T <= 1 := by
  have hsum := boundedExactLevelEntryMass_add_noEntryMass_eq_one P hP V x i T
  have hcomp := boundedExactLevelNoEntryMass_nonneg P hP V x i T
  linarith

/-- The bounded no-entry mass is at most one. -/
theorem boundedExactLevelNoEntryMass_le_one
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    boundedExactLevelNoEntryMass P V x i T <= 1 := by
  have hsum := boundedExactLevelEntryMass_add_noEntryMass_eq_one P hP V x i T
  have hentry := boundedExactLevelEntryMass_nonneg P hP V x i T
  linarith

/-- The no-entry branch is exactly the complement of the bounded entry mass. -/
theorem boundedExactLevelNoEntryMass_eq_one_sub_entryMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    boundedExactLevelNoEntryMass P V x i T =
      1 - boundedExactLevelEntryMass P V x i T := by
  have hsum := boundedExactLevelEntryMass_add_noEntryMass_eq_one P hP V x i T
  linarith

end ECRuntime
