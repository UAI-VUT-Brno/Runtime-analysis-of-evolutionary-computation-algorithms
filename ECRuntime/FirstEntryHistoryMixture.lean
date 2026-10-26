import ECRuntime.RandomEntryGeometricPattern
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 37: finite first-entry-history mixtures with explicit mass

Stage 26 fix 36 fix 1 is compiler verified warning-free.  For every fixed real
first-entry history, it proves that exhaustive marginalization of the inactive
comparison coordinate before entry leaves the coordinate-deleted history weight times
exactly the geometric pattern mass `(1 - p i)^r * p i`.

The next summation must keep one subtlety explicit: an exact positive fitness level may
be skipped by an elitist trajectory.  Consequently, the family of histories that
actually first enter one exact level need not carry total probability one.  Treating
those histories as a normalized probability mixture would silently assume away level
skipping.

This module therefore sums the fix-36 identity over an arbitrary *finite family of real
first-entry histories with history-dependent entry times* while retaining their total
complement mass as a scalar.  The result is the exact mass-explicit identity

  history-pattern mass = first-entry-history mass * (1 - p_i)^r * p_i.

A normalized-mixture corollary is retained only under an explicit normalization
hypothesis.  A later slice can instantiate the family by concrete bounded coupled
histories, identify its mass with the corresponding level-entry event mass, and add the
skipped-level branch before constructing the full geometric comparison coordinate.
-/

/-- Total coordinate-deleted weight of a finite family of histories that each really
visit exact positive level `i+1`.  The supplied existence witness is allowed to depend
on the history, so the first-entry time can vary across the family. -/
noncomputable def firstEntryHistoryComplementMass
    {alpha beta : Type*} [Fintype alpha] [Fintype beta] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (paths : beta -> Nat -> alpha)
    (labels : beta -> Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : forall a : beta, Exists fun s =>
      V (transitionTrajectoryState x (paths a) s) = i.val + 1) : Real :=
  Finset.univ.sum fun a : beta =>
    preEntryInactiveCoordinateComplementPrefixWeight
      P V hbound p i x (paths a) (labels a)
        (firstExactLevelEntryTime V x (paths a) i (hvisit a))

/-- Sum the fix-36 random-entry geometric-pattern identity over a finite family of
actual first-entry histories.  Each history may have a different first-entry time.
No normalization assumption is made: the common geometric singleton factor pulls out
and the remaining scalar is exactly the total coordinate-deleted history mass. -/
theorem sum_firstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight
    {alpha beta : Type*} [Fintype alpha] [Fintype beta] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (paths : beta -> Nat -> alpha)
    (labels : beta -> Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : forall a : beta, Exists fun s =>
      V (transitionTrajectoryState x (paths a) s) = i.val + 1)
    (r : Nat) :
    (Finset.univ.sum fun a : beta =>
      Finset.univ.sum fun coord : FiniteTrajectory Bool
          (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x (paths a)
            (updateLabelCoordinateStream (labels a) i
              (finiteBoolPrefixStream coord))
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
          bernoulliBoolPrefixWeight (p i)
            (failuresThenSuccessCoordinate r) (r + 1)) =
      firstEntryHistoryComplementMass
        P V hbound p x paths labels i hvisit *
        ((1 - p i) ^ r * p i) := by
  classical
  unfold firstEntryHistoryComplementMass
  calc
    (Finset.univ.sum fun a : beta =>
      Finset.univ.sum fun coord : FiniteTrajectory Bool
          (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x (paths a)
            (updateLabelCoordinateStream (labels a) i
              (finiteBoolPrefixStream coord))
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
          bernoulliBoolPrefixWeight (p i)
            (failuresThenSuccessCoordinate r) (r + 1)) =
        Finset.univ.sum fun a : beta =>
          preEntryInactiveCoordinateComplementPrefixWeight
            P V hbound p i x (paths a) (labels a)
              (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
            ((1 - p i) ^ r * p i) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact
        sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccessWeight_to_firstEntry
          P V hbound p x (paths a) (labels a) i (hvisit a) r
    _ =
        (Finset.univ.sum fun a : beta =>
          preEntryInactiveCoordinateComplementPrefixWeight
            P V hbound p i x (paths a) (labels a)
              (firstExactLevelEntryTime V x (paths a) i (hvisit a))) *
          ((1 - p i) ^ r * p i) := by
      rw [Finset.sum_mul]

/-- Mass-parameterized form of the finite first-entry-history mixture theorem.  This is
the form intended for a later concrete history family, whose total mass will be proved
to equal a bounded level-entry event mass rather than assumed to be one. -/
theorem sum_firstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight_of_mass
    {alpha beta : Type*} [Fintype alpha] [Fintype beta] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (paths : beta -> Nat -> alpha)
    (labels : beta -> Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : forall a : beta, Exists fun s =>
      V (transitionTrajectoryState x (paths a) s) = i.val + 1)
    (r : Nat) (mass : Real)
    (hmass : firstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit = mass) :
    (Finset.univ.sum fun a : beta =>
      Finset.univ.sum fun coord : FiniteTrajectory Bool
          (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x (paths a)
            (updateLabelCoordinateStream (labels a) i
              (finiteBoolPrefixStream coord))
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
          bernoulliBoolPrefixWeight (p i)
            (failuresThenSuccessCoordinate r) (r + 1)) =
      mass * ((1 - p i) ^ r * p i) := by
  rw [sum_firstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight
    P V hbound p x paths labels i hvisit r, hmass]

/-- If a particular finite first-entry-history family is explicitly known to have total
mass one, its geometric continuation has exactly the canonical singleton mass.  The
normalization is a hypothesis, not a default property of exact-level histories. -/
theorem sum_firstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight_of_normalized
    {alpha beta : Type*} [Fintype alpha] [Fintype beta] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha)
    (paths : beta -> Nat -> alpha)
    (labels : beta -> Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : forall a : beta, Exists fun s =>
      V (transitionTrajectoryState x (paths a) s) = i.val + 1)
    (r : Nat)
    (hnorm : firstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit = 1) :
    (Finset.univ.sum fun a : beta =>
      Finset.univ.sum fun coord : FiniteTrajectory Bool
          (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x (paths a)
            (updateLabelCoordinateStream (labels a) i
              (finiteBoolPrefixStream coord))
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
          bernoulliBoolPrefixWeight (p i)
            (failuresThenSuccessCoordinate r) (r + 1)) =
      (1 - p i) ^ r * p i := by
  calc
    (Finset.univ.sum fun a : beta =>
      Finset.univ.sum fun coord : FiniteTrajectory Bool
          (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x (paths a)
            (updateLabelCoordinateStream (labels a) i
              (finiteBoolPrefixStream coord))
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
          bernoulliBoolPrefixWeight (p i)
            (failuresThenSuccessCoordinate r) (r + 1)) =
        (1 : Real) * ((1 - p i) ^ r * p i) :=
      sum_firstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight_of_mass
        P V hbound p x paths labels i hvisit r 1 hnorm
    _ = (1 - p i) ^ r * p i := by simp

end ECRuntime
