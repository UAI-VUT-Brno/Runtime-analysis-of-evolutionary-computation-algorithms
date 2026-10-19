import ECRuntime.FirstEntryHistoryMixture
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 53: weighted first-entry geometric factorization

Stage 26 fix 52 fix 1 is compiler verified warning-free.  It reduces the remaining
full coupling problem to a coupling on finite vectors of natural geometric failure
counts.  To prove that the second marginal is the *product* of the coordinate laws,
one cannot simply multiply the already verified one-coordinate marginals: after some
higher-level failure counts have been fixed, the next random-entry argument must remain
valid under the corresponding history restriction.

This module strengthens the finite first-entry-history mixture from fix 37 by allowing
an arbitrary outer coefficient on every real first-entry history.  The coefficient may
encode any constraints already imposed on other coordinates.  Since coordinate `i` is
inactive before its first exact-level entry, exhaustive marginalization of its pre-entry
prefix still pulls out the same geometric factor `(1 - p i)^r * p i`, regardless of
those outer weights.

This is the algebraic "peeling" statement needed for a sequential proof of complete
failure-vector singleton masses.  No normalization and no independence assumption is
made here.  The next construction may instantiate the outer weights by the mass of an
already-fixed prefix of higher-level failure coordinates, then peel the next coordinate
without disturbing that prefix mass.
-/

/-- Coordinate-deleted first-entry-history mass with an arbitrary outer coefficient.
The coefficient is deliberately unrestricted: later it can encode already-fixed
failure-coordinate constraints. -/
noncomputable def weightedFirstEntryHistoryComplementMass
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
    (w : beta -> Real) : Real :=
  Finset.univ.sum fun a : beta =>
    w a *
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x (paths a) (labels a)
          (firstExactLevelEntryTime V x (paths a) i (hvisit a))

/-- Weighted geometric peeling at a history-dependent first-entry time.

The outer coefficient `w a` is untouched by marginalization of coordinate `i`; hence
any previously imposed history/failure constraints can be carried through the next
geometric factor. -/
theorem sum_weightedFirstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight
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
    (w : beta -> Real)
    (r : Nat) :
    (Finset.univ.sum fun a : beta =>
      w a *
        (Finset.univ.sum fun coord : FiniteTrajectory Bool
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x (paths a)
              (updateLabelCoordinateStream (labels a) i
                (finiteBoolPrefixStream coord))
              (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
            bernoulliBoolPrefixWeight (p i)
              (failuresThenSuccessCoordinate r) (r + 1))) =
      weightedFirstEntryHistoryComplementMass
        P V hbound p x paths labels i hvisit w *
        ((1 - p i) ^ r * p i) := by
  classical
  unfold weightedFirstEntryHistoryComplementMass
  calc
    (Finset.univ.sum fun a : beta =>
      w a *
        (Finset.univ.sum fun coord : FiniteTrajectory Bool
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x (paths a)
              (updateLabelCoordinateStream (labels a) i
                (finiteBoolPrefixStream coord))
              (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
            bernoulliBoolPrefixWeight (p i)
              (failuresThenSuccessCoordinate r) (r + 1))) =
        Finset.univ.sum fun a : beta =>
          w a *
            (preEntryInactiveCoordinateComplementPrefixWeight
              P V hbound p i x (paths a) (labels a)
                (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
              ((1 - p i) ^ r * p i)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccessWeight_to_firstEntry
        P V hbound p x (paths a) (labels a) i (hvisit a) r]
    _ = Finset.univ.sum fun a : beta =>
          (w a *
            preEntryInactiveCoordinateComplementPrefixWeight
              P V hbound p i x (paths a) (labels a)
                (firstExactLevelEntryTime V x (paths a) i (hvisit a))) *
            ((1 - p i) ^ r * p i) := by
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = (Finset.univ.sum fun a : beta =>
          w a *
            preEntryInactiveCoordinateComplementPrefixWeight
              P V hbound p i x (paths a) (labels a)
                (firstExactLevelEntryTime V x (paths a) i (hvisit a))) *
          ((1 - p i) ^ r * p i) := by
      rw [Finset.sum_mul]

/-- Mass-parameterized form of weighted geometric peeling.  This is the convenient
sequential-induction interface: once the weighted complement mass for the already-fixed
failure prefix has been identified with `mass`, peeling coordinate `i` multiplies it by
exactly the next geometric singleton factor. -/
theorem sum_weightedFirstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight_of_mass
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
    (w : beta -> Real)
    (r : Nat) (mass : Real)
    (hmass : weightedFirstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit w = mass) :
    (Finset.univ.sum fun a : beta =>
      w a *
        (Finset.univ.sum fun coord : FiniteTrajectory Bool
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x (paths a)
              (updateLabelCoordinateStream (labels a) i
                (finiteBoolPrefixStream coord))
              (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
            bernoulliBoolPrefixWeight (p i)
              (failuresThenSuccessCoordinate r) (r + 1))) =
      mass * ((1 - p i) ^ r * p i) := by
  rw [sum_weightedFirstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight
    P V hbound p x paths labels i hvisit w r, hmass]

/-- Normalized weighted form.  Unlike the original unweighted normalized corollary,
this permits normalization only *after* arbitrary other-coordinate restrictions have
been folded into `w`. -/
theorem sum_weightedFirstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight_of_normalized
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
    (w : beta -> Real)
    (r : Nat)
    (hnorm : weightedFirstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit w = 1) :
    (Finset.univ.sum fun a : beta =>
      w a *
        (Finset.univ.sum fun coord : FiniteTrajectory Bool
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x (paths a)
              (updateLabelCoordinateStream (labels a) i
                (finiteBoolPrefixStream coord))
              (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
            bernoulliBoolPrefixWeight (p i)
              (failuresThenSuccessCoordinate r) (r + 1))) =
      (1 - p i) ^ r * p i := by
  calc
    (Finset.univ.sum fun a : beta =>
      w a *
        (Finset.univ.sum fun coord : FiniteTrajectory Bool
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x (paths a)
              (updateLabelCoordinateStream (labels a) i
                (finiteBoolPrefixStream coord))
              (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
            bernoulliBoolPrefixWeight (p i)
              (failuresThenSuccessCoordinate r) (r + 1))) =
        (1 : Real) * ((1 - p i) ^ r * p i) :=
      sum_weightedFirstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight_of_mass
        P V hbound p x paths labels i hvisit w r 1 hnorm
    _ = (1 - p i) ^ r * p i := by simp

end ECRuntime
