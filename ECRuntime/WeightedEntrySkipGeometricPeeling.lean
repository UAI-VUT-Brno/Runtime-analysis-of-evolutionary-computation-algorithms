import ECRuntime.WeightedFirstEntryGeometricFactorization
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 54: weighted entry/skip geometric peeling

Stage 26 fix 53 is compiler verified warning-free.  It proves the geometric peeling
identity for an arbitrary weighted family of histories that eventually enter exact
level `i+1`.  A complete coordinate step must also cover the complementary branch on
which the exact level is permanently skipped.

On the skipped branch the actual level charge is zero, so the comparison failure count
may be sampled freshly from the same canonical geometric law.  At the scalar mass
level, if `skipMass` denotes the already-restricted mass carried by the skip branch,
then assigning failure count `r` contributes

  `skipMass * ((1 - p i)^r * p i)`.

This module combines that fresh skip contribution with the weighted first-entry
factorization from fix 53.  The result is the one-coordinate peeling identity

  `next restricted mass = previous restricted mass * geometric singleton factor`,

provided the previous restricted mass has been decomposed into its weighted-entry and
weighted-skip parts.

The skip mass is intentionally an abstract scalar here.  A later construction still
has to identify it with the actual permanently-skipping part of the previously fixed
failure-prefix event.  No independence or normalization is assumed in this file.
-/

/-- Weighted mass of the visited branch together with a prescribed geometric failure
count `r`.  This names the left-hand side of the fix-53 weighted factorization so it
can be combined cleanly with the permanent-skip branch. -/
noncomputable def weightedFirstEntryGeometricFailurePatternMass
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
    (r : Nat) : Real :=
  Finset.univ.sum fun a : beta =>
    w a *
      (Finset.univ.sum fun coord : FiniteTrajectory Bool
          (firstExactLevelEntryTime V x (paths a) i (hvisit a)) =>
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x (paths a)
            (updateLabelCoordinateStream (labels a) i
              (finiteBoolPrefixStream coord))
            (firstExactLevelEntryTime V x (paths a) i (hvisit a)) *
          bernoulliBoolPrefixWeight (p i)
            (failuresThenSuccessCoordinate r) (r + 1))

/-- The named visited-branch mass is exactly the weighted coordinate-deleted entry mass
times the canonical geometric singleton factor. -/
theorem weightedFirstEntryGeometricFailurePatternMass_eq
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
    weightedFirstEntryGeometricFailurePatternMass
        P V hbound p x paths labels i hvisit w r =
      weightedFirstEntryHistoryComplementMass
          P V hbound p x paths labels i hvisit w *
        ((1 - p i) ^ r * p i) := by
  unfold weightedFirstEntryGeometricFailurePatternMass
  exact
    sum_weightedFirstEntryHistoryCoordinatePrefixes_mul_failuresThenSuccessWeight
      P V hbound p x paths labels i hvisit w r

/-- Fresh geometric failure-count mass attached to an abstract weighted permanent-skip
branch.  The scalar `skipMass` may already contain arbitrary restrictions on previously
peeled coordinates. -/
def weightedPermanentSkipGeometricFailurePatternMass
    (skipMass q : Real) (r : Nat) : Real :=
  skipMass * ((1 - q) ^ r * q)

/-- Total coordinate-deleted mass before peeling the current coordinate, split into the
weighted eventual-entry part and an abstract weighted permanent-skip part. -/
noncomputable def weightedEntrySkipComplementMass
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
    (skipMass : Real) : Real :=
  weightedFirstEntryHistoryComplementMass
      P V hbound p x paths labels i hvisit w +
    skipMass

/-- Combined weighted entry/skip mass for prescribed failure count `r`. -/
noncomputable def weightedEntrySkipGeometricFailurePatternMass
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
    (skipMass : Real)
    (r : Nat) : Real :=
  weightedFirstEntryGeometricFailurePatternMass
      P V hbound p x paths labels i hvisit w r +
    weightedPermanentSkipGeometricFailurePatternMass skipMass (p i) r

/-- Weighted one-coordinate entry/skip peeling.

The current coordinate contributes the same canonical geometric singleton factor on
both eventual-entry and permanent-skip branches.  Therefore it factors from their
sum, leaving exactly the previously accumulated restricted mass. -/
theorem weightedEntrySkipGeometricFailurePatternMass_eq
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
    (skipMass : Real)
    (r : Nat) :
    weightedEntrySkipGeometricFailurePatternMass
        P V hbound p x paths labels i hvisit w skipMass r =
      weightedEntrySkipComplementMass
          P V hbound p x paths labels i hvisit w skipMass *
        ((1 - p i) ^ r * p i) := by
  unfold weightedEntrySkipGeometricFailurePatternMass
  rw [weightedFirstEntryGeometricFailurePatternMass_eq
    P V hbound p x paths labels i hvisit w r]
  unfold weightedPermanentSkipGeometricFailurePatternMass
  unfold weightedEntrySkipComplementMass
  ring

/-- Mass-parameterized one-coordinate peeling theorem.  This is the sequential product
interface: if the already-fixed failure-prefix mass is `mass`, then peeling coordinate
`i` with failure count `r` multiplies that mass by the next geometric singleton
factor. -/
theorem weightedEntrySkipGeometricFailurePatternMass_eq_of_mass
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
    (skipMass mass : Real)
    (r : Nat)
    (hmass : weightedEntrySkipComplementMass
      P V hbound p x paths labels i hvisit w skipMass = mass) :
    weightedEntrySkipGeometricFailurePatternMass
        P V hbound p x paths labels i hvisit w skipMass r =
      mass * ((1 - p i) ^ r * p i) := by
  rw [weightedEntrySkipGeometricFailurePatternMass_eq
    P V hbound p x paths labels i hvisit w skipMass r]
  rw [hmass]

/-- Normalized corollary.  Normalization is explicit and may only be used after the
weighted eventual-entry and weighted permanent-skip masses have been shown to exhaust
the previously restricted branch. -/
theorem weightedEntrySkipGeometricFailurePatternMass_eq_of_normalized
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
    (skipMass : Real)
    (r : Nat)
    (hnorm : weightedEntrySkipComplementMass
      P V hbound p x paths labels i hvisit w skipMass = 1) :
    weightedEntrySkipGeometricFailurePatternMass
        P V hbound p x paths labels i hvisit w skipMass r =
      (1 - p i) ^ r * p i := by
  calc
    weightedEntrySkipGeometricFailurePatternMass
        P V hbound p x paths labels i hvisit w skipMass r =
      (1 : Real) * ((1 - p i) ^ r * p i) :=
        weightedEntrySkipGeometricFailurePatternMass_eq_of_mass
          P V hbound p x paths labels i hvisit w skipMass 1 r hnorm
    _ = (1 - p i) ^ r * p i := by simp

end ECRuntime
