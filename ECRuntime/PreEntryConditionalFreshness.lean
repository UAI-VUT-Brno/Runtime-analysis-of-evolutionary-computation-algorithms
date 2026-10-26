import ECRuntime.PreEntryPrefixFactorization
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 34: ratio-free conditional freshness at random entry

Stage 26 fix 33 fix 1 compiler-verifies exact factorization of every finite coupled
prefix ending no later than the actual first entry into exact level `i+1`.  The full
prefix weight is the scalar Bernoulli prefix weight of coordinate `i` times a
complement that is unchanged when that coordinate stream is replaced.

The next random-entry argument will sum over finite first-entry histories.  Dividing by
the probability of such a history would introduce avoidable positivity side conditions.
This module instead records ratio-free cross-multiplication and finite-sum forms of the
verified factorization.  These identities say that all dependence on the pre-entry
coordinate pattern is carried by its scalar Bernoulli prefix factor, while the actual
entry history contributes a common complementary factor.

This is the finite algebraic interface needed before the next slice enumerates concrete
first-entry histories and attaches the already verified fixed-restart geometric law to
the post-entry suffix.
-/

/-- Two replacements of an inactive coordinate satisfy a ratio-free cross-product
identity on every prefix ending no later than first entry.  No division or positivity
assumption is required. -/
theorem multiLevelBernoulliCoupledPrefixWeight_update_coordinate_cross_mul_before_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord1 coord2 : Nat -> Bool) (T : Nat)
    (hT : T <= firstExactLevelEntryTime V x path i hvisit) :
    bernoulliBoolPrefixWeight (p i) coord2 T *
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x path
            (updateLabelCoordinateStream labels i coord1) T =
      bernoulliBoolPrefixWeight (p i) coord1 T *
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x path
            (updateLabelCoordinateStream labels i coord2) T := by
  rw [
    multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
      P V hbound p x path labels i hvisit coord1 T hT,
    multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
      P V hbound p x path labels i hvisit coord2 T hT
  ]
  ring

/-- Exact first-entry specialization of the ratio-free cross-product identity. -/
theorem multiLevelBernoulliCoupledPrefixWeight_update_coordinate_cross_mul_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord1 coord2 : Nat -> Bool) :
    bernoulliBoolPrefixWeight (p i) coord2
        (firstExactLevelEntryTime V x path i hvisit) *
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x path
            (updateLabelCoordinateStream labels i coord1)
            (firstExactLevelEntryTime V x path i hvisit) =
      bernoulliBoolPrefixWeight (p i) coord1
        (firstExactLevelEntryTime V x path i hvisit) *
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x path
            (updateLabelCoordinateStream labels i coord2)
            (firstExactLevelEntryTime V x path i hvisit) := by
  exact
    multiLevelBernoulliCoupledPrefixWeight_update_coordinate_cross_mul_before_firstEntry
      P V hbound p x path labels i hvisit coord1 coord2
      (firstExactLevelEntryTime V x path i hvisit) le_rfl

/-- Equal scalar Bernoulli prefix masses imply equal coupled prefix masses before first
entry, because the complementary first-entry-history factor is shared. -/
theorem multiLevelBernoulliCoupledPrefixWeight_update_coordinate_eq_of_prefixWeight_eq_before_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord1 coord2 : Nat -> Bool) (T : Nat)
    (hT : T <= firstExactLevelEntryTime V x path i hvisit)
    (hcoord : bernoulliBoolPrefixWeight (p i) coord1 T =
      bernoulliBoolPrefixWeight (p i) coord2 T) :
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord1) T =
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord2) T := by
  calc
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord1) T =
      bernoulliBoolPrefixWeight (p i) coord1 T *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T :=
      multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
        P V hbound p x path labels i hvisit coord1 T hT
    _ = bernoulliBoolPrefixWeight (p i) coord2 T *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T := by rw [hcoord]
    _ = multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord2) T :=
      (multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
        P V hbound p x path labels i hvisit coord2 T hT).symm

/-- Exact first-entry specialization of equality under equal Bernoulli prefix mass. -/
theorem multiLevelBernoulliCoupledPrefixWeight_update_coordinate_eq_of_prefixWeight_eq_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord1 coord2 : Nat -> Bool)
    (hcoord : bernoulliBoolPrefixWeight (p i) coord1
        (firstExactLevelEntryTime V x path i hvisit) =
      bernoulliBoolPrefixWeight (p i) coord2
        (firstExactLevelEntryTime V x path i hvisit)) :
    multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord1)
          (firstExactLevelEntryTime V x path i hvisit) =
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i coord2)
          (firstExactLevelEntryTime V x path i hvisit) := by
  exact
    multiLevelBernoulliCoupledPrefixWeight_update_coordinate_eq_of_prefixWeight_eq_before_firstEntry
      P V hbound p x path labels i hvisit coord1 coord2
      (firstExactLevelEntryTime V x path i hvisit) le_rfl hcoord

/-- The original prefix and any coordinate-replaced prefix satisfy the same ratio-free
identity at first entry.  This form will be useful when a concrete history is held fixed
while its inactive coordinate pattern is summed out. -/
theorem multiLevelBernoulliCoupledPrefixWeight_original_update_cross_mul_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coord : Nat -> Bool) :
    bernoulliBoolPrefixWeight (p i) coord
        (firstExactLevelEntryTime V x path i hvisit) *
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x path labels
          (firstExactLevelEntryTime V x path i hvisit) =
      bernoulliBoolPrefixWeight (p i) (fun t => labels t i)
        (firstExactLevelEntryTime V x path i hvisit) *
        multiLevelBernoulliCoupledPrefixWeight
          P V hbound p x path
            (updateLabelCoordinateStream labels i coord)
            (firstExactLevelEntryTime V x path i hvisit) := by
  rw [
    multiLevelBernoulliCoupledPrefixWeight_eq_coordinate_mul_complement_to_firstEntry
      P V hbound p x path labels i hvisit,
    multiLevelBernoulliCoupledPrefixWeight_update_coordinate_to_firstEntry
      P V hbound p x path labels i hvisit coord
  ]
  ring

/-- Summing over any finite family of replacement coordinate streams preserves the
same complementary first-entry-history factor.  This is the algebraic form needed when
concrete pre-entry patterns are enumerated. -/
theorem sum_multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    {beta : Type*} [Fintype beta]
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coords : beta -> Nat -> Bool) (T : Nat)
    (hT : T <= firstExactLevelEntryTime V x path i hvisit) :
    (Finset.univ.sum fun a =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i (coords a)) T) =
      (Finset.univ.sum fun a =>
        bernoulliBoolPrefixWeight (p i) (coords a) T) *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T := by
  calc
    (Finset.univ.sum fun a =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i (coords a)) T) =
      Finset.univ.sum (fun a =>
        bernoulliBoolPrefixWeight (p i) (coords a) T *
          preEntryInactiveCoordinateComplementPrefixWeight
            P V hbound p i x path labels T) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact
        multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
          P V hbound p x path labels i hvisit (coords a) T hT
    _ = (Finset.univ.sum fun a =>
        bernoulliBoolPrefixWeight (p i) (coords a) T) *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels T := by
      rw [Finset.sum_mul]

/-- Exact first-entry specialization of the finite-family factorization. -/
theorem sum_multiLevelBernoulliCoupledPrefixWeight_update_coordinate_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    {beta : Type*} [Fintype beta]
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (coords : beta -> Nat -> Bool) :
    (Finset.univ.sum fun a =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i (coords a))
          (firstExactLevelEntryTime V x path i hvisit)) =
      (Finset.univ.sum fun a =>
        bernoulliBoolPrefixWeight (p i) (coords a)
          (firstExactLevelEntryTime V x path i hvisit)) *
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x path labels
          (firstExactLevelEntryTime V x path i hvisit) := by
  exact
    sum_multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
      P V hbound p x path labels i hvisit coords
      (firstExactLevelEntryTime V x path i hvisit) le_rfl

/-- Pulling a common scalar out of a finite weighted mixture.  This small generic lemma
is recorded here because the next first-entry-history sum has exactly this shape. -/
theorem finiteWeightedMixture_constant
    {beta : Type*} [Fintype beta]
    (w : beta -> Real) (c : Real) :
    (Finset.univ.sum fun a => w a * c) =
      (Finset.univ.sum w) * c := by
  rw [Finset.sum_mul]

/-- A normalized finite mixture of a common constant is that constant. -/
theorem finiteProbabilityMixture_constant
    {beta : Type*} [Fintype beta]
    (w : beta -> Real) (c : Real)
    (hw : Finset.univ.sum w = 1) :
    (Finset.univ.sum fun a => w a * c) = c := by
  calc
    (Finset.univ.sum fun a => w a * c) =
        (Finset.univ.sum w) * c := finiteWeightedMixture_constant w c
    _ = c := by rw [hw, one_mul]

end ECRuntime
