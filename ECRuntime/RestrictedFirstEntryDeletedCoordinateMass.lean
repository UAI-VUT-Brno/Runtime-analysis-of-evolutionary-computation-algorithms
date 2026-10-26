import ECRuntime.RestrictedFirstEntryFiniteCylinder
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 58: deleted-coordinate exact-time mass

Stage 26 fix 57 is compiler verified warning-free.  It localizes every genuinely
restricted exact first-entry event to a finite coupled prefix and makes restrictions
that ignore the currently peeled coordinate `i` structural, via
`finiteCoupledDeletedCoordinateProjection`.

The remaining fixed-time task is to evaluate the finite full-label mass after summing
out coordinate `i`.  This file performs that marginalization at the level of complete
finite trajectories.

A finite full label vector is reconstructed from its deleted-coordinate representative
and one Boolean value.  Coordinatewise this gives an equivalence between full coupled
prefixes and

```
(deleted-coordinate coupled prefix, coordinate-i Boolean prefix).
```

The one-step sum over the Boolean coordinate is exactly
`inactiveCoordinateMarginalStepWeight` from fix 43.  The generic finite labelled-path
state-marginal theorem therefore gives an exact path-fiber identity: summing the full
adaptive coupled weight over every Boolean prefix above one fixed deleted-coordinate
prefix equals `finiteInactiveCoordinateMarginalWeight`.

On a terminal first-entry prefix, fix 43 already identifies that marginal path weight
with `preEntryInactiveCoordinateComplementPrefixWeight`.  Summing only the deleted
prefixes in an outer restriction `C` therefore defines a concrete finite restricted
complement mass.  The final theorems identify both the finite coupled measure and the
genuine infinite adaptive exact-time restricted slice with `ENNReal.ofReal` of this
mass.

The next stage only has to repackage this finite restricted complement sum as the
`weightedFirstEntryHistoryComplementMass` interface from fix 53 (using the finite
subtype of deleted prefixes satisfying the restriction and terminal-entry predicate).
Fix 56 can then reassemble the exact-time slices by `tsum`.
-/

/-- Recover a full finite coupled prefix from a deleted-coordinate prefix and the
missing Boolean trajectory. -/
def finiteCoupledInsertDeletedCoordinate
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)
    (coord : FiniteTrajectory Bool T) :
    FiniteTrajectory (alpha × (Fin m -> Bool)) T :=
  fun t => ((path t).1, Function.update (path t).2.val i (coord t))

/-- Read coordinate `i` from every full vector label in a finite coupled prefix. -/
def finiteCoupledCoordinateProjection
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) T) :
    FiniteTrajectory Bool T :=
  fun t => (path t).2 i

@[simp] theorem inactiveCoordinateRepresentative_val
    {m : Nat} (i : Fin m) (base : InactiveCoordinateLabelVector i) :
    inactiveCoordinateRepresentative i base.val = base := by
  apply Subtype.ext
  funext j
  by_cases hji : j = i
  · subst j
    simp [inactiveCoordinateRepresentative, base.property]
  · simp [inactiveCoordinateRepresentative, hji]

@[simp] theorem finiteCoupledDeletedCoordinateProjection_insertDeletedCoordinate
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)
    (coord : FiniteTrajectory Bool T) :
    finiteCoupledDeletedCoordinateProjection i
        (finiteCoupledInsertDeletedCoordinate i path coord) = path := by
  funext t
  apply Prod.ext
  · rfl
  · change inactiveCoordinateRepresentative i
        (Function.update (path t).2.val i (coord t)) = (path t).2
    rw [inactiveCoordinateRepresentative_update_self,
      inactiveCoordinateRepresentative_val]

@[simp] theorem finiteCoupledCoordinateProjection_insertDeletedCoordinate
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)
    (coord : FiniteTrajectory Bool T) :
    finiteCoupledCoordinateProjection i
        (finiteCoupledInsertDeletedCoordinate i path coord) = coord := by
  funext t
  simp [finiteCoupledCoordinateProjection,
    finiteCoupledInsertDeletedCoordinate]

/-- Reconstructing a full prefix from its two coordinatewise projections is exact. -/
@[simp] theorem finiteCoupledInsertDeletedCoordinate_projections
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) T) :
    finiteCoupledInsertDeletedCoordinate i
        (finiteCoupledDeletedCoordinateProjection i path)
        (finiteCoupledCoordinateProjection i path) = path := by
  funext t
  apply Prod.ext
  · rfl
  · exact (inactiveCoordinateLabelVectorBoolEquiv i).right_inv (path t).2

/-- Full finite coupled prefixes are equivalent to a deleted-coordinate prefix together
with the missing Boolean trajectory. -/
def finiteCoupledDeletedCoordinateBoolEquiv
    {alpha : Type*} {m T : Nat} (i : Fin m) :
    FiniteTrajectory (alpha × (Fin m -> Bool)) T ≃
      FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T ×
        FiniteTrajectory Bool T where
  toFun path :=
    (finiteCoupledDeletedCoordinateProjection i path,
      finiteCoupledCoordinateProjection i path)
  invFun z := finiteCoupledInsertDeletedCoordinate i z.1 z.2
  left_inv path := finiteCoupledInsertDeletedCoordinate_projections i path
  right_inv z := by
    rcases z with ⟨path, coord⟩
    apply Prod.ext
    · exact finiteCoupledDeletedCoordinateProjection_insertDeletedCoordinate
        i path coord
    · exact finiteCoupledCoordinateProjection_insertDeletedCoordinate
        i path coord

@[simp] theorem finiteCoupledStateProjection_deletedCoordinateProjection
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) T) :
    finiteCoupledStateProjection
        (finiteCoupledDeletedCoordinateProjection i path) =
      finiteCoupledStateProjection path := by
  funext t
  rfl

@[simp] theorem Fin_tail_finiteCoupledInsertDeletedCoordinate
    {alpha : Type*} {m T : Nat}
    (i : Fin m)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) (T + 1))
    (coord : FiniteTrajectory Bool (T + 1)) :
    Fin.tail (finiteCoupledInsertDeletedCoordinate i path coord) =
      finiteCoupledInsertDeletedCoordinate i (Fin.tail path) (Fin.tail coord) := by
  funext t
  rfl

/-- Regard the missing coordinate as the label of a one-step law whose state consists
of the real state together with the deleted-coordinate vector. -/
noncomputable def deletedCoordinateBoolCoupledStepWeight
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (current next : alpha × InactiveCoordinateLabelVector i)
    (b : Bool) : Real :=
  multiLevelBernoulliCoupledStepWeight
    P V hbound p current.1 next.1 (Function.update next.2.val i b)

/-- Pair transition matrix obtained after summing out coordinate `i`.  Stochasticity is
not needed for the algebraic finite-path marginal theorem. -/
noncomputable def inactiveCoordinatePairTransitionMatrix
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m) :
    TransitionMatrix (alpha × InactiveCoordinateLabelVector i) :=
  fun current next =>
    inactiveCoordinateMarginalStepWeight
      P V hbound p i current.1 next.1 next.2

/-- By definition, summing the missing Boolean label in the re-associated one-step law
is exactly the deleted-coordinate pair transition. -/
theorem deletedCoordinateBoolCoupledStepWeight_state_marginal
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (current next : alpha × InactiveCoordinateLabelVector i) :
    (∑ b : Bool,
      deletedCoordinateBoolCoupledStepWeight
        P V hbound p i current next b) =
      inactiveCoordinatePairTransitionMatrix
        P V hbound p i current next := by
  rfl

/-- The re-associated finite labelled weight is exactly the original full adaptive
coupled finite weight after inserting the missing coordinate trajectory. -/
theorem finiteDeletedCoordinateBoolCoupledWeight_eq_fullCoupledWeight
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m) :
    forall T (x : alpha) (base0 : InactiveCoordinateLabelVector i)
      (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)
      (coord : FiniteTrajectory Bool T),
      finiteLabeledTrajectoryWeight
          (deletedCoordinateBoolCoupledStepWeight P V hbound p i)
          T (x, base0) (zipFiniteTrajectories path coord) =
        finiteMultiLevelBernoulliCoupledWeight
          P V hbound p T x (finiteCoupledInsertDeletedCoordinate i path coord) := by
  intro T
  induction T with
  | zero =>
      intro x base0 path coord
      rfl
  | succ T ih =>
      intro x base0 path coord
      have htail :
          finiteLabeledTrajectoryWeight
              (deletedCoordinateBoolCoupledStepWeight P V hbound p i)
              T (path 0)
                (zipFiniteTrajectories (Fin.tail path) (Fin.tail coord)) =
            finiteLabeledTrajectoryWeight
              (multiLevelBernoulliCoupledStepWeight P V hbound p)
              T (path 0).1
                (finiteCoupledInsertDeletedCoordinate
                  i (Fin.tail path) (Fin.tail coord)) := by
        simpa only [finiteMultiLevelBernoulliCoupledWeight] using
          (ih (path 0).1 (path 0).2 (Fin.tail path) (Fin.tail coord))
      unfold finiteMultiLevelBernoulliCoupledWeight
      simp only [finiteLabeledTrajectoryWeight]
      rw [Fin_tail_zipFiniteTrajectories]
      rw [Fin_tail_finiteCoupledInsertDeletedCoordinate]
      change
        deletedCoordinateBoolCoupledStepWeight P V hbound p i
            (x, base0) (path 0) (coord 0) *
          finiteLabeledTrajectoryWeight
            (deletedCoordinateBoolCoupledStepWeight P V hbound p i)
            T (path 0)
              (zipFiniteTrajectories (Fin.tail path) (Fin.tail coord)) =
        multiLevelBernoulliCoupledStepWeight P V hbound p
            x (path 0).1 (Function.update (path 0).2.val i (coord 0)) *
          finiteLabeledTrajectoryWeight
            (multiLevelBernoulliCoupledStepWeight P V hbound p)
            T (path 0).1
              (finiteCoupledInsertDeletedCoordinate
                i (Fin.tail path) (Fin.tail coord))
      rw [htail]
      rfl

/-- The ordinary finite trajectory weight of the deleted-coordinate pair matrix is the
same recursive object as `finiteInactiveCoordinateMarginalWeight`. -/
theorem finiteTrajectoryWeight_inactiveCoordinatePair_eq_marginalWeight
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m) :
    forall T (x : alpha) (base0 : InactiveCoordinateLabelVector i)
      (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T),
      finiteTrajectoryWeight
          (inactiveCoordinatePairTransitionMatrix P V hbound p i)
          T (x, base0) path =
        finiteInactiveCoordinateMarginalWeight
          P V hbound p i T x path := by
  intro T
  induction T with
  | zero =>
      intro x base0 path
      rfl
  | succ T ih =>
      intro x base0 path
      unfold finiteInactiveCoordinateMarginalWeight
      simp only [finiteTrajectoryWeight, finiteLabeledTrajectoryWeight]
      rw [ih (path 0).1 (path 0).2 (Fin.tail path)]
      rfl

/-- Complete finite-path marginalization of coordinate `i`: the sum of all full coupled
weights in one deleted-coordinate fiber is the recursive deleted-coordinate marginal
weight. -/
theorem sum_finiteMultiLevelBernoulliCoupledWeight_deletedCoordinateFiber
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x : alpha)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T) :
    (∑ coord : FiniteTrajectory Bool T,
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x
          (finiteCoupledInsertDeletedCoordinate i path coord)) =
      finiteInactiveCoordinateMarginalWeight
        P V hbound p i T x path := by
  calc
    (∑ coord : FiniteTrajectory Bool T,
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x
          (finiteCoupledInsertDeletedCoordinate i path coord)) =
        ∑ coord : FiniteTrajectory Bool T,
          finiteLabeledTrajectoryWeight
            (deletedCoordinateBoolCoupledStepWeight P V hbound p i)
            T (x, inactiveCoordinateFalseVector i)
              (zipFiniteTrajectories path coord) := by
      apply Finset.sum_congr rfl
      intro coord _hcoord
      exact (finiteDeletedCoordinateBoolCoupledWeight_eq_fullCoupledWeight
        P V hbound p i T x (inactiveCoordinateFalseVector i) path coord).symm
    _ = finiteTrajectoryWeight
          (inactiveCoordinatePairTransitionMatrix P V hbound p i)
          T (x, inactiveCoordinateFalseVector i) path := by
      exact finiteLabeledTrajectoryWeight_state_marginal
        (deletedCoordinateBoolCoupledStepWeight P V hbound p i)
        (inactiveCoordinatePairTransitionMatrix P V hbound p i)
        (deletedCoordinateBoolCoupledStepWeight_state_marginal
          P V hbound p i) T
        (x, inactiveCoordinateFalseVector i) path
    _ = finiteInactiveCoordinateMarginalWeight
          P V hbound p i T x path :=
      finiteTrajectoryWeight_inactiveCoordinatePair_eq_marginalWeight
        P V hbound p i T x (inactiveCoordinateFalseVector i) path

/-- Deleted-coordinate finite prefixes whose state component first visits exact level
`i+1` at the terminal time. -/
def finiteDeletedCoordinateTerminalFirstEntrySet
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T) :=
  {path | finiteTrajectoryFirstVisitsExactLevelAt
    V x (finiteCoupledStateProjection path) i T}

/-- The full finite restriction/terminal-entry event is exactly the preimage of its
corresponding deleted-coordinate event. -/
theorem finiteCoupledDeletedCoordinateRestriction_inter_terminalFirstEntrySet
    {alpha : Type*} {m T : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    finiteCoupledDeletedCoordinateRestrictionSet i C ∩
        finiteCoupledTerminalFirstEntrySet (T := T) V x i =
      finiteCoupledDeletedCoordinateProjection i ⁻¹'
        (C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i) := by
  ext path
  rfl

/-- On a terminal first-entry deleted prefix, the full fiber sum is exactly the
pre-entry coordinate-deleted complement prefix weight. -/
theorem sum_finiteMultiLevelBernoulliCoupledWeight_deletedCoordinateFiber_terminalFirstEntry
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x : alpha)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt
      V x (finiteCoupledStateProjection path) i T) :
    (∑ coord : FiniteTrajectory Bool T,
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x
          (finiteCoupledInsertDeletedCoordinate i path coord)) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x (finiteCoupledStateProjection path))
          (finiteInactiveCoordinateFullLabelStream
            (finiteCoupledLabelProjection path)) T := by
  rw [sum_finiteMultiLevelBernoulliCoupledWeight_deletedCoordinateFiber
    P V hbound p i x path]
  let states := finiteCoupledStateProjection path
  let labels := finiteCoupledLabelProjection path
  have hpath : zipFiniteTrajectories states labels = path :=
    zipFiniteTrajectories_finiteCoupledProjections path
  calc
    finiteInactiveCoordinateMarginalWeight P V hbound p i T x path =
        finiteInactiveCoordinateMarginalWeight P V hbound p i T x
          (zipFiniteTrajectories states labels) := by
            rw [hpath]
    _ = preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x (finiteTrajectoryAbsoluteState x states)
            (finiteInactiveCoordinateFullLabelStream labels) T :=
      finiteInactiveCoordinateMarginalWeight_eq_complementPrefix_of_terminalFirstEntry
        P V hbound p i x states labels hfirst
    _ = preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x
            (finiteTrajectoryAbsoluteState x (finiteCoupledStateProjection path))
            (finiteInactiveCoordinateFullLabelStream
              (finiteCoupledLabelProjection path)) T := by
      rfl

/-- Real coordinate-deleted mass of a fixed-time first-entry slice subject to a finite
outer deleted-coordinate restriction. -/
noncomputable def restrictedTerminalFirstEntryComplementMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) : Real := by
  classical
  exact ∑ path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T,
    if path ∈ C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x
          (finiteTrajectoryAbsoluteState x (finiteCoupledStateProjection path))
          (finiteInactiveCoordinateFullLabelStream
            (finiteCoupledLabelProjection path)) T
    else 0

/-- Real full-label mass of the same finite restricted terminal first-entry event.
Packaging the classical membership test in a noncomputable definition keeps arbitrary
set restrictions out of theorem-statement elaboration. -/
noncomputable def restrictedFullTerminalFirstEntryMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) : Real := by
  classical
  exact ∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) T,
    if finiteCoupledDeletedCoordinateProjection i path ∈
        C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
      finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
    else 0

/-- Re-indexing full finite coupled prefixes by the deleted path and missing Boolean
trajectory identifies the restricted terminal first-entry real weight with the concrete
restricted complement mass. -/
theorem restrictedFullTerminalFirstEntryMass_eq_complementMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    restrictedFullTerminalFirstEntryMass P V hbound p x i C =
      restrictedTerminalFirstEntryComplementMass
        P V hbound p x i C := by
  classical
  unfold restrictedFullTerminalFirstEntryMass
  let e := finiteCoupledDeletedCoordinateBoolEquiv
    (alpha := alpha) (T := T) i
  calc
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) T,
      if finiteCoupledDeletedCoordinateProjection i path ∈
          C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
        finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
      else 0) =
        ∑ z :
            FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T ×
              FiniteTrajectory Bool T,
          if z.1 ∈ C ∩
              finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
              (finiteCoupledInsertDeletedCoordinate i z.1 z.2)
          else 0 := by
      refine Fintype.sum_equiv e
        (fun path : FiniteTrajectory (alpha × (Fin m -> Bool)) T =>
          if finiteCoupledDeletedCoordinateProjection i path ∈
              C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
          else 0)
        (fun z :
            FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T ×
              FiniteTrajectory Bool T =>
          if z.1 ∈ C ∩
              finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
              (finiteCoupledInsertDeletedCoordinate i z.1 z.2)
          else 0) ?_
      intro path
      change
        (if finiteCoupledDeletedCoordinateProjection i path ∈
            C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
          finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
        else 0) =
          (if finiteCoupledDeletedCoordinateProjection i path ∈
              C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
              (finiteCoupledInsertDeletedCoordinate i
                (finiteCoupledDeletedCoordinateProjection i path)
                (finiteCoupledCoordinateProjection i path))
          else 0)
      rw [finiteCoupledInsertDeletedCoordinate_projections]
    _ = ∑ path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T,
          ∑ coord : FiniteTrajectory Bool T,
            if path ∈ C ∩
                finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
                (finiteCoupledInsertDeletedCoordinate i path coord)
            else 0 := by
      simpa using
        (Fintype.sum_prod_type
          (fun z :
              FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T ×
                FiniteTrajectory Bool T =>
            if z.1 ∈ C ∩
                finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p T x
                (finiteCoupledInsertDeletedCoordinate i z.1 z.2)
            else 0))
    _ = ∑ path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T,
          if path ∈ C ∩
              finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteInactiveCoordinateMarginalWeight P V hbound p i T x path
          else 0 := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hmem : path ∈ C ∩
          finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
      · simp only [if_pos hmem]
        exact sum_finiteMultiLevelBernoulliCoupledWeight_deletedCoordinateFiber
          P V hbound p i x path
      · simp [hmem]
    _ = restrictedTerminalFirstEntryComplementMass
          P V hbound p x i C := by
      unfold restrictedTerminalFirstEntryComplementMass
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hmem : path ∈ C ∩
          finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
      · simp only [if_pos hmem]
        have hfirst : finiteTrajectoryFirstVisitsExactLevelAt
            V x (finiteCoupledStateProjection path) i T := hmem.2
        simpa using
          (finiteInactiveCoordinateMarginalWeight_eq_complementPrefix_of_terminalFirstEntry
            P V hbound p i x
              (finiteCoupledStateProjection path)
              (finiteCoupledLabelProjection path) hfirst)
      · simp [hmem]

/-- The restricted finite complement mass is nonnegative under the hypotheses that make
the adaptive coupled finite weights nonnegative. -/
theorem restrictedTerminalFirstEntryComplementMass_nonneg
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    0 <= restrictedTerminalFirstEntryComplementMass
      P V hbound p x i C := by
  classical
  rw [← restrictedFullTerminalFirstEntryMass_eq_complementMass
    P V hbound p x i C]
  unfold restrictedFullTerminalFirstEntryMass
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hmem : finiteCoupledDeletedCoordinateProjection i path ∈
      C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
  · simp only [if_pos hmem]
    exact finiteMultiLevelBernoulliCoupledWeight_nonneg
      P hP V hbound p hp hp1 hexit T x path
  · simp only [if_neg hmem, le_refl]

/-- Finite measure version of the fixed-time deleted-coordinate calculation. -/
theorem finiteMultiLevelBernoulliCoupledMeasure_deletedRestriction_terminalFirstEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit T x
        (finiteCoupledDeletedCoordinateRestrictionSet i C ∩
          finiteCoupledTerminalFirstEntrySet (T := T) V x i) =
      ENNReal.ofReal
        (restrictedTerminalFirstEntryComplementMass
          P V hbound p x i C) := by
  classical
  rw [finiteCoupledDeletedCoordinateRestriction_inter_terminalFirstEntrySet
    V x i C]
  let E : Set (FiniteTrajectory (alpha × (Fin m -> Bool)) T) :=
    finiteCoupledDeletedCoordinateProjection i ⁻¹'
      (C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i)
  have hE : MeasurableSet E := E.to_countable.measurableSet
  change finiteMultiLevelBernoulliCoupledMeasure
      P hP V hbound p hp hp1 hexit T x E = _
  rw [← MeasureTheory.lintegral_indicator_fun_one hE]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteMultiLevelBernoulliCoupledMeasure_singleton
    P hP V hbound p hp hp1 hexit T x]
  have hnonneg :
      ∀ path ∈
        (Finset.univ : Finset (FiniteTrajectory (alpha × (Fin m -> Bool)) T)),
        0 <=
          (if finiteCoupledDeletedCoordinateProjection i path ∈
              C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
          else 0) := by
    intro path _hpath
    by_cases hmem : finiteCoupledDeletedCoordinateProjection i path ∈
        C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
    · simp only [if_pos hmem]
      exact finiteMultiLevelBernoulliCoupledWeight_nonneg
        P hP V hbound p hp hp1 hexit T x path
    · simp only [if_neg hmem, le_refl]
  calc
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) T,
      E.indicator (fun _ => (1 : ENNReal)) path *
        ENNReal.ofReal
          (finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path)) =
        ∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) T,
          ENNReal.ofReal
            (if finiteCoupledDeletedCoordinateProjection i path ∈
                C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
            else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hmem : finiteCoupledDeletedCoordinateProjection i path ∈
          C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
      · have hmemE : path ∈ E := by
          change finiteCoupledDeletedCoordinateProjection i path ∈
            C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
          exact hmem
        rw [Set.indicator_of_mem hmemE (fun _ => (1 : ENNReal))]
        simp only [if_pos hmem, one_mul]
      · have hnotmemE : path ∉ E := by
          change finiteCoupledDeletedCoordinateProjection i path ∉
            C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i
          exact hmem
        rw [Set.indicator_of_notMem hnotmemE (fun _ => (1 : ENNReal))]
        simp [hmem]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) T,
          if finiteCoupledDeletedCoordinateProjection i path ∈
              C ∩ finiteDeletedCoordinateTerminalFirstEntrySet (T := T) V x i then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p T x path
          else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal
        (restrictedTerminalFirstEntryComplementMass
          P V hbound p x i C) := by
      have hmass := restrictedFullTerminalFirstEntryMass_eq_complementMass
        P V hbound p x i C
      unfold restrictedFullTerminalFirstEntryMass at hmass
      rw [hmass]

/-- The genuine infinite adaptive coupled law has the same restricted exact-time mass:
the finite complement sum is therefore no longer merely an algebraic surrogate. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_eq_ofReal
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i C ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T) =
      ENNReal.ofReal
        (restrictedTerminalFirstEntryComplementMass
          P V hbound p x i C) := by
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry
    P hP V hbound p hp hp1 hexit x i T C]
  exact finiteMultiLevelBernoulliCoupledMeasure_deletedRestriction_terminalFirstEntry
    P hP V hbound p hp hp1 hexit x i C

/-- Real-mass form of the preceding exact-time identity. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_toReal
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i C ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T)).toReal =
      restrictedTerminalFirstEntryComplementMass
        P V hbound p x i C := by
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_eq_ofReal
    P hP V hbound p hp hp1 hexit x i C]
  exact ENNReal.toReal_ofReal
    (restrictedTerminalFirstEntryComplementMass_nonneg
      P hP V hbound p hp hp1 hexit x i C)

end ECRuntime
