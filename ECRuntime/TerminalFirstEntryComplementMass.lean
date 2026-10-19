import ECRuntime.FiniteCoupledPrefixRepresentation
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 43: terminal first-entry complement mass

Stage 26 fix 42 fix 2 is compiler verified warning-free.  The recursive finite
multi-level coupled weight is therefore now identified exactly with the explicit
prefix-product representation used by the pre-entry freshness machinery.

The next issue is bookkeeping rather than stopping-time freshness.  The complement
obtained by deleting coordinate `i` is insensitive to that coordinate, so summing it
over *all* full Boolean vectors would count each deleted-coordinate history twice at
every transition.  This file introduces one canonical representative of every vector
with coordinate `i` removed: a full vector whose `i`-th bit is fixed to `false`.
Together with the separately restored Boolean bit this representative is equivalent to
the original full vector space.

We use that equivalence to define a globally normalized one-step row in which coordinate
`i` has been marginalized.  Before the first visit of exact level `i+1`, the resulting
one-step factor is exactly the verified inactive-coordinate complement.  Consequently,
on a finite state prefix whose first entry occurs at its terminal time, summing the
coordinate-deleted prefix weights over all remaining label histories gives exactly the
ordinary state-prefix weight.  Summing over all such state prefixes identifies the
coordinate-deleted first-entry mass with the concrete fix-40 state and coupled terminal
first-entry slice masses.

A later stage will use projective consistency to identify an arbitrary fix-40 slice at
time `s <= T` with this terminal-prefix mass at horizon `s`, and then sum over `s`.
-/

/-- Canonical representatives for Boolean label vectors with coordinate `i` removed.
The omitted coordinate is fixed to `false`; its actual Boolean value is carried
separately when reconstructing a full vector. -/
abbrev InactiveCoordinateLabelVector {m : Nat} (i : Fin m) :=
  {bits : Fin m -> Bool // bits i = false}

/-- Canonical representative of a full Boolean vector after deleting coordinate `i`. -/
def inactiveCoordinateRepresentative {m : Nat} (i : Fin m)
    (bits : Fin m -> Bool) : InactiveCoordinateLabelVector i :=
  ⟨Function.update bits i false, by simp⟩

/-- A deleted-coordinate representative together with the missing Boolean bit is exactly
one full Boolean vector. -/
def inactiveCoordinateLabelVectorBoolEquiv {m : Nat} (i : Fin m) :
    InactiveCoordinateLabelVector i × Bool ≃ (Fin m -> Bool) where
  toFun z := Function.update z.1.val i z.2
  invFun bits := (inactiveCoordinateRepresentative i bits, bits i)
  left_inv z := by
    rcases z with ⟨base, b⟩
    apply Prod.ext
    · apply Subtype.ext
      funext j
      by_cases hji : j = i
      · subst j
        simp [inactiveCoordinateRepresentative, base.property]
      · simp [inactiveCoordinateRepresentative, hji]
    · simp
  right_inv bits := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [inactiveCoordinateRepresentative]
    · simp [inactiveCoordinateRepresentative, hji]

/-- Re-index a sum over full Boolean vectors by a deleted-coordinate representative and
its missing bit. -/
theorem sum_inactiveCoordinateLabelVector_sum_bool
    {m : Nat} (i : Fin m) (F : (Fin m -> Bool) -> Real) :
    (∑ base : InactiveCoordinateLabelVector i, ∑ b : Bool,
      F (Function.update base.val i b)) =
      ∑ bits : Fin m -> Bool, F bits := by
  classical
  let e := inactiveCoordinateLabelVectorBoolEquiv i
  calc
    (∑ base : InactiveCoordinateLabelVector i, ∑ b : Bool,
        F (Function.update base.val i b)) =
        ∑ z : InactiveCoordinateLabelVector i × Bool,
          F (Function.update z.1.val i z.2) := by
      simpa using
        (Fintype.sum_prod_type
          (fun z : InactiveCoordinateLabelVector i × Bool =>
            F (Function.update z.1.val i z.2))).symm
    _ = ∑ bits : Fin m -> Bool, F bits := by
      refine Fintype.sum_equiv e
        (fun z : InactiveCoordinateLabelVector i × Bool =>
          F (Function.update z.1.val i z.2)) F ?_
      intro z
      rfl

/-- One-step adaptive coupled weight after coordinate `i` has been marginalized.
This definition is valid at every current state, including states where `i` is active. -/
noncomputable def inactiveCoordinateMarginalStepWeight
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x y : alpha) (base : InactiveCoordinateLabelVector i) : Real :=
  ∑ b : Bool,
    multiLevelBernoulliCoupledStepWeight
      P V hbound p x y (Function.update base.val i b)

/-- Marginalizing the missing coordinate and then summing all remaining label vectors
recovers the original transition row. -/
theorem inactiveCoordinateMarginalStepWeight_state_marginal
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x y : alpha) :
    (∑ base : InactiveCoordinateLabelVector i,
      inactiveCoordinateMarginalStepWeight P V hbound p i x y base) =
      P x y := by
  classical
  unfold inactiveCoordinateMarginalStepWeight
  calc
    (∑ base : InactiveCoordinateLabelVector i, ∑ b : Bool,
        multiLevelBernoulliCoupledStepWeight
          P V hbound p x y (Function.update base.val i b)) =
        ∑ bits : Fin m -> Bool,
          multiLevelBernoulliCoupledStepWeight P V hbound p x y bits := by
      exact sum_inactiveCoordinateLabelVector_sum_bool i
        (fun bits => multiLevelBernoulliCoupledStepWeight P V hbound p x y bits)
    _ = P x y :=
      multiLevelBernoulliCoupledStepWeight_state_marginal P V hbound p x y

/-- At a state where coordinate `i` is inactive, the globally marginalized one-step
factor is exactly the coordinate-deleted complement from fix 32. -/
theorem inactiveCoordinateMarginalStepWeight_eq_complement_of_inactive
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x y : alpha) (base : InactiveCoordinateLabelVector i)
    (hi : V x ≠ i.val + 1) :
    inactiveCoordinateMarginalStepWeight P V hbound p i x y base =
      multiLevelBernoulliInactiveCoordinateComplementWeight
        P V hbound p i x y base.val := by
  unfold inactiveCoordinateMarginalStepWeight
  exact sum_multiLevelBernoulliCoupledStepWeight_update_inactiveCoordinate
    P V hbound p i x y base.val hi

/-- All-false canonical deleted-coordinate vector, used only for padding a finite label
trajectory outside its horizon. -/
def inactiveCoordinateFalseVector {m : Nat} (i : Fin m) :
    InactiveCoordinateLabelVector i :=
  ⟨fun _ => false, rfl⟩

/-- Embed a finite deleted-coordinate label trajectory into a total transition-indexed
stream. -/
def finiteInactiveCoordinateLabelStream
    {m T : Nat} {i : Fin m}
    (labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T) :
    Nat -> InactiveCoordinateLabelVector i :=
  fun t => if ht : t < T then labels ⟨t, ht⟩ else inactiveCoordinateFalseVector i

@[simp] theorem finiteInactiveCoordinateLabelStream_apply_of_lt
    {m T : Nat} {i : Fin m}
    (labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T)
    (t : Nat) (ht : t < T) :
    finiteInactiveCoordinateLabelStream labels t = labels ⟨t, ht⟩ := by
  simp [finiteInactiveCoordinateLabelStream, ht]

/-- View a finite deleted-coordinate trajectory as a total stream of ordinary full
Boolean vectors using the canonical representatives. -/
def finiteInactiveCoordinateFullLabelStream
    {m T : Nat} {i : Fin m}
    (labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T) :
    Nat -> (Fin m -> Bool) :=
  fun t => (finiteInactiveCoordinateLabelStream labels t).val

/-- Reading the first `T` deleted-coordinate labels back from their padded stream
recovers the original finite label trajectory. -/
theorem transitionLabelTrajectory_finiteInactiveCoordinateLabelStream
    {m T : Nat} {i : Fin m}
    (labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T) :
    transitionLabelTrajectory T (finiteInactiveCoordinateLabelStream labels) = labels := by
  funext j
  simp [transitionLabelTrajectory,
    finiteInactiveCoordinateLabelStream, j.isLt]

/-- Finite recursively defined path weight after coordinate `i` has been marginalized. -/
noncomputable def finiteInactiveCoordinateMarginalWeight
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (T : Nat) (x : alpha)
    (path : FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T) : Real :=
  finiteLabeledTrajectoryWeight
    (inactiveCoordinateMarginalStepWeight P V hbound p i) T x path

/-- The finite deleted-coordinate coupled law has exactly the original state-path
marginal. -/
theorem finiteInactiveCoordinateMarginalWeight_state_marginal
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x : alpha) (states : FiniteTrajectory alpha T) :
    (∑ labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T,
      finiteInactiveCoordinateMarginalWeight P V hbound p i T x
        (zipFiniteTrajectories states labels)) =
      finiteTrajectoryWeight P T x states := by
  unfold finiteInactiveCoordinateMarginalWeight
  exact finiteLabeledTrajectoryWeight_state_marginal
    (inactiveCoordinateMarginalStepWeight P V hbound p i) P
    (inactiveCoordinateMarginalStepWeight_state_marginal
      P V hbound p i) T x states

/-- On a state prefix whose first visit of exact level `i+1` occurs at its terminal time,
the recursive deleted-coordinate path weight is exactly the pre-entry complement prefix
weight from fixes 33--35. -/
theorem finiteInactiveCoordinateMarginalWeight_eq_complementPrefix_of_terminalFirstEntry
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x : alpha) (states : FiniteTrajectory alpha T)
    (labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T)
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i T) :
    finiteInactiveCoordinateMarginalWeight P V hbound p i T x
        (zipFiniteTrajectories states labels) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x (finiteTrajectoryAbsoluteState x states)
          (finiteInactiveCoordinateFullLabelStream labels) T := by
  have h := finiteLabeledTrajectoryWeight_stream_eq_prefixProduct
    (inactiveCoordinateMarginalStepWeight P V hbound p i)
    T x (finiteTrajectoryAbsoluteState x states)
      (finiteInactiveCoordinateLabelStream labels)
  rw [transitionTrajectoryTail_finiteTrajectoryAbsoluteState x states] at h
  rw [transitionLabelTrajectory_finiteInactiveCoordinateLabelStream labels] at h
  unfold finiteInactiveCoordinateMarginalWeight
  rw [h]
  unfold preEntryInactiveCoordinateComplementPrefixWeight
  apply Finset.prod_congr rfl
  intro t ht
  have htT : t < T := Finset.mem_range.mp ht
  have hi :
      V (transitionTrajectoryState x
        (finiteTrajectoryAbsoluteState x states) t) ≠ i.val + 1 := by
    simpa using hfirst.2.2 t htT
  exact inactiveCoordinateMarginalStepWeight_eq_complement_of_inactive
    P V hbound p i
      (transitionTrajectoryState x (finiteTrajectoryAbsoluteState x states) t)
      (transitionTrajectoryState x (finiteTrajectoryAbsoluteState x states) (t + 1))
      (finiteInactiveCoordinateLabelStream labels t) hi

/-- After deleting coordinate `i`, summing all remaining label histories of a terminal
first-entry prefix gives exactly the ordinary state-prefix probability weight. -/
theorem sum_inactiveCoordinateComplementPrefixWeight_terminalFirstEntry
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (i : Fin m)
    (x : alpha) (states : FiniteTrajectory alpha T)
    (hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i T) :
    (∑ labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T,
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x (finiteTrajectoryAbsoluteState x states)
          (finiteInactiveCoordinateFullLabelStream labels) T) =
      finiteTrajectoryWeight P T x states := by
  calc
    (∑ labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T,
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x (finiteTrajectoryAbsoluteState x states)
          (finiteInactiveCoordinateFullLabelStream labels) T) =
        ∑ labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T,
          finiteInactiveCoordinateMarginalWeight P V hbound p i T x
            (zipFiniteTrajectories states labels) := by
      apply Finset.sum_congr rfl
      intro labels _hlabels
      exact (finiteInactiveCoordinateMarginalWeight_eq_complementPrefix_of_terminalFirstEntry
        P V hbound p i x states labels hfirst).symm
    _ = finiteTrajectoryWeight P T x states :=
      finiteInactiveCoordinateMarginalWeight_state_marginal
        P V hbound p i x states

/-- Coordinate-deleted mass of all state/remaining-label prefixes that first enter exact
level `i+1` precisely at their terminal time `T`. -/
noncomputable def terminalFirstEntryComplementMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) : Real := by
  classical
  exact Finset.univ.sum fun states : FiniteTrajectory alpha T =>
    if finiteTrajectoryFirstVisitsExactLevelAt V x states i T then
      Finset.univ.sum fun labels : FiniteTrajectory (InactiveCoordinateLabelVector i) T =>
        preEntryInactiveCoordinateComplementPrefixWeight
          P V hbound p i x (finiteTrajectoryAbsoluteState x states)
            (finiteInactiveCoordinateFullLabelStream labels) T
    else 0

/-- The coordinate-deleted terminal first-entry mass is exactly the concrete fix-40
state first-entry slice at the same horizon. -/
theorem terminalFirstEntryComplementMass_eq_stateSliceMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    terminalFirstEntryComplementMass P V hbound p x i T =
      boundedExactLevelFirstEntrySliceMass P V x i (Fin.last T) := by
  classical
  unfold terminalFirstEntryComplementMass boundedExactLevelFirstEntrySliceMass
  apply Finset.sum_congr rfl
  intro states _hstates
  have hlast : (Fin.last T).val = T := rfl
  rw [hlast]
  by_cases hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i T
  · simp only [if_pos hfirst]
    exact sum_inactiveCoordinateComplementPrefixWeight_terminalFirstEntry
      P V hbound p i x states hfirst
  · simp [hfirst]

/-- The same coordinate-deleted mass is exactly the concrete adaptive coupled fix-40
terminal first-entry slice. -/
theorem terminalFirstEntryComplementMass_eq_coupledSliceMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    terminalFirstEntryComplementMass P V hbound p x i T =
      boundedCoupledExactLevelFirstEntrySliceMass
        P V hbound p x i (Fin.last T) := by
  rw [terminalFirstEntryComplementMass_eq_stateSliceMass
    P V hbound p x i T]
  exact (boundedCoupledExactLevelFirstEntrySliceMass_eq_stateSliceMass
    P V hbound p x i (Fin.last T)).symm

end ECRuntime
