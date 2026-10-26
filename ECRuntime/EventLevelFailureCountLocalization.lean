import ECRuntime.CountableRestrictedEntryGeometricPeeling
import ECRuntime.OneLevelGeometricCouplingInterface
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 62: event-level failure-count localization and monotone support

Stage 26 fix 61 fix 1 is compiler verified warning-free.  It proves the countable
one-coordinate scalar peeling identity: after combining genuine eventual entry and
permanent skipping, prescribing failure count `r` contributes the geometric singleton
factor `(1 - p i)^r * p i`.

The remaining coupling construction needs two pathwise interfaces before those scalar
masses can be iterated into an actual failure-vector coupling.

First, the visited branch must be represented by a genuine measurable path event rather
than only by a weighted scalar.  This module therefore defines the finite cylinder in
which exact level `i+1` is first entered at time `T`, coordinate `i` then fails for the
first `r` comparisons, and succeeds at comparison `r`.  Pulling this finite cylinder
back to the infinite adaptive pair path gives a measurable exact-time event; taking the
countable union over `T` gives the measurable visited failure-count event.  Membership
is proved equivalent to the visited branch of
`AdaptiveCoupledExactLevelGeometricFailureSupport`.

Second, the final support relation requires potential nonincrease.  The exit-bound
hypothesis alone does not imply monotonicity, so the required transition-support
assumption is made explicit: every positive-probability transition of `P` must weakly
decrease `V`.  Positive adaptive coupled-step support then implies positive underlying
state-transition probability, hence pathwise potential nonincrease.  Fix 48 fix 2
already proves positive adaptive support almost surely, so monotonicity follows almost
surely under this explicit transition-support assumption.

The last lemmas record the finite-prefix localization consequence needed for descending
coordinate peeling: once a nonincreasing trajectory has reached a lower exact level,
every strictly higher exact level has either already been visited or is permanently
skipped.

This stage deliberately does not yet identify the measure of the new visited event with
the scalar mass from fix 61.  That is the next finite-cylinder calculation: extend the
fix-58 deleted-coordinate fiber argument through the `r` failures and terminal success.
-/

/-- A state-transition support condition sufficient for potential monotonicity: every
transition with strictly positive probability weakly decreases the natural potential. -/
def HasPotentialNonincreasingTransitionSupport
    {alpha : Type*}
    (P : TransitionMatrix alpha) (V : alpha -> Nat) : Prop :=
  forall x y : alpha, 0 < P x y -> V y <= V x

/-- A positive adaptive coupled one-step weight forces the corresponding underlying
state transition to have positive `P`-mass. -/
theorem transitionMatrix_pos_of_multiLevelBernoulliCoupledStepWeight_pos
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x y : alpha) (bits : Fin m -> Bool)
    (hpos : 0 < multiLevelBernoulliCoupledStepWeight
      P V hbound p x y bits) :
    0 < P x y := by
  classical
  have hle :
      multiLevelBernoulliCoupledStepWeight P V hbound p x y bits <=
        ∑ b : Fin m -> Bool,
          multiLevelBernoulliCoupledStepWeight P V hbound p x y b := by
    exact Finset.single_le_sum
      (fun b _hb =>
        multiLevelBernoulliCoupledStepWeight_nonneg
          P hP V hbound p hp hp1 hexit x y b)
      (Finset.mem_univ bits)
  rw [multiLevelBernoulliCoupledStepWeight_state_marginal
    P V hbound p x y] at hle
  exact lt_of_lt_of_le hpos hle

/-- Positive adaptive coupled-step support plus monotone transition support gives
potential nonincrease along the supplied state path. -/
theorem isPotentialNonincreasingAlong_of_positiveAdaptiveCoupledStepSupport
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x path labels) :
    IsPotentialNonincreasingAlong V x path := by
  intro t
  apply hmonoP
  exact transitionMatrix_pos_of_multiLevelBernoulliCoupledStepWeight_pos
    P hP V hbound p hp hp1 hexit
      (transitionTrajectoryState x path t)
      (transitionTrajectoryState x path (t + 1))
      (labels t) (hsupport t)

/-- Under monotone transition support, the genuine infinite adaptive coupled trajectory
has nonincreasing potential almost surely. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_ae_potentialNonincreasing
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : alpha) :
    ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path) := by
  filter_upwards
    [adaptiveMultiLevelCoupledTrajectoryMeasure_ae_positiveAdaptiveSupport
      P hP V hbound p hp hp1 hexit x] with path hsupport
  exact isPotentialNonincreasingAlong_of_positiveAdaptiveCoupledStepSupport
    P hP V hbound p hp hp1 hexit hmonoP x
      (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path) hsupport

/-- The genuine adaptive law simultaneously has potential nonincrease and positive
adaptive coupled-step support almost surely.  These are the first two conjuncts of the
final `AdaptiveCoupledGeometricFailureCouplingSupport` relation. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_ae_monotone_positiveSupport
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : alpha) :
    ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path) /\
        HasPositiveAdaptiveCoupledStepSupport
          P V hbound p x (adaptiveCoupledStatePath path)
            (adaptiveCoupledLabelStream path) := by
  filter_upwards
    [adaptiveMultiLevelCoupledTrajectoryMeasure_ae_potentialNonincreasing
      P hP V hbound p hp hp1 hexit hmonoP x,
     adaptiveMultiLevelCoupledTrajectoryMeasure_ae_positiveAdaptiveSupport
      P hP V hbound p hp hp1 hexit x] with path hmono hsupport
  exact ⟨hmono, hsupport⟩

/-- Finite coupled prefixes witnessing first entry into exact level `i+1` at time `T`,
followed by exactly `r` failures of comparison coordinate `i` and then one success.
The prefix has length `T + r + 1`, so its last constrained label is the transition at
absolute time `T+r`. -/
def finiteCoupledFirstEntryGeometricFailurePatternSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat) :
    Set (FiniteTrajectory (alpha × (Fin m -> Bool)) (T + r + 1)) :=
  {pathPrefix |
    finiteTrajectoryFirstVisitsExactLevelAt
        V x (finiteCoupledStateProjection pathPrefix) i T /\
      (forall k : Fin r,
        (pathPrefix ⟨T + k.val, by omega⟩).2 i = false) /\
      (pathPrefix ⟨T + r, by omega⟩).2 i = true}

/-- Exact-time visited failure-count event on the genuine infinite adaptive pair-path
space, obtained by pulling back the finite cylinder above. -/
def adaptiveCoupledFirstEntryGeometricFailurePatternSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  transitionTrajectoryTail (T + r + 1) ⁻¹'
    finiteCoupledFirstEntryGeometricFailurePatternSet V x i T r

/-- Every exact-time visited failure-count cylinder is measurable. -/
theorem measurableSet_adaptiveCoupledFirstEntryGeometricFailurePatternSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat) :
    MeasurableSet
      (adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r) := by
  unfold adaptiveCoupledFirstEntryGeometricFailurePatternSet
  exact
    (finiteCoupledFirstEntryGeometricFailurePatternSet V x i T r).to_countable.measurableSet.preimage
      (measurable_transitionTrajectoryTail
        (α := alpha × (Fin m -> Bool)) (T + r + 1))

/-- Countable visited branch for failure count `r`, with the first-entry time existentially
quantified by a measurable union. -/
def adaptiveCoupledVisitedExactLevelGeometricFailureSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (r : Nat) :
    Set (Nat -> (alpha × (Fin m -> Bool))) :=
  ⋃ T : Nat, adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r

/-- The visited failure-count event is measurable. -/
theorem measurableSet_adaptiveCoupledVisitedExactLevelGeometricFailureSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (r : Nat) :
    MeasurableSet
      (adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r) := by
  unfold adaptiveCoupledVisitedExactLevelGeometricFailureSet
  exact MeasurableSet.iUnion
    (fun T => measurableSet_adaptiveCoupledFirstEntryGeometricFailurePatternSet
      V x i T r)

/-- A finite exact-time failure-pattern cylinder yields the corresponding infinite
first-entry predicate on the projected state path. -/
theorem transitionTrajectoryFirstVisitsExactLevelAt_of_mem_firstEntryFailurePattern
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmem : path ∈ adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r) :
    transitionTrajectoryFirstVisitsExactLevelAt
      V x i T (adaptiveCoupledStatePath path) := by
  change transitionTrajectoryTail (T + r + 1) path ∈
    finiteCoupledFirstEntryGeometricFailurePatternSet V x i T r at hmem
  change finiteTrajectoryFirstVisitsExactLevelAt V x
      (transitionTrajectoryTail (T + r + 1) (adaptiveCoupledStatePath path)) i T /\
    (forall k : Fin r, adaptiveCoupledLabelStream path (T + k.val) i = false) /\
    adaptiveCoupledLabelStream path (T + r) i = true at hmem
  have hfirst := hmem.1
  have hTle : T <= T + r + 1 := by omega
  constructor
  · rw [← finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
      x (adaptiveCoupledStatePath path) (T + r + 1) T hTle]
    exact hfirst.2.1
  · intro s hs
    have hsle : s <= T + r + 1 := by omega
    rw [← finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
      x (adaptiveCoupledStatePath path) (T + r + 1) s hsle]
    exact hfirst.2.2 s hs

/-- Every exact-time failure-pattern cylinder is contained in the corresponding
exact-first-entry-time event. -/
theorem adaptiveCoupledFirstEntryGeometricFailurePatternSet_subset_firstEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat) :
    adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r ⊆
      adaptiveCoupledFirstExactLevelEntrySet V x i T := by
  intro path hmem
  change transitionTrajectoryFirstVisitsExactLevelAt
    V x i T (adaptiveCoupledStatePath path)
  exact transitionTrajectoryFirstVisitsExactLevelAt_of_mem_firstEntryFailurePattern
    V x i T r path hmem

/-- Distinct exact-entry-time failure-pattern cylinders are disjoint. -/
theorem pairwise_disjoint_adaptiveCoupledFirstEntryGeometricFailurePatternSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (r : Nat) :
    Pairwise (Function.onFun Disjoint
      (fun T => adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro path hs ht
  have hs' := adaptiveCoupledFirstEntryGeometricFailurePatternSet_subset_firstEntrySet
    V x i s r hs
  have ht' := adaptiveCoupledFirstEntryGeometricFailurePatternSet_subset_firstEntrySet
    V x i t r ht
  exact (Set.disjoint_left.mp
    (pairwise_disjoint_adaptiveCoupledFirstExactLevelEntrySet V x i hst)) hs' ht'

/-- The genuine visited failure-count mass is the disjoint countable sum of its exact
first-entry-time cylinders. -/
theorem adaptiveCoupledVisitedExactLevelGeometricFailureSet_measure_eq_tsum
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m) (r : Nat) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r) =
      ∑' T : Nat,
        adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r) := by
  unfold adaptiveCoupledVisitedExactLevelGeometricFailureSet
  exact measure_iUnion
    (pairwise_disjoint_adaptiveCoupledFirstEntryGeometricFailurePatternSet
      V x i r)
    (fun T => measurableSet_adaptiveCoupledFirstEntryGeometricFailurePatternSet
      V x i T r)

/-- The same exact-time decomposition remains valid after intersecting with an arbitrary
measurable outer restriction. -/
theorem adaptiveCoupled_restricted_visitedFailure_measure_eq_tsum
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m) (r : Nat)
    (A : Set (Nat -> (alpha × (Fin m -> Bool))))
    (hA : MeasurableSet A) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (A ∩ adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r) =
      ∑' T : Nat,
        adaptiveMultiLevelCoupledTrajectoryMeasure
          P hP V hbound p hp hp1 hexit x
          (A ∩ adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r) := by
  have hset :
      A ∩ adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r =
        ⋃ T : Nat,
          A ∩ adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r := by
    unfold adaptiveCoupledVisitedExactLevelGeometricFailureSet
    ext path
    simp
  rw [hset]
  apply measure_iUnion
  · intro s t hst
    apply Set.disjoint_left.mpr
    intro path hs ht
    exact (Set.disjoint_left.mp
      (pairwise_disjoint_adaptiveCoupledFirstEntryGeometricFailurePatternSet
        V x i r hst)) hs.2 ht.2
  · intro T
    exact hA.inter
      (measurableSet_adaptiveCoupledFirstEntryGeometricFailurePatternSet
        V x i T r)

/-- On an exact-time failure cylinder, all first `r` coordinate comparisons after entry
are false. -/
theorem adaptiveCoupledLabelStream_eq_false_of_mem_firstEntryFailurePattern
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmem : path ∈ adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r)
    (k : Nat) (hk : k < r) :
    adaptiveCoupledLabelStream path (T + k) i = false := by
  change transitionTrajectoryTail (T + r + 1) path ∈
    finiteCoupledFirstEntryGeometricFailurePatternSet V x i T r at hmem
  change finiteTrajectoryFirstVisitsExactLevelAt V x
      (transitionTrajectoryTail (T + r + 1) (adaptiveCoupledStatePath path)) i T /\
    (forall q : Fin r, adaptiveCoupledLabelStream path (T + q.val) i = false) /\
    adaptiveCoupledLabelStream path (T + r) i = true at hmem
  exact hmem.2.1 ⟨k, hk⟩

/-- On an exact-time failure cylinder, comparison `r` after entry is true. -/
theorem adaptiveCoupledLabelStream_eq_true_of_mem_firstEntryFailurePattern
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmem : path ∈ adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r) :
    adaptiveCoupledLabelStream path (T + r) i = true := by
  change transitionTrajectoryTail (T + r + 1) path ∈
    finiteCoupledFirstEntryGeometricFailurePatternSet V x i T r at hmem
  change finiteTrajectoryFirstVisitsExactLevelAt V x
      (transitionTrajectoryTail (T + r + 1) (adaptiveCoupledStatePath path)) i T /\
    (forall q : Fin r, adaptiveCoupledLabelStream path (T + q.val) i = false) /\
    adaptiveCoupledLabelStream path (T + r) i = true at hmem
  exact hmem.2.2

/-- Membership in one exact-time cylinder realizes the visited branch of the one-level
geometric failure support with failure count `r`. -/
theorem adaptiveCoupledExactLevelGeometricFailureSupport_of_mem_firstEntryFailurePattern
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmem : path ∈ adaptiveCoupledFirstEntryGeometricFailurePatternSet V x i T r) :
    AdaptiveCoupledExactLevelGeometricFailureSupport V x path i r := by
  let states := adaptiveCoupledStatePath path
  let labels := adaptiveCoupledLabelStream path
  have hfirst : transitionTrajectoryFirstVisitsExactLevelAt V x i T states :=
    transitionTrajectoryFirstVisitsExactLevelAt_of_mem_firstEntryFailurePattern
      V x i T r path hmem
  have hvisit : ∃ t : Nat,
      V (transitionTrajectoryState x states t) = i.val + 1 :=
    ⟨T, hfirst.1⟩
  have hentry_le : firstExactLevelEntryTime V x states i hvisit <= T := by
    exact Nat.find_min' hvisit hfirst.1
  have hT_le : T <= firstExactLevelEntryTime V x states i hvisit := by
    by_contra hnot
    have hlt : firstExactLevelEntryTime V x states i hvisit < T := by omega
    exact hfirst.2 _ hlt
      (firstExactLevelEntryTime_spec V x states i hvisit)
  have hentry : firstExactLevelEntryTime V x states i hvisit = T := by
    omega
  have hsucc : ∃ k : Nat,
      labels (firstExactLevelEntryTime V x states i hvisit + k) i = true := by
    refine ⟨r, ?_⟩
    rw [hentry]
    exact adaptiveCoupledLabelStream_eq_true_of_mem_firstEntryFailurePattern
      V x i T r path hmem
  have hsuccess_le :
      firstComparisonSuccessOffsetAfterEntry
          V x states labels i hvisit hsucc <= r := by
    apply Nat.find_min' hsucc
    rw [hentry]
    exact adaptiveCoupledLabelStream_eq_true_of_mem_firstEntryFailurePattern
      V x i T r path hmem
  have hr_le : r <= firstComparisonSuccessOffsetAfterEntry
      V x states labels i hvisit hsucc := by
    by_contra hnot
    have hlt : firstComparisonSuccessOffsetAfterEntry
        V x states labels i hvisit hsucc < r := by omega
    have hspec :
        labels
          (T + firstComparisonSuccessOffsetAfterEntry
            V x states labels i hvisit hsucc) i = true := by
      simpa [hentry] using
        (firstComparisonSuccessOffsetAfterEntry_spec
          V x states labels i hvisit hsucc)
    have hfalse :
        labels
          (T + firstComparisonSuccessOffsetAfterEntry
            V x states labels i hvisit hsucc) i = false := by
      simpa [states, labels] using
        (adaptiveCoupledLabelStream_eq_false_of_mem_firstEntryFailurePattern
          V x i T r path hmem
            (firstComparisonSuccessOffsetAfterEntry
              V x states labels i hvisit hsucc) hlt)
    rw [hfalse] at hspec
    cases hspec
  left
  refine ⟨hvisit, hsucc, ?_⟩
  exact Nat.le_antisymm hsuccess_le hr_le

/-- Every path in the countable visited failure-count event belongs to the corresponding
one-level support slice. -/
theorem adaptiveCoupledExactLevelGeometricFailureSupport_of_mem_visitedFailureSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hmem : path ∈ adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r) :
    AdaptiveCoupledExactLevelGeometricFailureSupport V x path i r := by
  rw [adaptiveCoupledVisitedExactLevelGeometricFailureSet] at hmem
  rcases Set.mem_iUnion.mp hmem with ⟨T, hT⟩
  exact adaptiveCoupledExactLevelGeometricFailureSupport_of_mem_firstEntryFailurePattern
    V x i T r path hT

/-- Conversely, the visited branch of the one-level support relation belongs to the
measurable visited failure-count event. -/
theorem mem_adaptiveCoupledVisitedExactLevelGeometricFailureSet_of_visitSupport
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hvisit : ∃ t : Nat,
      V (transitionTrajectoryState x (adaptiveCoupledStatePath path) t) = i.val + 1)
    (hsucc : ∃ k : Nat,
      adaptiveCoupledLabelStream path
        (firstExactLevelEntryTime V x (adaptiveCoupledStatePath path) i hvisit + k) i = true)
    (hoffset : firstComparisonSuccessOffsetAfterEntry
        V x (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path)
          i hvisit hsucc = r) :
    path ∈ adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r := by
  let T := firstExactLevelEntryTime V x (adaptiveCoupledStatePath path) i hvisit
  have hfirst : transitionTrajectoryFirstVisitsExactLevelAt
      V x i T (adaptiveCoupledStatePath path) := by
    constructor
    · exact firstExactLevelEntryTime_spec
        V x (adaptiveCoupledStatePath path) i hvisit
    · intro s hs
      exact firstExactLevelEntryTime_minimal
        V x (adaptiveCoupledStatePath path) i hvisit hs
  have hfalse : forall k : Nat, k < r ->
      adaptiveCoupledLabelStream path (T + k) i = false := by
    intro k hk
    have hk' : k < firstComparisonSuccessOffsetAfterEntry
        V x (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path)
          i hvisit hsucc := by
      rw [hoffset]
      exact hk
    exact firstComparisonSuccessOffsetAfterEntry_eq_false_of_lt
      V x (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path)
        i hvisit hsucc hk'
  have htrue : adaptiveCoupledLabelStream path (T + r) i = true := by
    have hspec := firstComparisonSuccessOffsetAfterEntry_spec
      V x (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path)
        i hvisit hsucc
    rw [hoffset] at hspec
    exact hspec
  rw [adaptiveCoupledVisitedExactLevelGeometricFailureSet]
  apply Set.mem_iUnion.mpr
  refine ⟨T, ?_⟩
  change transitionTrajectoryTail (T + r + 1) path ∈
    finiteCoupledFirstEntryGeometricFailurePatternSet V x i T r
  change finiteTrajectoryFirstVisitsExactLevelAt V x
      (transitionTrajectoryTail (T + r + 1) (adaptiveCoupledStatePath path)) i T /\
    (forall k : Fin r, adaptiveCoupledLabelStream path (T + k.val) i = false) /\
    adaptiveCoupledLabelStream path (T + r) i = true
  constructor
  ·
    have hTle : T <= T + r + 1 := by omega
    refine ⟨hTle, ?_, ?_⟩
    · rw [finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
        x (adaptiveCoupledStatePath path) (T + r + 1) T hTle]
      exact hfirst.1
    · intro s hs
      have hsle : s <= T + r + 1 := by omega
      rw [finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
        x (adaptiveCoupledStatePath path) (T + r + 1) s hsle]
      exact hfirst.2 s hs
  · constructor
    · intro k
      exact hfalse k.val k.isLt
    · exact htrue

/-- The measurable visited event is exactly the visited disjunct of the one-level
geometric failure support. -/
theorem mem_adaptiveCoupledVisitedExactLevelGeometricFailureSet_iff
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (r : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool))) :
    path ∈ adaptiveCoupledVisitedExactLevelGeometricFailureSet V x i r <->
      ∃ hvisit : (∃ t : Nat,
          V (transitionTrajectoryState x (adaptiveCoupledStatePath path) t) = i.val + 1),
        ∃ hsucc : (∃ k : Nat,
          adaptiveCoupledLabelStream path
            (firstExactLevelEntryTime
              V x (adaptiveCoupledStatePath path) i hvisit + k) i = true),
          firstComparisonSuccessOffsetAfterEntry
            V x (adaptiveCoupledStatePath path) (adaptiveCoupledLabelStream path)
              i hvisit hsucc = r := by
  constructor
  · intro hmem
    have hsupport :=
      adaptiveCoupledExactLevelGeometricFailureSupport_of_mem_visitedFailureSet
        V x i r path hmem
    exact hsupport.resolve_right (by
      intro hskip
      rw [adaptiveCoupledVisitedExactLevelGeometricFailureSet] at hmem
      rcases Set.mem_iUnion.mp hmem with ⟨T, hT⟩
      have hfirst :=
        transitionTrajectoryFirstVisitsExactLevelAt_of_mem_firstEntryFailurePattern
          V x i T r path hT
      exact hskip T hfirst.1)
  · rintro ⟨hvisit, hsucc, hoffset⟩
    exact mem_adaptiveCoupledVisitedExactLevelGeometricFailureSet_of_visitSupport
      V x i r path hvisit hsucc hoffset

/-- Along a nonincreasing trajectory, visiting a strictly higher exact level cannot
occur at or after a time at which a lower exact level has already been reached. -/
theorem higherExactLevelVisitTime_lt_of_nonincreasing
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i j : Fin m) (hij : i.val < j.val)
    (T t : Nat)
    (hT : V (transitionTrajectoryState x path T) = i.val + 1)
    (ht : V (transitionTrajectoryState x path t) = j.val + 1) :
    t < T := by
  by_contra hnot
  have hTt : T <= t := by omega
  have hle := potential_le_of_nonincreasingAlong V x path hmono hTt
  omega

/-- Consequently, by the time a nonincreasing trajectory reaches a lower exact level,
every strictly higher exact level is already resolved: it was visited earlier, or it is
permanently skipped. -/
theorem higherExactLevel_visitedBefore_or_permanentlySkipped_of_nonincreasing
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i j : Fin m) (hij : i.val < j.val)
    (T : Nat)
    (hT : V (transitionTrajectoryState x path T) = i.val + 1) :
    (∃ t : Nat, t < T /\
        V (transitionTrajectoryState x path t) = j.val + 1) \/
      (forall t : Nat,
        V (transitionTrajectoryState x path t) ≠ j.val + 1) := by
  classical
  by_cases hvisit : ∃ t : Nat,
      V (transitionTrajectoryState x path t) = j.val + 1
  · rcases hvisit with ⟨t, ht⟩
    left
    exact ⟨t,
      higherExactLevelVisitTime_lt_of_nonincreasing
        V x path hmono i j hij T t hT ht,
      ht⟩
  · right
    exact fun t ht => hvisit ⟨t, ht⟩

end ECRuntime
