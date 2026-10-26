import ECRuntime.BoundedFirstEntryProjectiveMass
import ECRuntime.FiniteMarginalIdentification
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-!
# Stage 26 fix 45: eventual exact-level entry and permanent skipping

Stage 26 fix 44 fix 1 compiler-verifies the complete bounded finite mass-identification
layer.  In particular, for every horizon `T`, the sum of the coordinate-deleted terminal
first-entry masses through time `T` is exactly both the bounded state entry mass and the
bounded adaptive coupled entry mass.

The project already has a genuine infinite trajectory law: Stage 17 constructs the
Ionescu--Tulcea measure and Stage 22 proves that every finite post-initial tail marginal is
exactly the explicit finite-trajectory measure.  Hence the next bridge can be made directly
at the measure level instead of introducing a separate abstract limit.

This file defines the infinite-path event that exact level `i+1` is first visited at time
`s`, proves that these events are measurable and pairwise disjoint, and identifies the
probability of the time-`s` event with `ENNReal.ofReal` of the compiler-verified
`terminalFirstEntryComplementMass` from fix 43.  Their countable union is the genuine
eventual-entry event.  Its complement is the permanent-skip event, giving the normalized
entry/skip partition needed before geometric continuation is attached to the entry branch.
-/

/-- Infinite-path predicate saying that exact level `i+1` is first visited at absolute
trajectory time `s`. -/
def transitionTrajectoryFirstVisitsExactLevelAt
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (s : Nat) (path : Nat -> alpha) : Prop :=
  V (transitionTrajectoryState x path s) = i.val + 1 ∧
    ∀ r, r < s -> V (transitionTrajectoryState x path r) ≠ i.val + 1

/-- Infinite-path set of trajectories whose first visit to exact level `i+1` occurs at
absolute time `s`. -/
def transitionTrajectoryFirstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (s : Nat) : Set (Nat -> alpha) :=
  {path | transitionTrajectoryFirstVisitsExactLevelAt V x i s path}

/-- The finite absolute-state view of the first `T` post-initial states agrees with the
infinite absolute-state view at every time `r <= T`. -/
theorem finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
    {alpha : Type*}
    (x : alpha) (path : Nat -> alpha) (T r : Nat) (hr : r <= T) :
    finiteTrajectoryAbsoluteState x (transitionTrajectoryTail T path) r =
      transitionTrajectoryState x path r := by
  cases r with
  | zero =>
      rfl
  | succ t =>
      have ht : t < T := by omega
      rw [finiteTrajectoryAbsoluteState_succ_of_lt x
        (transitionTrajectoryTail T path) t ht]
      rfl

/-- The infinite first-entry-at-`T` predicate is exactly the terminal finite first-entry
predicate applied to the first `T` post-initial states. -/
theorem transitionTrajectoryFirstVisitsExactLevelAt_iff_finiteTerminal
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m)
    (T : Nat) (path : Nat -> alpha) :
    transitionTrajectoryFirstVisitsExactLevelAt V x i T path <->
      finiteTrajectoryFirstVisitsExactLevelAt
        V x (transitionTrajectoryTail T path) i T := by
  constructor
  · intro hfirst
    refine ⟨le_rfl, ?_, ?_⟩
    · rw [finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
        x path T T le_rfl]
      exact hfirst.1
    · intro r hr
      have hrT : r <= T := by omega
      rw [finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
        x path T r hrT]
      exact hfirst.2 r hr
  · intro hfirst
    refine ⟨?_, ?_⟩
    · rw [← finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
        x path T T le_rfl]
      exact hfirst.2.1
    · intro r hr
      have hrT : r <= T := by omega
      rw [← finiteTrajectoryAbsoluteState_transitionTrajectoryTail_of_le
        x path T r hrT]
      exact hfirst.2.2 r hr

/-- The exact-time infinite first-entry set is the inverse image of the corresponding
terminal first-entry subset of the finite trajectory space. -/
theorem transitionTrajectoryFirstExactLevelEntrySet_eq_preimage
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    transitionTrajectoryFirstExactLevelEntrySet V x i T =
      transitionTrajectoryTail T ⁻¹'
        {states : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x states i T} := by
  ext path
  simp only [transitionTrajectoryFirstExactLevelEntrySet, Set.mem_setOf_eq,
    Set.mem_preimage]
  exact transitionTrajectoryFirstVisitsExactLevelAt_iff_finiteTerminal
    V x i T path

/-- Every exact-time first-entry event is measurable on the infinite trajectory space. -/
theorem measurableSet_transitionTrajectoryFirstExactLevelEntrySet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    MeasurableSet (transitionTrajectoryFirstExactLevelEntrySet V x i T) := by
  rw [transitionTrajectoryFirstExactLevelEntrySet_eq_preimage V x i T]
  have hset :
      MeasurableSet
        {states : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :=
    ({states : FiniteTrajectory alpha T |
      finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :
        Set (FiniteTrajectory alpha T)).to_countable.measurableSet
  have htail :
      Measurable
        (transitionTrajectoryTail T :
          (Nat -> alpha) -> FiniteTrajectory alpha T) :=
    measurable_transitionTrajectoryTail T
  exact hset.preimage htail

/-- Distinct exact first-entry times define disjoint infinite-path events. -/
theorem pairwise_disjoint_transitionTrajectoryFirstExactLevelEntrySet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    Pairwise (Function.onFun Disjoint
      (transitionTrajectoryFirstExactLevelEntrySet V x i)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro path hs ht
  change transitionTrajectoryFirstVisitsExactLevelAt V x i s path at hs
  change transitionTrajectoryFirstVisitsExactLevelAt V x i t path at ht
  by_cases hlt : s < t
  · exact (ht.2 s hlt) hs.1
  · have hts : t < s := by omega
    exact (hs.2 t hts) ht.1

/-- The terminal first-entry subset has finite-trajectory probability equal to the
`ENNReal.ofReal` embedding of the corresponding state first-entry slice mass. -/
theorem finiteTrajectoryMeasure_terminalFirstEntrySet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) (T : Nat) :
    finiteTrajectoryMeasure P hP T x
        {states : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x states i T} =
      ENNReal.ofReal
        (boundedExactLevelFirstEntrySliceMass P V x i (Fin.last T)) := by
  classical
  have hEvent :
      MeasurableSet
        {states : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :=
    ({states : FiniteTrajectory alpha T |
      finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :
        Set (FiniteTrajectory alpha T)).to_countable.measurableSet
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP T x]
  have hnonneg :
      ∀ states ∈ (Finset.univ : Finset (FiniteTrajectory alpha T)),
        0 <=
          (if finiteTrajectoryFirstVisitsExactLevelAt V x states i T
           then finiteTrajectoryWeight P T x states else 0) := by
    intro states _hstates
    by_cases hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i T
    · simpa [hfirst] using finiteTrajectoryWeight_nonneg P hP T x states
    · simp [hfirst]
  calc
    (∑ states : FiniteTrajectory alpha T,
        {q : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x q i T}.indicator
            (fun _ => (1 : ENNReal)) states *
          ENNReal.ofReal (finiteTrajectoryWeight P T x states)) =
        ∑ states : FiniteTrajectory alpha T,
          ENNReal.ofReal
            (if finiteTrajectoryFirstVisitsExactLevelAt V x states i T
             then finiteTrajectoryWeight P T x states else 0) := by
      apply Finset.sum_congr rfl
      intro states _hstates
      by_cases hfirst : finiteTrajectoryFirstVisitsExactLevelAt V x states i T
      · simp [hfirst]
      · simp [hfirst]
    _ = ENNReal.ofReal
        (∑ states : FiniteTrajectory alpha T,
          if finiteTrajectoryFirstVisitsExactLevelAt V x states i T
          then finiteTrajectoryWeight P T x states else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal
        (boundedExactLevelFirstEntrySliceMass P V x i (Fin.last T)) := by
      rfl

/-- Under the genuine infinite trajectory law, the probability that exact level `i+1`
is first visited at time `T` is exactly the terminal coordinate-deleted mass from fix 43. -/
theorem transitionTrajectoryMeasure_firstExactLevelEntryAt
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) (T : Nat) :
    transitionTrajectoryMeasure P hP x
        (transitionTrajectoryFirstExactLevelEntrySet V x i T) =
      ENNReal.ofReal
        (terminalFirstEntryComplementMass P V hbound p x i T) := by
  rw [transitionTrajectoryFirstExactLevelEntrySet_eq_preimage V x i T]
  have htail :
      Measurable
        (transitionTrajectoryTail T :
          (Nat -> alpha) -> FiniteTrajectory alpha T) :=
    measurable_transitionTrajectoryTail T
  have hset :
      MeasurableSet
        {states : FiniteTrajectory alpha T |
          finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :=
    ({states : FiniteTrajectory alpha T |
      finiteTrajectoryFirstVisitsExactLevelAt V x states i T} :
        Set (FiniteTrajectory alpha T)).to_countable.measurableSet
  rw [← Measure.map_apply htail hset]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x T]
  rw [finiteTrajectoryMeasure_terminalFirstEntrySet P hP V x i T]
  rw [terminalFirstEntryComplementMass_eq_stateSliceMass
    P V hbound p x i T]

/-- Genuine infinite-path event that exact level `i+1` is eventually visited.  The union
is disjoint because every visiting trajectory has a unique first-entry time. -/
def transitionTrajectoryEventuallyVisitsExactLevelSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) : Set (Nat -> alpha) :=
  ⋃ T : Nat, transitionTrajectoryFirstExactLevelEntrySet V x i T

/-- The eventual exact-level entry event is measurable. -/
theorem measurableSet_transitionTrajectoryEventuallyVisitsExactLevelSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    MeasurableSet (transitionTrajectoryEventuallyVisitsExactLevelSet V x i) := by
  unfold transitionTrajectoryEventuallyVisitsExactLevelSet
  exact MeasurableSet.iUnion fun T =>
    measurableSet_transitionTrajectoryFirstExactLevelEntrySet V x i T

/-- The probability of eventual exact-level entry is the countable sum of the verified
coordinate-deleted terminal first-entry masses. -/
theorem transitionTrajectoryMeasure_eventualExactLevelEntry
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m) :
    transitionTrajectoryMeasure P hP x
        (transitionTrajectoryEventuallyVisitsExactLevelSet V x i) =
      ∑' T : Nat,
        ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T) := by
  unfold transitionTrajectoryEventuallyVisitsExactLevelSet
  rw [measure_iUnion
    (pairwise_disjoint_transitionTrajectoryFirstExactLevelEntrySet V x i)
    (fun T => measurableSet_transitionTrajectoryFirstExactLevelEntrySet V x i T)]
  apply tsum_congr
  intro T
  exact transitionTrajectoryMeasure_firstExactLevelEntryAt
    P hP V hbound p x i T

/-- Infinite-path event of permanently skipping exact level `i+1`. -/
def transitionTrajectoryPermanentlySkipsExactLevelSet
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) : Set (Nat -> alpha) :=
  (transitionTrajectoryEventuallyVisitsExactLevelSet V x i)ᶜ

/-- The permanent-skip event is measurable. -/
theorem measurableSet_transitionTrajectoryPermanentlySkipsExactLevelSet
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    MeasurableSet (transitionTrajectoryPermanentlySkipsExactLevelSet V x i) := by
  exact (measurableSet_transitionTrajectoryEventuallyVisitsExactLevelSet V x i).compl

/-- Eventual entry and permanent skipping form a normalized partition under the genuine
infinite trajectory probability measure. -/
theorem transitionTrajectoryMeasure_eventualEntry_add_permanentSkip
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (x : alpha) (i : Fin m) :
    transitionTrajectoryMeasure P hP x
        (transitionTrajectoryEventuallyVisitsExactLevelSet V x i) +
      transitionTrajectoryMeasure P hP x
        (transitionTrajectoryPermanentlySkipsExactLevelSet V x i) = 1 := by
  have hmeas :=
    measurableSet_transitionTrajectoryEventuallyVisitsExactLevelSet V x i
  unfold transitionTrajectoryPermanentlySkipsExactLevelSet
  rw [measure_compl hmeas (measure_ne_top _ _)]
  have huniv : transitionTrajectoryMeasure P hP x Set.univ = 1 := by simp
  rw [huniv]
  apply add_tsub_cancel_of_le
  calc
    transitionTrajectoryMeasure P hP x
        (transitionTrajectoryEventuallyVisitsExactLevelSet V x i) <=
        transitionTrajectoryMeasure P hP x Set.univ :=
      measure_mono (Set.subset_univ _)
    _ = 1 := by simp

end ECRuntime
