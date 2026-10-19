import ECRuntime.ExactLevelGeometricBranchAssembly
import ECRuntime.MultiLevelCoupledTrajectory
import ECRuntime.TransitionKernel
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 47: infinite adaptive coupled trajectory law

The finite adaptive state/vector-label law has been available since fixes 26--27, and
fixes 30--46 extract the exact-level support, random-entry freshness, bounded and
infinite first-entry masses, and the normalized entry/skip geometric branch bookkeeping.
The remaining coupling argument, however, needs one genuine probability measure under
which the pathwise adaptive support and residence statements hold almost everywhere.

This file supplies that missing measure-theoretic object without changing the finite
coupling.  We regard a post-transition state together with the Boolean comparison vector
emitted on that transition as one pair state.  The transition row from `(x, oldBits)` to
`(y, bits)` is exactly

`multiLevelBernoulliCoupledStepWeight P V hbound p x y bits`.

The previous Boolean vector is deliberately ignored.  Under stochasticity, positive
comparison parameters, upper probability bounds, and the uniform exact-level exit
bounds, this pair transition matrix is stochastic.  Its ordinary finite trajectory
weight is definitionally the already verified finite labelled adaptive weight, so the
standard Ionescu--Tulcea construction gives a canonical infinite extension whose every
finite post-initial marginal is exactly the existing finite coupled law.

No geometric coordinate is extracted here.  The next slice can work on this genuine
coupled probability space, prove positive adaptive step support almost everywhere, and
map each comparison coordinate stream from its actual first-entry time to the canonical
geometric waiting coordinate, using fix 46 to fill the permanent-skip branch.
-/

/-- Product Bernoulli vector weights are nonnegative when every coordinate parameter lies
in `[0,1]`. -/
theorem bernoulliLevelVectorWeight_nonneg
    {m : Nat} (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1)
    (bits : Fin m -> Bool) :
    0 <= bernoulliLevelVectorWeight p bits := by
  unfold bernoulliLevelVectorWeight
  apply Finset.prod_nonneg
  intro i _hi
  exact bernoulliBoolWeight_nonneg (hp0 i) (hp1 i) (bits i)

/-- The complement product obtained by deleting one Boolean coordinate is nonnegative
under the same coordinatewise probability bounds. -/
theorem bernoulliLevelVectorComplementWeight_nonneg
    {m : Nat} (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1)
    (i : Fin m) (bits : Fin m -> Bool) :
    0 <= bernoulliLevelVectorComplementWeight p i bits := by
  unfold bernoulliLevelVectorComplementWeight
  apply Finset.prod_nonneg
  intro j _hj
  exact bernoulliBoolWeight_nonneg (hp0 j) (hp1 j) (bits j)

/-- The active-coordinate Bernoulli-vector split is nonnegative. -/
theorem levelBernoulliVectorCoupledStepWeight_nonneg
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (level : Set alpha)
    (hP : IsStochastic P)
    (p : Fin m -> Real) (i : Fin m)
    (hp : forall j, 0 < p j) (hp1 : forall j, p j <= 1)
    (hexit : forall z, z ∈ level ->
      p i <= finiteEventMass (P z) (fun y => y ∉ level))
    (x y : alpha) (bits : Fin m -> Bool) :
    0 <= levelBernoulliVectorCoupledStepWeight P level p i x y bits := by
  rw [levelBernoulliVectorCoupledStepWeight_eq_active_mul_complement]
  apply mul_nonneg
  · exact levelBernoulliCoupledStepWeight_nonneg
      P level hP (p i) (hp i) (hp1 i) hexit x y (bits i)
  · exact bernoulliLevelVectorComplementWeight_nonneg
      p (fun j => le_of_lt (hp j)) hp1 i bits

/-- Every global adaptive one-step state/vector-label weight is nonnegative. -/
theorem multiLevelBernoulliCoupledStepWeight_nonneg
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x y : alpha) (bits : Fin m -> Bool) :
    0 <= multiLevelBernoulliCoupledStepWeight P V hbound p x y bits := by
  classical
  by_cases hx : V x = 0
  · rw [show multiLevelBernoulliCoupledStepWeight P V hbound p x y bits =
        P x y * bernoulliLevelVectorWeight p bits by
        simp [multiLevelBernoulliCoupledStepWeight, hx]]
    exact mul_nonneg (hP.1 x y)
      (bernoulliLevelVectorWeight_nonneg
        p (fun j => le_of_lt (hp j)) hp1 bits)
  · let i : Fin m := activePositivePotentialLevelIndex V hbound x hx
    have hexit_i : forall z, z ∈ exactPositivePotentialLevel V i ->
        p i <= finiteEventMass (P z)
          (fun u => u ∉ exactPositivePotentialLevel V i) := by
      intro z hz
      exact hexit i z hz
    rw [show multiLevelBernoulliCoupledStepWeight P V hbound p x y bits =
        levelBernoulliVectorCoupledStepWeight
          P (exactPositivePotentialLevel V i) p i x y bits by
        simp [multiLevelBernoulliCoupledStepWeight, hx, i]]
    exact levelBernoulliVectorCoupledStepWeight_nonneg
      P (exactPositivePotentialLevel V i) hP p i hp hp1 hexit_i x y bits

/-- Markov transition matrix on pair states `(state, emitted Boolean vector)`.
The previous Boolean vector is irrelevant; the new vector labels the current transition. -/
noncomputable def adaptiveMultiLevelCoupledTransitionMatrix
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) :
    TransitionMatrix (alpha × (Fin m -> Bool)) :=
  fun current next =>
    multiLevelBernoulliCoupledStepWeight
      P V hbound p current.1 next.1 next.2

/-- The pair-state transition matrix is stochastic under the standard Stage-26 exit
assumptions. -/
theorem adaptiveMultiLevelCoupledTransitionMatrix_stochastic
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p) :
    IsStochastic
      (adaptiveMultiLevelCoupledTransitionMatrix P V hbound p) := by
  classical
  constructor
  · intro current next
    unfold adaptiveMultiLevelCoupledTransitionMatrix
    exact multiLevelBernoulliCoupledStepWeight_nonneg
      P hP V hbound p hp hp1 hexit current.1 next.1 next.2
  · intro current
    unfold adaptiveMultiLevelCoupledTransitionMatrix
    calc
      (∑ next : alpha × (Fin m -> Bool),
          multiLevelBernoulliCoupledStepWeight
            P V hbound p current.1 next.1 next.2) =
          ∑ y : alpha, ∑ bits : Fin m -> Bool,
            multiLevelBernoulliCoupledStepWeight
              P V hbound p current.1 y bits := by
        simpa using
          (Fintype.sum_prod_type
            (fun next : alpha × (Fin m -> Bool) =>
              multiLevelBernoulliCoupledStepWeight
                P V hbound p current.1 next.1 next.2))
      _ = ∑ y : alpha, P current.1 y := by
        apply Finset.sum_congr rfl
        intro y _hy
        exact multiLevelBernoulliCoupledStepWeight_state_marginal
          P V hbound p current.1 y
      _ = 1 := hP.2 current.1

/-- A harmless deterministic comparison-vector value used only in the time-zero pair
state.  Actual transition labels begin at path coordinate one. -/
def adaptiveCoupledInitialBits {m : Nat} : Fin m -> Bool :=
  fun _ => false

/-- Canonical time-zero pair state for the infinite adaptive coupled chain. -/
def adaptiveCoupledInitialState
    {alpha : Type*} {m : Nat} (x : alpha) : alpha × (Fin m -> Bool) :=
  (x, adaptiveCoupledInitialBits)

/-- The previously defined finite adaptive coupled path weights are nonnegative. -/
theorem finiteMultiLevelBernoulliCoupledWeight_nonneg
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) t) :
    0 <= finiteMultiLevelBernoulliCoupledWeight
      P V hbound p t x path := by
  unfold finiteMultiLevelBernoulliCoupledWeight
  exact finiteLabeledTrajectoryWeight_nonneg
    (multiLevelBernoulliCoupledStepWeight P V hbound p)
    (multiLevelBernoulliCoupledStepWeight_nonneg
      P hP V hbound p hp hp1 hexit)
    t x path

/-- The finite adaptive coupled weights have total mass one. -/
theorem finiteMultiLevelBernoulliCoupledWeight_sum
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (t : Nat) (x : alpha) :
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x path) = 1 := by
  unfold finiteMultiLevelBernoulliCoupledWeight
  exact finiteLabeledTrajectoryWeight_sum_of_state_marginal
    (multiLevelBernoulliCoupledStepWeight P V hbound p) P hP
    (multiLevelBernoulliCoupledStepWeight_state_marginal P V hbound p)
    t x

/-- The finite adaptive state/vector-label law packaged as an honest PMF. -/
noncomputable def finiteMultiLevelBernoulliCoupledPMF
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    PMF (FiniteTrajectory (alpha × (Fin m -> Bool)) t) :=
  PMF.ofFintype
    (fun path => ENNReal.ofReal
      (finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x path))
    (by
      have hnonneg :
          ∀ path ∈
            (Finset.univ :
              Finset (FiniteTrajectory (alpha × (Fin m -> Bool)) t)),
            0 <= finiteMultiLevelBernoulliCoupledWeight
              P V hbound p t x path := by
        intro path _hpath
        exact finiteMultiLevelBernoulliCoupledWeight_nonneg
          P hP V hbound p hp hp1 hexit t x path
      calc
        (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
          ENNReal.ofReal
            (finiteMultiLevelBernoulliCoupledWeight
              P V hbound p t x path)) =
            ENNReal.ofReal
              (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
                finiteMultiLevelBernoulliCoupledWeight
                  P V hbound p t x path) := by
          symm
          exact ENNReal.ofReal_sum_of_nonneg hnonneg
        _ = 1 := by
          rw [finiteMultiLevelBernoulliCoupledWeight_sum
            P hP V hbound p t x]
          simp)

/-- Measure associated with the finite adaptive coupled PMF. -/
noncomputable def finiteMultiLevelBernoulliCoupledMeasure
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    Measure (FiniteTrajectory (alpha × (Fin m -> Bool)) t) :=
  (finiteMultiLevelBernoulliCoupledPMF
    P hP V hbound p hp hp1 hexit t x).toMeasure

instance instIsProbabilityMeasureFiniteMultiLevelBernoulliCoupledMeasure
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    IsProbabilityMeasure
      (finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x) := by
  unfold finiteMultiLevelBernoulliCoupledMeasure
  infer_instance

/-- Point masses of the finite adaptive coupled measure are exactly the verified real
coupled path weights embedded in `ENNReal`. -/
@[simp] theorem finiteMultiLevelBernoulliCoupledMeasure_singleton
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) t) :
    finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x {path} =
      ENNReal.ofReal
        (finiteMultiLevelBernoulliCoupledWeight
          P V hbound p t x path) := by
  unfold finiteMultiLevelBernoulliCoupledMeasure
  rw [PMF.toMeasure_apply_singleton _ path (measurableSet_singleton path)]
  rfl

/-- Generic bridge: the ordinary finite path weight of the pair transition matrix equals
the labelled path weight obtained by reading the first component as the state and the
new second component as the emitted transition label. -/
theorem finiteTrajectoryWeight_adaptivePair_eq_finiteLabeled
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) :
    forall t (current : alpha × (Fin m -> Bool))
      (path : FiniteTrajectory (alpha × (Fin m -> Bool)) t),
      finiteTrajectoryWeight
          (adaptiveMultiLevelCoupledTransitionMatrix P V hbound p)
          t current path =
        finiteLabeledTrajectoryWeight
          (multiLevelBernoulliCoupledStepWeight P V hbound p)
          t current.1 path := by
  intro t
  induction t with
  | zero =>
      intro current path
      rfl
  | succ t ih =>
      intro current path
      simp only [finiteTrajectoryWeight, finiteLabeledTrajectoryWeight]
      rw [ih (path 0) (Fin.tail path)]
      rfl

/-- Specialization of the pair-weight bridge to the existing finite adaptive coupled
weight. -/
theorem finiteTrajectoryWeight_adaptivePair_eq_multiLevelCoupled
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (t : Nat) (x : alpha)
    (path : FiniteTrajectory (alpha × (Fin m -> Bool)) t) :
    finiteTrajectoryWeight
        (adaptiveMultiLevelCoupledTransitionMatrix P V hbound p)
        t (adaptiveCoupledInitialState x) path =
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x path := by
  unfold finiteMultiLevelBernoulliCoupledWeight
  exact finiteTrajectoryWeight_adaptivePair_eq_finiteLabeled
    P V hbound p t (adaptiveCoupledInitialState x) path

/-- The standard finite trajectory measure of the pair transition matrix is exactly the
finite adaptive coupled measure already determined by the state/vector-label weights. -/
theorem finiteTrajectoryMeasure_adaptivePair_eq_coupledMeasure
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    finiteTrajectoryMeasure
        (adaptiveMultiLevelCoupledTransitionMatrix P V hbound p)
        (adaptiveMultiLevelCoupledTransitionMatrix_stochastic
          P hP V hbound p hp hp1 hexit)
        t (adaptiveCoupledInitialState x) =
      finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x := by
  apply Measure.ext_iff_singleton.mpr
  intro path
  rw [finiteTrajectoryMeasure_singleton]
  rw [finiteMultiLevelBernoulliCoupledMeasure_singleton]
  rw [finiteTrajectoryWeight_adaptivePair_eq_multiLevelCoupled
    P V hbound p t x path]

/-- Canonical infinite adaptive coupled law obtained from the stochastic pair transition
matrix by the already verified Ionescu--Tulcea construction. -/
noncomputable def adaptiveMultiLevelCoupledTrajectoryMeasure
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) :
    Measure (Nat -> (alpha × (Fin m -> Bool))) :=
  transitionTrajectoryMeasure
    (adaptiveMultiLevelCoupledTransitionMatrix P V hbound p)
    (adaptiveMultiLevelCoupledTransitionMatrix_stochastic
      P hP V hbound p hp hp1 hexit)
    (adaptiveCoupledInitialState x)

instance instIsProbabilityMeasureAdaptiveMultiLevelCoupledTrajectoryMeasure
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) :
    IsProbabilityMeasure
      (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x) := by
  unfold adaptiveMultiLevelCoupledTrajectoryMeasure
  infer_instance

/-- Every finite post-initial marginal of the infinite adaptive coupled law is exactly the
finite coupled measure from the existing Stage-26 state/vector-label construction. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_map_tail_eq_finiteCoupledMeasure
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (t : Nat) :
    (adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x).map
      (transitionTrajectoryTail t) =
      finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x := by
  unfold adaptiveMultiLevelCoupledTrajectoryMeasure
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure
    (adaptiveMultiLevelCoupledTransitionMatrix P V hbound p)
    (adaptiveMultiLevelCoupledTransitionMatrix_stochastic
      P hP V hbound p hp hp1 hexit)
    (adaptiveCoupledInitialState x) t]
  exact finiteTrajectoryMeasure_adaptivePair_eq_coupledMeasure
    P hP V hbound p hp hp1 hexit t x

/-- State-path projection from the coupled pair trajectory. -/
def adaptiveCoupledStatePath
    {alpha : Type*} {m : Nat}
    (path : Nat -> (alpha × (Fin m -> Bool))) : Nat -> alpha :=
  fun t => (path t).1

/-- Comparison-vector stream emitted by the coupled transitions.  Transition `t -> t+1`
is labelled by the second component stored at path coordinate `t+1`. -/
def adaptiveCoupledLabelStream
    {alpha : Type*} {m : Nat}
    (path : Nat -> (alpha × (Fin m -> Bool))) : Nat -> (Fin m -> Bool) :=
  fun t => (path (t + 1)).2

@[fun_prop] theorem measurable_adaptiveCoupledStatePath
    {alpha : Type*} [MeasurableSpace alpha] {m : Nat} :
    Measurable (adaptiveCoupledStatePath
      (alpha := alpha) (m := m)) := by
  unfold adaptiveCoupledStatePath
  fun_prop

@[fun_prop] theorem measurable_adaptiveCoupledLabelStream
    {alpha : Type*} [MeasurableSpace alpha] {m : Nat} :
    Measurable (adaptiveCoupledLabelStream
      (alpha := alpha) (m := m)) := by
  unfold adaptiveCoupledLabelStream
  fun_prop

end ECRuntime
