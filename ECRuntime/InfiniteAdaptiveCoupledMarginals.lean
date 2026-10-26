import ECRuntime.InfiniteAdaptiveCoupledTrajectory
import ECRuntime.HistoryDependentWaiting
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 48: finite marginals and almost-sure adaptive support

Fix 47 fix 1 supplies the normalized infinite adaptive state/vector-label law.  The
next coupling arguments need three concrete facts about that law:

* every finite state cylinder has exactly the original Markov trajectory marginal;
* every finite Boolean-vector cylinder has exactly the i.i.d. product-Bernoulli
  marginal; and
* every realized adaptive coupled transition has positive coupled weight almost
  surely.

The finite state/label claims are proved first at the already verified finite coupled
measure and are then transported through fix 47's exact infinite-to-finite tail
projection.  The support claim uses a simple discrete fact: under the finite coupled
PMF, paths of zero coupled weight have measure zero.  Almost surely every finite prefix
therefore has positive weight.  Rewriting each prefix by the verified fix-42 product
representation shows every individual transition factor is positive, which is exactly
`HasPositiveAdaptiveCoupledStepSupport` from fix 31.

No geometric waiting variable is introduced here.  The next stage can combine this
almost-sure support theorem with the finite i.i.d. label cylinders and the pathwise
residence bound.
-/

/-- First-component projection of a finite pair trajectory. -/
def finiteCoupledStateProjection
    {alpha beta : Type*} {t : Nat}
    (path : FiniteTrajectory (alpha × beta) t) : FiniteTrajectory alpha t :=
  fun j => (path j).1

/-- Second-component projection of a finite pair trajectory. -/
def finiteCoupledLabelProjection
    {alpha beta : Type*} {t : Nat}
    (path : FiniteTrajectory (alpha × beta) t) : FiniteTrajectory beta t :=
  fun j => (path j).2

@[simp] theorem zipFiniteTrajectories_finiteCoupledProjections
    {alpha beta : Type*} {t : Nat}
    (path : FiniteTrajectory (alpha × beta) t) :
    zipFiniteTrajectories
        (finiteCoupledStateProjection path)
        (finiteCoupledLabelProjection path) = path := by
  funext j
  apply Prod.ext <;> rfl

/-- Coordinatewise splitting is an equivalence between pair trajectories and pairs of
state/label trajectories. -/
def finiteTrajectoryProdEquiv
    {alpha beta : Type*} {t : Nat} :
    FiniteTrajectory (alpha × beta) t ≃
      FiniteTrajectory alpha t × FiniteTrajectory beta t where
  toFun path :=
    (finiteCoupledStateProjection path, finiteCoupledLabelProjection path)
  invFun z := zipFiniteTrajectories z.1 z.2
  left_inv path := zipFiniteTrajectories_finiteCoupledProjections path
  right_inv z := by
    rcases z with ⟨states, labels⟩
    apply Prod.ext
    · rfl
    · rfl

/-- Summing finite adaptive coupled weights over the fiber of a fixed state path gives
exactly the original finite Markov path weight. -/
theorem sum_finiteMultiLevelBernoulliCoupledWeight_stateFiber
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha] {m t : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (x : alpha)
    (states : FiniteTrajectory alpha t) :
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
      if finiteCoupledStateProjection path = states then
        finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
      else 0) =
      finiteTrajectoryWeight P t x states := by
  classical
  let e : FiniteTrajectory (alpha × (Fin m -> Bool)) t ≃
      FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t :=
    finiteTrajectoryProdEquiv
  calc
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
        if finiteCoupledStateProjection path = states then
          finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
        else 0) =
        ∑ z : FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t,
          if z.1 = states then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
              (zipFiniteTrajectories z.1 z.2)
          else 0 := by
      refine Fintype.sum_equiv e
        (fun path : FiniteTrajectory (alpha × (Fin m -> Bool)) t =>
          if finiteCoupledStateProjection path = states then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
          else 0)
        (fun z : FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t =>
          if z.1 = states then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
              (zipFiniteTrajectories z.1 z.2)
          else 0) ?_
      intro path
      rfl
    _ = ∑ s : FiniteTrajectory alpha t,
          ∑ labels : FiniteTrajectory (Fin m -> Bool) t,
            if s = states then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
                (zipFiniteTrajectories s labels)
            else 0 := by
      simpa using
        (Fintype.sum_prod_type
          (fun z : FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t =>
            if z.1 = states then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
                (zipFiniteTrajectories z.1 z.2)
            else 0))
    _ = ∑ labels : FiniteTrajectory (Fin m -> Bool) t,
          finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
            (zipFiniteTrajectories states labels) := by
      simp
    _ = finiteTrajectoryWeight P t x states :=
      finiteMultiLevelBernoulliCoupledWeight_state_marginal
        P V hbound p t x states

/-- Summing finite adaptive coupled weights over the fiber of a fixed vector-label path
gives its exact i.i.d. product-Bernoulli weight. -/
theorem sum_finiteMultiLevelBernoulliCoupledWeight_labelFiber
    {alpha : Type*} [Fintype alpha] {m t : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real) (hp : forall i, 0 < p i)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (labels : FiniteTrajectory (Fin m -> Bool) t) :
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
      if finiteCoupledLabelProjection path = labels then
        finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
      else 0) =
      finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t labels := by
  classical
  let e : FiniteTrajectory (alpha × (Fin m -> Bool)) t ≃
      FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t :=
    finiteTrajectoryProdEquiv
  calc
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
        if finiteCoupledLabelProjection path = labels then
          finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
        else 0) =
        ∑ z : FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t,
          if z.2 = labels then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
              (zipFiniteTrajectories z.1 z.2)
          else 0 := by
      refine Fintype.sum_equiv e
        (fun path : FiniteTrajectory (alpha × (Fin m -> Bool)) t =>
          if finiteCoupledLabelProjection path = labels then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
          else 0)
        (fun z : FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t =>
          if z.2 = labels then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
              (zipFiniteTrajectories z.1 z.2)
          else 0) ?_
      intro path
      rfl
    _ = ∑ states : FiniteTrajectory alpha t,
          ∑ ell : FiniteTrajectory (Fin m -> Bool) t,
            if ell = labels then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
                (zipFiniteTrajectories states ell)
            else 0 := by
      simpa using
        (Fintype.sum_prod_type
          (fun z : FiniteTrajectory alpha t × FiniteTrajectory (Fin m -> Bool) t =>
            if z.2 = labels then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
                (zipFiniteTrajectories z.1 z.2)
            else 0))
    _ = ∑ states : FiniteTrajectory alpha t,
          finiteMultiLevelBernoulliCoupledWeight P V hbound p t x
            (zipFiniteTrajectories states labels) := by
      simp
    _ = finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t labels :=
      finiteMultiLevelBernoulliCoupledWeight_label_marginal
        P hP V hbound p hp hexit t x labels

/-- Time-homogeneous transition matrix whose every next-vector row is the same product
Bernoulli vector weight. -/
noncomputable def iidBernoulliLevelVectorTransitionMatrix
    {m : Nat} (p : Fin m -> Real) :
    TransitionMatrix (Fin m -> Bool) :=
  fun _ bits => bernoulliLevelVectorWeight p bits

/-- The i.i.d. vector transition matrix is stochastic under coordinatewise probability
bounds. -/
theorem iidBernoulliLevelVectorTransitionMatrix_stochastic
    {m : Nat} (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1) :
    IsStochastic (iidBernoulliLevelVectorTransitionMatrix p) := by
  constructor
  · intro current bits
    unfold iidBernoulliLevelVectorTransitionMatrix
    exact bernoulliLevelVectorWeight_nonneg p hp0 hp1 bits
  · intro current
    unfold iidBernoulliLevelVectorTransitionMatrix
    exact sum_bernoulliLevelVectorWeight p

/-- Finite trajectories of the constant-row vector transition matrix have exactly the
recursive i.i.d. label weight. -/
theorem finiteTrajectoryWeight_iidBernoulliLevelVector_eq
    {m : Nat} (p : Fin m -> Real) :
    forall t (current : Fin m -> Bool)
      (labels : FiniteTrajectory (Fin m -> Bool) t),
      finiteTrajectoryWeight
          (iidBernoulliLevelVectorTransitionMatrix p)
          t current labels =
        finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t labels := by
  intro t
  induction t with
  | zero =>
      intro current labels
      rfl
  | succ t ih =>
      intro current labels
      simp only [finiteTrajectoryWeight, finiteIIDLabelWeight]
      rw [ih (labels 0) (Fin.tail labels)]
      rfl

/-- The finite coupled measure projected to states is exactly the original finite
trajectory measure. -/
theorem finiteMultiLevelBernoulliCoupledMeasure_map_stateProjection
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    (finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x).map
      (finiteCoupledStateProjection
        (alpha := alpha) (beta := Fin m -> Bool) (t := t)) =
      finiteTrajectoryMeasure P hP t x := by
  classical
  apply Measure.ext_iff_singleton.mpr
  intro states
  have hproj : Measurable
      (finiteCoupledStateProjection
        (alpha := alpha) (beta := Fin m -> Bool) (t := t)) :=
    measurable_of_finite _
  rw [Measure.map_apply hproj (measurableSet_singleton states)]
  have hpre :
      (finiteCoupledStateProjection
          (alpha := alpha) (beta := Fin m -> Bool) (t := t)) ⁻¹' {states} =
        {path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
          finiteCoupledStateProjection path = states} := by
    ext path
    simp
  rw [hpre]
  have hEvent : MeasurableSet
      {path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
        finiteCoupledStateProjection path = states} :=
    ({path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
      finiteCoupledStateProjection path = states} :
        Set (FiniteTrajectory (alpha × (Fin m -> Bool)) t)).to_countable.measurableSet
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteMultiLevelBernoulliCoupledMeasure_singleton
    P hP V hbound p hp hp1 hexit t x]
  have hnonneg :
      ∀ path ∈
        (Finset.univ : Finset (FiniteTrajectory (alpha × (Fin m -> Bool)) t)),
        0 <=
          (if finiteCoupledStateProjection path = states then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
          else 0) := by
    intro path _hpath
    by_cases hs : finiteCoupledStateProjection path = states
    · simpa [hs] using
        finiteMultiLevelBernoulliCoupledWeight_nonneg
          P hP V hbound p hp hp1 hexit t x path
    · simp [hs]
  calc
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
        {q : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
          finiteCoupledStateProjection q = states}.indicator
            (fun _ => (1 : ENNReal)) path *
          ENNReal.ofReal
            (finiteMultiLevelBernoulliCoupledWeight
              P V hbound p t x path)) =
        ∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
          ENNReal.ofReal
            (if finiteCoupledStateProjection path = states then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
            else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hs : finiteCoupledStateProjection path = states <;> simp [hs]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
          if finiteCoupledStateProjection path = states then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
          else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal (finiteTrajectoryWeight P t x states) := by
      rw [sum_finiteMultiLevelBernoulliCoupledWeight_stateFiber
        P V hbound p x states]
    _ = finiteTrajectoryMeasure P hP t x {states} := by
      symm
      exact finiteTrajectoryMeasure_singleton P hP t x states

/-- The finite coupled measure projected to vector labels is exactly the finite path law
of the constant-row i.i.d. product-Bernoulli transition matrix. -/
theorem finiteMultiLevelBernoulliCoupledMeasure_map_labelProjection
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    (finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x).map
      (finiteCoupledLabelProjection
        (alpha := alpha) (beta := Fin m -> Bool) (t := t)) =
      finiteTrajectoryMeasure
        (iidBernoulliLevelVectorTransitionMatrix p)
        (iidBernoulliLevelVectorTransitionMatrix_stochastic
          p (fun i => le_of_lt (hp i)) hp1)
        t adaptiveCoupledInitialBits := by
  classical
  apply Measure.ext_iff_singleton.mpr
  intro labels
  have hproj : Measurable
      (finiteCoupledLabelProjection
        (alpha := alpha) (beta := Fin m -> Bool) (t := t)) :=
    measurable_of_finite _
  rw [Measure.map_apply hproj (measurableSet_singleton labels)]
  have hpre :
      (finiteCoupledLabelProjection
          (alpha := alpha) (beta := Fin m -> Bool) (t := t)) ⁻¹' {labels} =
        {path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
          finiteCoupledLabelProjection path = labels} := by
    ext path
    simp
  rw [hpre]
  have hEvent : MeasurableSet
      {path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
        finiteCoupledLabelProjection path = labels} :=
    ({path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
      finiteCoupledLabelProjection path = labels} :
        Set (FiniteTrajectory (alpha × (Fin m -> Bool)) t)).to_countable.measurableSet
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteMultiLevelBernoulliCoupledMeasure_singleton
    P hP V hbound p hp hp1 hexit t x]
  have hnonneg :
      ∀ path ∈
        (Finset.univ : Finset (FiniteTrajectory (alpha × (Fin m -> Bool)) t)),
        0 <=
          (if finiteCoupledLabelProjection path = labels then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
          else 0) := by
    intro path _hpath
    by_cases hs : finiteCoupledLabelProjection path = labels
    · simpa [hs] using
        finiteMultiLevelBernoulliCoupledWeight_nonneg
          P hP V hbound p hp hp1 hexit t x path
    · simp [hs]
  calc
    (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
        {q : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
          finiteCoupledLabelProjection q = labels}.indicator
            (fun _ => (1 : ENNReal)) path *
          ENNReal.ofReal
            (finiteMultiLevelBernoulliCoupledWeight
              P V hbound p t x path)) =
        ∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
          ENNReal.ofReal
            (if finiteCoupledLabelProjection path = labels then
              finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
            else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hs : finiteCoupledLabelProjection path = labels <;> simp [hs]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory (alpha × (Fin m -> Bool)) t,
          if finiteCoupledLabelProjection path = labels then
            finiteMultiLevelBernoulliCoupledWeight P V hbound p t x path
          else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal
        (finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t labels) := by
      rw [sum_finiteMultiLevelBernoulliCoupledWeight_labelFiber
        P hP V hbound p hp hexit x labels]
    _ = ENNReal.ofReal
        (finiteTrajectoryWeight
          (iidBernoulliLevelVectorTransitionMatrix p)
          t adaptiveCoupledInitialBits labels) := by
      rw [finiteTrajectoryWeight_iidBernoulliLevelVector_eq]
    _ = finiteTrajectoryMeasure
        (iidBernoulliLevelVectorTransitionMatrix p)
        (iidBernoulliLevelVectorTransitionMatrix_stochastic
          p (fun i => le_of_lt (hp i)) hp1)
        t adaptiveCoupledInitialBits {labels} := by
      symm
      exact finiteTrajectoryMeasure_singleton
        (iidBernoulliLevelVectorTransitionMatrix p)
        (iidBernoulliLevelVectorTransitionMatrix_stochastic
          p (fun i => le_of_lt (hp i)) hp1)
        t adaptiveCoupledInitialBits labels

/-- First `t` post-initial state coordinates of an infinite coupled pair path. -/
def adaptiveCoupledStatePrefix
    {alpha : Type*} {m : Nat} (t : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool))) : FiniteTrajectory alpha t :=
  finiteCoupledStateProjection (transitionTrajectoryTail t path)

/-- First `t` emitted vector labels of an infinite coupled pair path. -/
def adaptiveCoupledLabelPrefix
    {alpha : Type*} {m : Nat} (t : Nat)
    (path : Nat -> (alpha × (Fin m -> Bool))) :
    FiniteTrajectory (Fin m -> Bool) t :=
  finiteCoupledLabelProjection (transitionTrajectoryTail t path)

@[fun_prop] theorem measurable_adaptiveCoupledStatePrefix
    {alpha : Type*} [MeasurableSpace alpha] {m : Nat} (t : Nat) :
    Measurable (adaptiveCoupledStatePrefix
      (alpha := alpha) (m := m) t) := by
  unfold adaptiveCoupledStatePrefix finiteCoupledStateProjection
  fun_prop

@[fun_prop] theorem measurable_adaptiveCoupledLabelPrefix
    {alpha : Type*} [MeasurableSpace alpha] {m : Nat} (t : Nat) :
    Measurable (adaptiveCoupledLabelPrefix
      (alpha := alpha) (m := m) t) := by
  unfold adaptiveCoupledLabelPrefix finiteCoupledLabelProjection
  fun_prop

/-- Every finite state cylinder of the infinite adaptive coupled law is exactly the
ordinary finite trajectory law. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_map_statePrefix_eq_finiteTrajectoryMeasure
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
      (adaptiveCoupledStatePrefix (alpha := alpha) (m := m) t) =
      finiteTrajectoryMeasure P hP t x := by
  have htail : Measurable
      (transitionTrajectoryTail
        (α := alpha × (Fin m -> Bool)) t) :=
    measurable_transitionTrajectoryTail
      (α := alpha × (Fin m -> Bool)) t
  have hproj : Measurable
      (finiteCoupledStateProjection
        (alpha := alpha) (beta := Fin m -> Bool) (t := t)) :=
    measurable_of_finite _
  have hfun :
      adaptiveCoupledStatePrefix (alpha := alpha) (m := m) t =
        finiteCoupledStateProjection ∘
          transitionTrajectoryTail (α := alpha × (Fin m -> Bool)) t := by
    rfl
  rw [hfun]
  rw [← Measure.map_map hproj htail]
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_map_tail_eq_finiteCoupledMeasure
    P hP V hbound p hp hp1 hexit x t]
  exact finiteMultiLevelBernoulliCoupledMeasure_map_stateProjection
    P hP V hbound p hp hp1 hexit t x

/-- Every finite Boolean-vector cylinder of the infinite adaptive coupled law is exactly
its i.i.d. product-Bernoulli finite trajectory law. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_map_labelPrefix_eq_finiteIIDMeasure
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
      (adaptiveCoupledLabelPrefix (alpha := alpha) (m := m) t) =
      finiteTrajectoryMeasure
        (iidBernoulliLevelVectorTransitionMatrix p)
        (iidBernoulliLevelVectorTransitionMatrix_stochastic
          p (fun i => le_of_lt (hp i)) hp1)
        t adaptiveCoupledInitialBits := by
  have htail : Measurable
      (transitionTrajectoryTail
        (α := alpha × (Fin m -> Bool)) t) :=
    measurable_transitionTrajectoryTail
      (α := alpha × (Fin m -> Bool)) t
  have hproj : Measurable
      (finiteCoupledLabelProjection
        (alpha := alpha) (beta := Fin m -> Bool) (t := t)) :=
    measurable_of_finite _
  have hfun :
      adaptiveCoupledLabelPrefix (alpha := alpha) (m := m) t =
        finiteCoupledLabelProjection ∘
          transitionTrajectoryTail (α := alpha × (Fin m -> Bool)) t := by
    rfl
  rw [hfun]
  rw [← Measure.map_map hproj htail]
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_map_tail_eq_finiteCoupledMeasure
    P hP V hbound p hp hp1 hexit x t]
  exact finiteMultiLevelBernoulliCoupledMeasure_map_labelProjection
    P hP V hbound p hp hp1 hexit t x

/-- Under the finite adaptive coupled measure, a path has strictly positive coupled
weight almost surely.  Zero-weight atoms carry zero PMF mass. -/
theorem finiteMultiLevelBernoulliCoupledMeasure_ae_weight_pos
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : Nat) (x : alpha) :
    ∀ᵐ path ∂(finiteMultiLevelBernoulliCoupledMeasure
        P hP V hbound p hp hp1 hexit t x),
      0 < finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x path := by
  classical
  rw [ae_iff]
  have hEvent : MeasurableSet
      {path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
        ¬ 0 < finiteMultiLevelBernoulliCoupledWeight
          P V hbound p t x path} :=
    ({path : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
      ¬ 0 < finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x path} :
        Set (FiniteTrajectory (alpha × (Fin m -> Bool)) t)).to_countable.measurableSet
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteMultiLevelBernoulliCoupledMeasure_singleton
    P hP V hbound p hp hp1 hexit t x]
  apply Finset.sum_eq_zero
  intro path _hpath
  have hnonneg := finiteMultiLevelBernoulliCoupledWeight_nonneg
    P hP V hbound p hp hp1 hexit t x path
  by_cases hpos : 0 < finiteMultiLevelBernoulliCoupledWeight
      P V hbound p t x path
  · simp [hpos]
  · have hzero : finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x path = 0 :=
      le_antisymm (not_lt.mp hpos) hnonneg
    simp [hzero]

/-- Almost surely, every finite post-initial prefix of the infinite adaptive coupled
trajectory has strictly positive coupled path weight. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_ae_all_prefixWeights_pos
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) :
    ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      forall t : Nat,
        0 < finiteMultiLevelBernoulliCoupledWeight
          P V hbound p t x (transitionTrajectoryTail t path) := by
  rw [ae_all_iff]
  intro t
  have htail : Measurable
      (transitionTrajectoryTail
        (α := alpha × (Fin m -> Bool)) t) :=
    measurable_transitionTrajectoryTail
      (α := alpha × (Fin m -> Bool)) t
  have hset : MeasurableSet
      {q : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
        0 < finiteMultiLevelBernoulliCoupledWeight
          P V hbound p t x q} :=
    ({q : FiniteTrajectory (alpha × (Fin m -> Bool)) t |
      0 < finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x q} :
        Set (FiniteTrajectory (alpha × (Fin m -> Bool)) t)).to_countable.measurableSet
  change ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
      P hP V hbound p hp hp1 hexit x),
    0 < finiteMultiLevelBernoulliCoupledWeight
      P V hbound p t x (transitionTrajectoryTail t path)
  rw [← ae_map_iff htail.aemeasurable hset]
  rw [adaptiveMultiLevelCoupledTrajectoryMeasure_map_tail_eq_finiteCoupledMeasure
    P hP V hbound p hp hp1 hexit x t]
  exact finiteMultiLevelBernoulliCoupledMeasure_ae_weight_pos
    P hP V hbound p hp hp1 hexit t x

/-- The finite pair prefix of an infinite coupled path is exactly the zip of its
post-initial state prefix and emitted vector-label prefix. -/
theorem transitionTrajectoryTail_eq_zip_adaptiveCoupledPrefixes
    {alpha : Type*} {m T : Nat}
    (path : Nat -> (alpha × (Fin m -> Bool))) :
    transitionTrajectoryTail T path =
      zipFiniteTrajectories
        (transitionTrajectoryTail T (adaptiveCoupledStatePath path))
        (transitionLabelTrajectory T (adaptiveCoupledLabelStream path)) := by
  funext j
  rfl

/-- If all finite prefixes of a coupled pair path have positive total weight, then every
individual adaptive transition on that path has positive one-step coupled weight. -/
theorem hasPositiveAdaptiveCoupledStepSupport_of_all_prefixWeights_pos
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (path : Nat -> (alpha × (Fin m -> Bool)))
    (hprefix : forall T : Nat,
      0 < finiteMultiLevelBernoulliCoupledWeight
        P V hbound p T x (transitionTrajectoryTail T path)) :
    HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x
        (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path) := by
  unfold HasPositiveAdaptiveCoupledStepSupport
  intro t
  have hpref := hprefix (t + 1)
  rw [transitionTrajectoryTail_eq_zip_adaptiveCoupledPrefixes path] at hpref
  rw [finiteMultiLevelBernoulliCoupledWeight_streamPrefix_eq_prefixWeight] at hpref
  have hstep_nonneg :
      0 <= multiLevelBernoulliCoupledStepWeight
        P V hbound p
        (transitionTrajectoryState x (adaptiveCoupledStatePath path) t)
        (transitionTrajectoryState x (adaptiveCoupledStatePath path) (t + 1))
        (adaptiveCoupledLabelStream path t) :=
    multiLevelBernoulliCoupledStepWeight_nonneg
      P hP V hbound p hp hp1 hexit
      (transitionTrajectoryState x (adaptiveCoupledStatePath path) t)
      (transitionTrajectoryState x (adaptiveCoupledStatePath path) (t + 1))
      (adaptiveCoupledLabelStream path t)
  by_contra hnot
  have hstep_zero :
      multiLevelBernoulliCoupledStepWeight
        P V hbound p
        (transitionTrajectoryState x (adaptiveCoupledStatePath path) t)
        (transitionTrajectoryState x (adaptiveCoupledStatePath path) (t + 1))
        (adaptiveCoupledLabelStream path t) = 0 :=
    le_antisymm (not_lt.mp hnot) hstep_nonneg
  have hprod_zero :
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x
        (adaptiveCoupledStatePath path)
        (adaptiveCoupledLabelStream path) (t + 1) = 0 := by
    unfold multiLevelBernoulliCoupledPrefixWeight
    rw [Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.lt_succ_self t))]
    exact hstep_zero
  exact (ne_of_gt hpref) hprod_zero

/-- Main fix-48 support endpoint: positive adaptive coupled-step support holds almost
surely under the genuine infinite adaptive coupled law. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_ae_positiveAdaptiveSupport
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) :
    ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      HasPositiveAdaptiveCoupledStepSupport
        P V hbound p x
          (adaptiveCoupledStatePath path)
          (adaptiveCoupledLabelStream path) := by
  filter_upwards
    [adaptiveMultiLevelCoupledTrajectoryMeasure_ae_all_prefixWeights_pos
      P hP V hbound p hp hp1 hexit x] with path hprefix
  exact hasPositiveAdaptiveCoupledStepSupport_of_all_prefixWeights_pos
    P hP V hbound p hp hp1 hexit x path hprefix

end ECRuntime
