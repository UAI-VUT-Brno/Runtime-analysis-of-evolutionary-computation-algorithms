import ECRuntime.LeadingOnesOccupationRecurrenceAssembly
import Mathlib

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 23: exact same-level Markov lift and concrete occupation renewal

Stage 27 fix 22 fix 1 is compiler verified warning/error-free.  The remaining local
stochastic boundary is the same-level two-time branch

  P_x(LO(X_t)=i, LO(X_{t+1})=i)
    = (1 - p(1-p)^i) P_x(LO(X_t)=i).

This file proves that identity without adding a conditional-independence or abstract
strong-Markov assumption.  The genuine trajectory law is first projected to the
already identified explicit finite-trajectory measure.  A length-`t+1` path is then
split as `Fin.snoc pref y`; its weight factors into the old prefix weight and the one
final transition.  On every prefix whose endpoint has score `i`, the sum over final
states of score `i` is the compiler-promoted exact stay mass `1-p(1-p)^i`.

The result supplies `HasLeadingOnesExactStayBranch` unconditionally, closes the
concrete fixed-initial scalar renewal recurrence, and exposes the exact-time occupation
mass as the promoted entry/stay convolution.  The next slice can therefore be purely
countable-sum algebra: sum the convolution over time, interchange the two nonnegative
sums, evaluate the geometric tail, and obtain the fixed-initial occupation bridge.
-/

/-- Finite-path event that score level `i` is occupied at the final horizon. -/
def leadingOnesFiniteScoreLevelAtHorizonSet
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    Set (FiniteTrajectory (BitString n) t) :=
  {path | leadingOnes (finiteTrajectoryEndpoint x t path) = i.val}

/-- Finite-path version of the same-level two-time event at absolute times `t,t+1`. -/
def leadingOnesFiniteEqualThenExactAtNextSet
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    Set (FiniteTrajectory (BitString n) (t + 1)) :=
  {path |
    leadingOnes (finiteTrajectoryEndpoint x t (Fin.init path)) = i.val ∧
      leadingOnes (finiteTrajectoryEndpoint x (t + 1) path) = i.val}

/-- Appending one final state makes that state the new finite-trajectory endpoint. -/
@[simp] theorem finiteTrajectoryEndpoint_snoc
    {α : Type*} (x : α) (t : ℕ)
    (path : FiniteTrajectory α t) (y : α) :
    finiteTrajectoryEndpoint x (t + 1) (Fin.snoc path y) = y := by
  simp [finiteTrajectoryEndpoint]

/-- Forgetting the last coordinate of the first `t+1` post-initial states yields the
first `t` post-initial states. -/
@[simp] theorem Fin_init_transitionTrajectoryTail
    {α : Type*} (t : ℕ) (path : ℕ → α) :
    Fin.init (transitionTrajectoryTail (t + 1) path) =
      transitionTrajectoryTail t path := by
  funext j
  rfl

/-- The infinite exact-time occupation event is the pullback of its finite-horizon
endpoint event. -/
theorem leadingOnesScoreLevelAtTimeSet_eq_preimage_finiteHorizon
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesScoreLevelAtTimeSet x i t =
      transitionTrajectoryTail t ⁻¹'
        leadingOnesFiniteScoreLevelAtHorizonSet x i t := by
  ext path
  simp [leadingOnesScoreLevelAtTimeSet,
    leadingOnesFiniteScoreLevelAtHorizonSet]

/-- The infinite same-level two-time event is the pullback of the corresponding
finite-horizon event. -/
theorem leadingOnesEqualThenExactAtNextSet_eq_preimage_finiteHorizon
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesEqualThenExactAtNextSet x i t =
      transitionTrajectoryTail (t + 1) ⁻¹'
        leadingOnesFiniteEqualThenExactAtNextSet x i t := by
  ext path
  change
    (leadingOnes (transitionTrajectoryState x path t) = i.val ∧
        leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val) ↔
      (leadingOnes
            (finiteTrajectoryEndpoint x t
              (Fin.init (transitionTrajectoryTail (t + 1) path))) = i.val ∧
        leadingOnes
            (finiteTrajectoryEndpoint x (t + 1)
              (transitionTrajectoryTail (t + 1) path)) = i.val)
  rw [Fin_init_transitionTrajectoryTail]
  simp only [finiteTrajectoryEndpoint_transitionTrajectoryTail]

/-- Real path-weight mass of an arbitrary finite-trajectory event.  The membership
case split is hidden behind a noncomputable definition so theorem statements do not
require a `DecidablePred` instance for an opaque `Set`. -/
noncomputable def finiteTrajectorySetWeight
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (t : ℕ) (x : α)
    (E : Set (FiniteTrajectory α t)) : ℝ := by
  classical
  exact ∑ path : FiniteTrajectory α t,
    if path ∈ E then finiteTrajectoryWeight P t x path else 0

/-- Restricted finite-trajectory path weight is nonnegative for a stochastic kernel. -/
theorem finiteTrajectorySetWeight_nonneg
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (t : ℕ) (x : α) (E : Set (FiniteTrajectory α t)) :
    0 ≤ finiteTrajectorySetWeight P t x E := by
  classical
  unfold finiteTrajectorySetWeight
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hmem : path ∈ E
  · simp only [if_pos hmem]
    exact finiteTrajectoryWeight_nonneg P hP t x path
  · simp [hmem]

/-- On a finite state space, the explicit finite-trajectory measure of an arbitrary
set is the `ENNReal.ofReal` embedding of its restricted real path-weight mass. -/
theorem finiteTrajectoryMeasure_apply_eq_ofReal_setWeight
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (t : ℕ) (x : α) (E : Set (FiniteTrajectory α t)) :
    finiteTrajectoryMeasure P hP t x E =
      ENNReal.ofReal (finiteTrajectorySetWeight P t x E) := by
  classical
  have hE : MeasurableSet E := E.to_countable.measurableSet
  rw [← MeasureTheory.lintegral_indicator_fun_one hE]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP t x]
  have hnonneg :
      ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory α t)),
        0 ≤ (if path ∈ E then finiteTrajectoryWeight P t x path else 0) := by
    intro path _hpath
    by_cases hmem : path ∈ E
    · simp only [if_pos hmem]
      exact finiteTrajectoryWeight_nonneg P hP t x path
    · simp [hmem]
  calc
    (∑ path : FiniteTrajectory α t,
        E.indicator (fun _ => (1 : ENNReal)) path *
          ENNReal.ofReal (finiteTrajectoryWeight P t x path)) =
        ∑ path : FiniteTrajectory α t,
          ENNReal.ofReal
            (if path ∈ E then finiteTrajectoryWeight P t x path else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hmem : path ∈ E
      · simp [hmem]
      · simp [hmem]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory α t,
          if path ∈ E then finiteTrajectoryWeight P t x path else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal (finiteTrajectorySetWeight P t x E) := by
      rfl

/-- The genuine fixed-initial occupation mass is the explicit finite-trajectory mass
of the endpoint score-level event. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_eq_finiteTrajectoryMeasure
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i t =
      finiteTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
        t x (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have htail : Measurable (transitionTrajectoryTail (α := BitString n) t) :=
    measurable_transitionTrajectoryTail (α := BitString n) t
  have hEvent : MeasurableSet (leadingOnesFiniteScoreLevelAtHorizonSet x i t) :=
    (leadingOnesFiniteScoreLevelAtHorizonSet x i t).to_countable.measurableSet
  unfold leadingOnesFixedInitialScoreLevelOccupationMass
  rw [leadingOnesScoreLevelAtTimeSet_eq_preimage_finiteHorizon x i t]
  unfold leadingOnesTrajectoryMeasure
  change transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail t ⁻¹'
        leadingOnesFiniteScoreLevelAtHorizonSet x i t) = _
  rw [← Measure.map_apply htail hEvent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]

/-- The genuine same-level branch mass is the explicit finite-trajectory mass of the
corresponding two-time finite event. -/
theorem leadingOnesTrajectoryMeasure_equalThenExactAtNextSet_eq_finiteTrajectoryMeasure
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesEqualThenExactAtNextSet x i t) =
      finiteTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
        (t + 1) x (leadingOnesFiniteEqualThenExactAtNextSet x i t) := by
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have htail : Measurable
      (transitionTrajectoryTail (α := BitString n) (t + 1)) :=
    measurable_transitionTrajectoryTail (α := BitString n) (t + 1)
  have hEvent : MeasurableSet (leadingOnesFiniteEqualThenExactAtNextSet x i t) :=
    (leadingOnesFiniteEqualThenExactAtNextSet x i t).to_countable.measurableSet
  rw [leadingOnesEqualThenExactAtNextSet_eq_preimage_finiteHorizon x i t]
  unfold leadingOnesTrajectoryMeasure
  change transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail (t + 1) ⁻¹'
        leadingOnesFiniteEqualThenExactAtNextSet x i t) = _
  rw [← Measure.map_apply htail hEvent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure
    P hP x (t + 1)]

/-- Closed-interval version of the elementary upper bound on the exact exit
probability. -/
theorem leadingOnesLevelExitProbability_le_one_of_mem_Icc
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin n) :
    leadingOnesLevelExitProbability p i ≤ 1 := by
  unfold leadingOnesLevelExitProbability
  have hq0 : 0 ≤ 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hpow : (1 - p) ^ i.val ≤ 1 := pow_le_one₀ hq0 hq1
  calc
    p * (1 - p) ^ i.val ≤ p * 1 :=
      mul_le_mul_of_nonneg_left hpow hp0
    _ = p := by ring
    _ ≤ 1 := hp1

/-- Restricted real path-weight mass of the finite same-level event factors as the
constant stay probability times the restricted endpoint-level prefix mass. -/
theorem leadingOnesFiniteEqualThenExact_setWeight_eq_stay_mul_scoreSetWeight
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    finiteTrajectorySetWeight
        (onePlusOneTransition p (leadingOnesReal (n := n))) (t + 1) x
        (leadingOnesFiniteEqualThenExactAtNextSet x i t) =
      (1 - leadingOnesLevelExitProbability p i) *
        finiteTrajectorySetWeight
          (onePlusOneTransition p (leadingOnesReal (n := n))) t x
          (leadingOnesFiniteScoreLevelAtHorizonSet x i t) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  change
    finiteTrajectorySetWeight P (t + 1) x
        (leadingOnesFiniteEqualThenExactAtNextSet x i t) =
      (1 - leadingOnesLevelExitProbability p i) *
        finiteTrajectorySetWeight P t x
          (leadingOnesFiniteScoreLevelAtHorizonSet x i t)
  unfold finiteTrajectorySetWeight
  rw [sum_finiteTrajectory_snoc]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro pref _hpref
  by_cases hlevel : leadingOnes (finiteTrajectoryEndpoint x t pref) = i.val
  · have hstay := onePlusOneTransition_leadingOnes_exactLevel_stayMass_eq
      hp0 hp1 i (finiteTrajectoryEndpoint x t pref) hlevel
    calc
      (∑ y : BitString n,
          if Fin.snoc pref y ∈ leadingOnesFiniteEqualThenExactAtNextSet x i t then
            finiteTrajectoryWeight P (t + 1) x (Fin.snoc pref y)
          else 0) =
          ∑ y : BitString n,
            if leadingOnes y = i.val then
              finiteTrajectoryWeight P t x pref *
                P (finiteTrajectoryEndpoint x t pref) y
            else 0 := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [finiteTrajectoryWeight_snoc P]
        simp only [leadingOnesFiniteEqualThenExactAtNextSet, Set.mem_setOf_eq,
          Fin.init_snoc, finiteTrajectoryEndpoint_snoc, hlevel, true_and]
      _ = finiteTrajectoryWeight P t x pref *
          finiteEventMass
            (P (finiteTrajectoryEndpoint x t pref))
            (fun y => leadingOnes y = i.val) := by
        unfold finiteEventMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        by_cases hy : leadingOnes y = i.val
        · simp [hy]
        · simp [hy]
      _ = finiteTrajectoryWeight P t x pref *
          (1 - leadingOnesLevelExitProbability p i) := by
        rw [hstay]
      _ = (1 - leadingOnesLevelExitProbability p i) *
          (if pref ∈ leadingOnesFiniteScoreLevelAtHorizonSet x i t then
            finiteTrajectoryWeight P t x pref else 0) := by
        simp [leadingOnesFiniteScoreLevelAtHorizonSet, hlevel, mul_comm]
  · simp [leadingOnesFiniteEqualThenExactAtNextSet,
      leadingOnesFiniteScoreLevelAtHorizonSet, hlevel]

/-- Exact Markov lift for the same-level branch under the genuine fixed-initial
trajectory law. -/
theorem leadingOnesTrajectoryMeasure_equalThenExactAtNextSet_eq_stay_mul_occupation
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesEqualThenExactAtNextSet x i t) =
      leadingOnesLevelStayENNReal p i *
        leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i t := by
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have hstay0 : 0 ≤ 1 - leadingOnesLevelExitProbability p i := by
    exact sub_nonneg.mpr
      (leadingOnesLevelExitProbability_le_one_of_mem_Icc hp0 hp1 i)
  rw [leadingOnesTrajectoryMeasure_equalThenExactAtNextSet_eq_finiteTrajectoryMeasure
    p hp0 hp1 x i t]
  rw [finiteTrajectoryMeasure_apply_eq_ofReal_setWeight P hP (t + 1) x
    (leadingOnesFiniteEqualThenExactAtNextSet x i t)]
  rw [leadingOnesFiniteEqualThenExact_setWeight_eq_stay_mul_scoreSetWeight
    p hp0 hp1 x i t]
  rw [ENNReal.ofReal_mul hstay0]
  change
    leadingOnesLevelStayENNReal p i *
        ENNReal.ofReal
          (finiteTrajectorySetWeight P t x
            (leadingOnesFiniteScoreLevelAtHorizonSet x i t)) =
      leadingOnesLevelStayENNReal p i *
        leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i t
  apply congrArg (fun z : ENNReal => leadingOnesLevelStayENNReal p i * z)
  rw [leadingOnesFixedInitialScoreLevelOccupationMass_eq_finiteTrajectoryMeasure
    p hp0 hp1 x i t]
  symm
  exact finiteTrajectoryMeasure_apply_eq_ofReal_setWeight P hP t x
    (leadingOnesFiniteScoreLevelAtHorizonSet x i t)

/-- The sole interface left by fix 22 is now discharged unconditionally. -/
theorem hasLeadingOnesExactStayBranch
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) :
    HasLeadingOnesExactStayBranch p hp0 hp1 x i := by
  intro t
  exact leadingOnesTrajectoryMeasure_equalThenExactAtNextSet_eq_stay_mul_occupation
    p hp0 hp1 x i t

/-- Hence the genuine fixed-initial occupation sequence satisfies the concrete renewal
recurrence with no remaining stochastic hypothesis. -/
theorem hasLeadingOnesFixedInitialScoreLevelOccupationRenewal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) :
    HasLeadingOnesFixedInitialScoreLevelOccupationRenewal p hp0 hp1 x i := by
  exact hasLeadingOnesFixedInitialScoreLevelOccupationRenewal_of_exactStayBranch
    p hp0 hp1 x i (hasLeadingOnesExactStayBranch p hp0 hp1 x i)

/-- Exact-time occupation mass is therefore the finite convolution of exact-entry
masses with powers of the exact stay factor. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_eq_entryConvolution
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i t =
      ∑ s ∈ Finset.range (t + 1),
        leadingOnesFixedInitialExactEntryENNMass p i x s *
          (leadingOnesLevelStayENNReal p i) ^ (t - s) := by
  exact
    leadingOnesFixedInitialScoreLevelOccupationMass_eq_entryConvolution_of_renewal
      p hp0 hp1 x i
      (hasLeadingOnesFixedInitialScoreLevelOccupationRenewal p hp0 hp1 x i)
      t

end ECRuntime
