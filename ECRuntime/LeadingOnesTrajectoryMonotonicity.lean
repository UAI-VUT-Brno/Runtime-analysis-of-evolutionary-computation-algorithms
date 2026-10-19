import ECRuntime.LeadingOnesRuntimeChargeDecomposition
import ECRuntime.EventLevelFailureCountLocalization
import ECRuntime.FiniteMarginalIdentification
import Mathlib

open scoped BigOperators ENNReal
open Finset Function MeasureTheory ProbabilityTheory

namespace ECRuntime

/-!
# Stage 27 fix 14: almost-sure monotonicity of the genuine LeadingOnes trajectory

Stage 27 fix 13 fix 1 compiler-verifies the exact pathwise charge decomposition and
its measure-level lift under one explicit stochastic premise: along the genuine
LeadingOnes trajectory, the canonical distance potential must be nonincreasing almost
surely.

For the `(1+1)` EA this premise is a consequence of elitist selection.  This module
closes that representation gap directly on the ordinary Ionescu--Tulcea trajectory
law.  The proof is split into reusable finite-state pieces:

* positive support of `onePlusOneTransition` can only reach states whose LeadingOnes
  potential is no larger than the parent potential;
* for a general finite stochastic transition matrix with monotone positive support,
  the final transition of every finite marginal is monotone almost surely;
* pulling these finite events back through all trajectory marginals and using
  `ae_all_iff` yields potential nonincrease at every absolute time almost surely.

The final corollaries discharge the monotonicity premise of the Stage-27-fix-13
measure-level charge decomposition.  The only remaining exact-runtime obligation is
therefore to identify the expected charge of each positive LeadingOnes level with its
already promoted first-entry mass times conditional geometric mean residence.
-/

/-- The state reached at absolute time `t` is the endpoint of the first `t`
post-initial coordinates of the infinite trajectory. -/
@[simp] theorem finiteTrajectoryEndpoint_transitionTrajectoryTail
    {α : Type*} (x : α) (path : ℕ → α) (t : ℕ) :
    finiteTrajectoryEndpoint x t (transitionTrajectoryTail t path) =
      transitionTrajectoryState x path t := by
  cases t <;> rfl

/-- Under monotone positive transition support, the last step of a finite trajectory
is potential-nonincreasing almost surely under the explicit finite trajectory law. -/
theorem finiteTrajectoryMeasure_ae_lastStep_potentialNonincreasing
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : α) (t : ℕ) :
    ∀ᵐ path ∂finiteTrajectoryMeasure P hP (t + 1) x,
      V (path (Fin.last t)) ≤
        V (finiteTrajectoryEndpoint x t (Fin.init path)) := by
  classical
  rw [ae_iff]
  have hEvent : MeasurableSet
      {path : FiniteTrajectory α (t + 1) |
        ¬ V (path (Fin.last t)) ≤
          V (finiteTrajectoryEndpoint x t (Fin.init path))} :=
    ({path : FiniteTrajectory α (t + 1) |
      ¬ V (path (Fin.last t)) ≤
        V (finiteTrajectoryEndpoint x t (Fin.init path))} :
        Set (FiniteTrajectory α (t + 1))).to_countable.measurableSet
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP (t + 1) x]
  apply Finset.sum_eq_zero
  intro path _hpath
  by_cases hbad :
      ¬ V (path (Fin.last t)) ≤
        V (finiteTrajectoryEndpoint x t (Fin.init path))
  · have hnotpos :
        ¬ 0 < P (finiteTrajectoryEndpoint x t (Fin.init path))
          (path (Fin.last t)) := by
      intro hpos
      exact hbad (hmonoP _ _ hpos)
    have htransZero :
        P (finiteTrajectoryEndpoint x t (Fin.init path))
          (path (Fin.last t)) = 0 := by
      exact le_antisymm (le_of_not_gt hnotpos) (hP.1 _ _)
    have hsnoc :
        Fin.snoc (Fin.init path) (path (Fin.last t)) = path := by
      exact Fin.snoc_init_self path
    have hweightZero : finiteTrajectoryWeight P (t + 1) x path = 0 := by
      rw [← hsnoc]
      rw [finiteTrajectoryWeight_snoc P t x (Fin.init path) (path (Fin.last t))]
      rw [htransZero, mul_zero]
    simp [hweightZero]
  · have hgood :
        V (path (Fin.last t)) ≤
          V (finiteTrajectoryEndpoint x t (Fin.init path)) :=
      not_not.mp hbad
    simp [hgood]

/-- A finite-state transition matrix whose positive support weakly decreases a natural
potential generates an infinite trajectory on which that potential is nonincreasing
almost surely. -/
theorem transitionTrajectoryMeasure_ae_potentialNonincreasing_of_support
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ)
    (hmonoP : HasPotentialNonincreasingTransitionSupport P V)
    (x : α) :
    ∀ᵐ path ∂transitionTrajectoryMeasure P hP x,
      IsPotentialNonincreasingAlong V x path := by
  unfold IsPotentialNonincreasingAlong
  rw [ae_all_iff]
  intro t
  have htail : Measurable
      (transitionTrajectoryTail (α := α) (t + 1)) :=
    measurable_transitionTrajectoryTail (α := α) (t + 1)
  have hset : MeasurableSet
      {q : FiniteTrajectory α (t + 1) |
        V (q (Fin.last t)) ≤
          V (finiteTrajectoryEndpoint x t (Fin.init q))} :=
    ({q : FiniteTrajectory α (t + 1) |
      V (q (Fin.last t)) ≤
        V (finiteTrajectoryEndpoint x t (Fin.init q))} :
        Set (FiniteTrajectory α (t + 1))).to_countable.measurableSet
  have hpull :
      ∀ᵐ path ∂transitionTrajectoryMeasure P hP x,
        V ((transitionTrajectoryTail (t + 1) path) (Fin.last t)) ≤
          V (finiteTrajectoryEndpoint x t
            (Fin.init (transitionTrajectoryTail (t + 1) path))) := by
    rw [← ae_map_iff htail.aemeasurable hset]
    rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure
      P hP x (t + 1)]
    exact finiteTrajectoryMeasure_ae_lastStep_potentialNonincreasing
      P hP V hmonoP x t
  filter_upwards [hpull] with path hstep
  rw [transitionTrajectoryTail_init t path] at hstep
  rw [finiteTrajectoryEndpoint_transitionTrajectoryTail] at hstep
  simpa [transitionTrajectoryTail] using hstep

/-- Every positive-probability `(1+1)`-EA LeadingOnes transition weakly decreases the
canonical distance potential.  The statement is independent of the numerical mutation
rate because it follows solely from deterministic elitist selection. -/
theorem onePlusOneTransition_leadingOnes_hasPotentialNonincreasingTransitionSupport
    {n : ℕ} (p : ℝ) :
    HasPotentialNonincreasingTransitionSupport
      (onePlusOneTransition p (leadingOnesReal (n := n)))
      (leadingOnesPotential (n := n)) := by
  classical
  intro x y hxy
  by_contra hnot
  have hgt : leadingOnesPotential x < leadingOnesPotential y := by
    omega
  have hzero :
      onePlusOneTransition p (leadingOnesReal (n := n)) x y = 0 := by
    unfold onePlusOneTransition pushforwardWeight
    apply Finset.sum_eq_zero
    intro mask _hmask
    have hle := leadingOnesPotential_selectedAfterMask_le x mask
    have hne :
        selectedAfterMask (leadingOnesReal (n := n)) x mask ≠ y := by
      intro heq
      rw [heq] at hle
      omega
    rw [if_neg hne]
  rw [hzero] at hxy
  exact (lt_irrefl (0 : ℝ)) hxy

/-- The genuine LeadingOnes `(1+1)`-EA trajectory has nonincreasing distance potential
almost surely for every stochastic mutation rate `0 ≤ p ≤ 1`. -/
theorem leadingOnesTrajectoryMeasure_ae_potentialNonincreasing
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n) :
    ∀ᵐ path ∂leadingOnesTrajectoryMeasure p hp0 hp1 x,
      IsPotentialNonincreasingAlong
        (leadingOnesPotential (n := n)) x path := by
  unfold leadingOnesTrajectoryMeasure
  exact transitionTrajectoryMeasure_ae_potentialNonincreasing_of_support
    (onePlusOneTransition p (leadingOnesReal (n := n)))
    (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
    (leadingOnesPotential (n := n))
    (onePlusOneTransition_leadingOnes_hasPotentialNonincreasingTransitionSupport p)
    x

/-- The fixed-initial LeadingOnes expected runtime is exactly the expected finite sum
of complete level charges; the almost-sure monotonicity premise from Stage 27 fix 13 is
now discharged internally. -/
theorem leadingOnesFixedInitialFirstHittingTimeExpectation_eq_levelChargeExpectation
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      ∫⁻ path : ℕ → BitString n,
        ∑ i : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x i path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
  exact
    leadingOnesFixedInitialFirstHittingTimeExpectation_eq_levelChargeExpectation_of_ae_nonincreasing
      p hp0 hp1 x
      (leadingOnesTrajectoryMeasure_ae_potentialNonincreasing p hp0 hp1 x)

/-- Uniform-initialization version of the exact runtime/charge expectation identity,
with potential monotonicity fully discharged for the genuine LeadingOnes process. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_levelChargeExpectation
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0 hp1 =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          ∫⁻ path : ℕ → BitString n,
            ∑ i : Fin n,
              trajectoryLevelCharge
                (leadingOnesPotential (n := n)) x i path
          ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
  exact
    leadingOnesUniformFirstHittingTimeExpectation_eq_levelChargeExpectation_of_ae_nonincreasing
      n p hp0 hp1
      (fun x => leadingOnesTrajectoryMeasure_ae_potentialNonincreasing p hp0 hp1 x)

end ECRuntime
