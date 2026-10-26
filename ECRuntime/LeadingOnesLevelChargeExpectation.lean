import ECRuntime.LeadingOnesLevelIndexBridge
import Mathlib

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 17: measurable score-indexed level-charge expectations

Stage 27 fix 16 compiler-verifies the index reversal that identifies LeadingOnes score
level `i` with positive distance-potential charge coordinate `n-(i+1)`.  The remaining
exact-runtime bridge can therefore be proved one score level at a time.

Before conditioning on the exact first-entry time, however, the complete charge itself
has to be available as a genuine measurable trajectory observable, and the finite sum
over score levels has to be exchangeable with the trajectory `lintegral` and the finite
uniform average over initial states.

This module performs only that measure-theoretic bookkeeping step:

* trajectory states at fixed absolute times are measurable;
* finite-horizon and complete positive-level charges are measurable on a finite state
  space;
* a score-indexed complete charge is packaged as a fixed-initial and uniform expected
  charge;
* the `lintegral` of the finite score-level sum is the finite sum of the individual
  charge `lintegral`s;
* consequently the genuine uniformly initialized expected first-hitting time is a
  finite sum of genuine per-score-level expected charges.

No first-entry/residence independence or conditional factorization is asserted here.
After this interface is compiler verified, the remaining proof may fix one `i : Fin n`
and identify exactly one summand with the already assembled first-entry-mass times
conditional-residence contribution.
-/

/-- For a fixed deterministic initial state, the absolute state at any fixed time is a
measurable function of the infinite post-initial trajectory. -/
theorem measurable_transitionTrajectoryState_fixed
    {α : Type*} [MeasurableSpace α]
    (x : α) (t : ℕ) :
    Measurable (fun path : ℕ → α => transitionTrajectoryState x path t) := by
  cases t with
  | zero =>
      exact (measurable_const : Measurable (fun _ : ℕ → α => x))
  | succ t =>
      simpa using
        (measurable_pi_apply (t + 1) :
          Measurable (fun path : ℕ → α => path (t + 1)))

/-- On a finite measurable state space, every finite-horizon positive-level charge is
measurable as a function of the infinite trajectory. -/
theorem measurable_finiteHorizonLevelCharge
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    {m : ℕ} (V : α → ℕ) (x : α) (T : ℕ) (i : Fin m) :
    Measurable (fun path : ℕ → α =>
      finiteHorizonLevelCharge V x path T i) := by
  unfold finiteHorizonLevelCharge
  exact Finset.measurable_sum (Finset.range T) (by
    intro t _ht
    exact
      (measurable_of_finite
        (fun y : α => positiveLevelIndicator (V y) i)).comp
        (measurable_transitionTrajectoryState_fixed x t))

/-- The complete positive-level charge is measurable.  It is the countable supremum of
its measurable finite-horizon truncations. -/
theorem measurable_trajectoryLevelCharge
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α]
    {m : ℕ} (V : α → ℕ) (x : α) (i : Fin m) :
    Measurable (trajectoryLevelCharge V x i) := by
  unfold trajectoryLevelCharge
  exact Measurable.iSup (fun T =>
    measurable_finiteHorizonLevelCharge V x T i)

/-- The complete charge corresponding to one LeadingOnes score level is measurable.
This is the exact coordinate exposed by the Stage-27-fix-16 index bridge. -/
theorem measurable_leadingOnesScoreIndexedLevelCharge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (i : Fin n) :
    Measurable (fun path : ℕ → BitString n =>
      trajectoryLevelCharge (leadingOnesPotential (n := n)) x
        (leadingOnesScoreToPotentialIndex i) path) := by
  exact measurable_trajectoryLevelCharge
    (leadingOnesPotential (n := n)) x
    (leadingOnesScoreToPotentialIndex i)

/-- Genuine expected complete charge of score level `i`, conditional on one fixed
initial state. -/
noncomputable def leadingOnesFixedInitialScoreLevelChargeExpectation
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) : ENNReal :=
  ∫⁻ path : ℕ → BitString n,
    trajectoryLevelCharge (leadingOnesPotential (n := n)) x
      (leadingOnesScoreToPotentialIndex i) path
  ∂leadingOnesTrajectoryMeasure p hp0 hp1 x

/-- Genuine uniformly initialized expected complete charge of one LeadingOnes score
level.  This is the one-level sample-path quantity that remains to be identified with
first-entry mass times conditional mean residence. -/
noncomputable def leadingOnesUniformScoreLevelChargeExpectation
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) : ENNReal :=
  ((Fintype.card (BitString n) : ENNReal)⁻¹) *
    ∑ x : BitString n,
      leadingOnesFixedInitialScoreLevelChargeExpectation p hp0 hp1 x i

/-- For a fixed initial state, the trajectory `lintegral` of the finite score-indexed
charge sum is the finite sum of the individual charge `lintegral`s. -/
theorem leadingOnesFixedInitial_scoreIndexedLevelCharge_lintegral_sum
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n) :
    (∫⁻ path : ℕ → BitString n,
        ∑ i : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x
            (leadingOnesScoreToPotentialIndex i) path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      ∑ i : Fin n,
        leadingOnesFixedInitialScoreLevelChargeExpectation p hp0 hp1 x i := by
  classical
  unfold leadingOnesFixedInitialScoreLevelChargeExpectation
  simpa using
    (MeasureTheory.lintegral_finsetSum
      (μ := leadingOnesTrajectoryMeasure p hp0 hp1 x)
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun (i : Fin n) (path : ℕ → BitString n) =>
        trajectoryLevelCharge (leadingOnesPotential (n := n)) x
          (leadingOnesScoreToPotentialIndex i) path)
      (by
        intro i _hi
        exact measurable_leadingOnesScoreIndexedLevelCharge x i))

/-- The genuine uniformly initialized first-hitting-time expectation is the finite sum
of the genuine expected complete charges of the individual LeadingOnes score levels.
This is the one-level reduction needed by the remaining exact-runtime bridge. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_sum_scoreLevelChargeExpectation
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0 hp1 =
      ∑ i : Fin n,
        leadingOnesUniformScoreLevelChargeExpectation n p hp0 hp1 i := by
  classical
  rw [leadingOnesUniformFirstHittingTimeExpectation_eq_scoreIndexedLevelChargeExpectation
    n p hp0 hp1]
  simp_rw [leadingOnesFixedInitial_scoreIndexedLevelCharge_lintegral_sum
    p hp0 hp1]
  unfold leadingOnesUniformScoreLevelChargeExpectation
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]

end ECRuntime
