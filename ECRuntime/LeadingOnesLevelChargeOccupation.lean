import ECRuntime.LeadingOnesExactRuntimeClosure
import Mathlib

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 19 fix 2: score-level charge as total occupation mass

Stage 27 fix 18 is compiler verified warning/error-free.  The first fix-19 compiler run
reported two local elaboration failures. Fix 19 fix 1 removed both original failures, but the
finite-horizon monotonicity repair used the wrong addition-side congruence theorem. Fix 19 fix 2
changes only that theorem application and does not change any theorem statement or mathematical
argument.  The genuine uniformly
initialized runtime is now reduced to one expected complete charge for each LeadingOnes
score level, and the exact first-entry mass is available as a finite uniform average of
fixed-initial countable entry masses.

The remaining bridge can be made smaller by avoiding conditional expectations at a
random entry time.  For one fixed initial state and one score level, the complete charge
is simply the monotone limit of its finite-horizon visit counts.  Monotone convergence
therefore identifies its expectation with the monotone limit of the corresponding
finite sums of exact-time occupation probabilities.

This module makes that occupation representation explicit.  It also packages the
algebra showing that a fixed-initial renewal identity

  total occupation mass = eventual exact-entry mass * visited-level mean residence

is already sufficient to close the uniform one-level bridge and hence the full exact
runtime theorem.  No independence or stopping-time conditional law is assumed.
-/

/-- Finite-horizon level charge is monotone when the horizon is extended by one step. -/
theorem finiteHorizonLevelCharge_le_succ
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (T : ℕ) (i : Fin m) :
    finiteHorizonLevelCharge V x path T i ≤
      finiteHorizonLevelCharge V x path (T + 1) i := by
  unfold finiteHorizonLevelCharge
  rw [Finset.sum_range_succ]
  calc
    (∑ t ∈ Finset.range T,
        positiveLevelIndicator (V (transitionTrajectoryState x path t)) i) =
        (∑ t ∈ Finset.range T,
          positiveLevelIndicator (V (transitionTrajectoryState x path t)) i) + 0 := by
      simp
    _ ≤ (∑ t ∈ Finset.range T,
          positiveLevelIndicator (V (transitionTrajectoryState x path t)) i) +
        positiveLevelIndicator (V (transitionTrajectoryState x path T)) i := by
      exact add_le_add_right
        (show (0 : ENNReal) ≤
          positiveLevelIndicator (V (transitionTrajectoryState x path T)) i from bot_le) _

/-- The finite-horizon charge observables form a monotone family in the horizon. -/
theorem finiteHorizonLevelCharge_monotone
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (i : Fin m) :
    Monotone (fun T : ℕ => fun path : ℕ → α =>
      finiteHorizonLevelCharge V x path T i) := by
  apply monotone_nat_of_le_succ
  intro T path
  exact finiteHorizonLevelCharge_le_succ V x path T i

/-- Infinite-path event that the absolute trajectory state at time `t` has exactly
LeadingOnes score `i`. -/
def leadingOnesScoreLevelAtTimeSet
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    Set (ℕ → BitString n) :=
  {path | leadingOnes (transitionTrajectoryState x path t) = i.val}

/-- Exact-time score-level occupation is measurable on the genuine trajectory space. -/
theorem measurableSet_leadingOnesScoreLevelAtTimeSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (i : Fin n) (t : ℕ) :
    MeasurableSet (leadingOnesScoreLevelAtTimeSet x i t) := by
  have hlevel :
      MeasurableSet
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) :=
    ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)).to_countable.measurableSet
  simpa [leadingOnesScoreLevelAtTimeSet] using
    hlevel.preimage (measurable_transitionTrajectoryState_fixed x t)

/-- Fixed-initial probability mass of occupying score level `i` at absolute time `t`. -/
noncomputable def leadingOnesFixedInitialScoreLevelOccupationMass
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) : ENNReal :=
  leadingOnesTrajectoryMeasure p hp0 hp1 x
    (leadingOnesScoreLevelAtTimeSet x i t)

/-- The one-hot score-level integrand at a fixed time integrates to the corresponding
exact-time occupation mass. -/
theorem leadingOnes_scoreLevelIndicator_lintegral_eq_occupationMass
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    (∫⁻ path : ℕ → BitString n,
        positiveLevelIndicator
          (leadingOnesPotential
            (transitionTrajectoryState x path t))
          (leadingOnesScoreToPotentialIndex i)
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      leadingOnesFixedInitialScoreLevelOccupationMass
        p hp0 hp1 x i t := by
  unfold leadingOnesFixedInitialScoreLevelOccupationMass
  have hset := measurableSet_leadingOnesScoreLevelAtTimeSet x i t
  rw [← MeasureTheory.lintegral_indicator_fun_one hset]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun path => by
    change
      positiveLevelIndicator
          (leadingOnesPotential (transitionTrajectoryState x path t))
          (leadingOnesScoreToPotentialIndex i) =
        (leadingOnesScoreLevelAtTimeSet x i t).indicator
          (fun _ => (1 : ENNReal)) path
    rw [positiveLevelIndicator_leadingOnesPotential_scoreIndex]
    by_cases hlevel : leadingOnes (transitionTrajectoryState x path t) = i.val
    · simp [leadingOnesScoreLevelAtTimeSet, hlevel]
    · simp [leadingOnesScoreLevelAtTimeSet, hlevel])

/-- The expected finite-horizon score-level charge is the finite sum of the exact-time
occupation masses in that horizon. -/
theorem leadingOnesFixedInitial_finiteHorizonScoreLevelCharge_lintegral
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (T : ℕ) :
    (∫⁻ path : ℕ → BitString n,
        finiteHorizonLevelCharge (leadingOnesPotential (n := n)) x path T
          (leadingOnesScoreToPotentialIndex i)
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      ∑ t ∈ Finset.range T,
        leadingOnesFixedInitialScoreLevelOccupationMass
          p hp0 hp1 x i t := by
  unfold finiteHorizonLevelCharge
  calc
    (∫⁻ path : ℕ → BitString n,
        ∑ t ∈ Finset.range T,
          positiveLevelIndicator
            (leadingOnesPotential
              (transitionTrajectoryState x path t))
            (leadingOnesScoreToPotentialIndex i)
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
        ∑ t ∈ Finset.range T,
          ∫⁻ path : ℕ → BitString n,
            positiveLevelIndicator
              (leadingOnesPotential
                (transitionTrajectoryState x path t))
              (leadingOnesScoreToPotentialIndex i)
          ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
      simpa using
        (MeasureTheory.lintegral_finsetSum
          (μ := leadingOnesTrajectoryMeasure p hp0 hp1 x)
          (s := Finset.range T)
          (f := fun (t : ℕ) (path : ℕ → BitString n) =>
            positiveLevelIndicator
              (leadingOnesPotential
                (transitionTrajectoryState x path t))
              (leadingOnesScoreToPotentialIndex i))
          (by
            intro t _ht
            exact
              (measurable_of_finite
                (fun y : BitString n =>
                  positiveLevelIndicator (leadingOnesPotential y)
                    (leadingOnesScoreToPotentialIndex i))).comp
                (measurable_transitionTrajectoryState_fixed x t)))
    _ = ∑ t ∈ Finset.range T,
        leadingOnesFixedInitialScoreLevelOccupationMass
          p hp0 hp1 x i t := by
      apply Finset.sum_congr rfl
      intro t _ht
      exact leadingOnes_scoreLevelIndicator_lintegral_eq_occupationMass
        p hp0 hp1 x i t

/-- Monotone-limit total of the exact-time occupation masses from one fixed initial
state.  This scalar is the renewal quantity that remains to be evaluated. -/
noncomputable def leadingOnesFixedInitialScoreLevelOccupationTotal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) : ENNReal :=
  ⨆ T : ℕ,
    ∑ t ∈ Finset.range T,
      leadingOnesFixedInitialScoreLevelOccupationMass
        p hp0 hp1 x i t

/-- The genuine expected complete score-level charge is exactly the total occupation
mass.  This is monotone convergence applied to the finite-horizon visit counts. -/
theorem leadingOnesFixedInitialScoreLevelChargeExpectation_eq_occupationTotal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) :
    leadingOnesFixedInitialScoreLevelChargeExpectation
        p hp0 hp1 x i =
      leadingOnesFixedInitialScoreLevelOccupationTotal
        p hp0 hp1 x i := by
  unfold leadingOnesFixedInitialScoreLevelChargeExpectation
  unfold leadingOnesFixedInitialScoreLevelOccupationTotal
  unfold trajectoryLevelCharge
  rw [MeasureTheory.lintegral_iSup
    (fun T => measurable_finiteHorizonLevelCharge
      (leadingOnesPotential (n := n)) x T
      (leadingOnesScoreToPotentialIndex i))
    (finiteHorizonLevelCharge_monotone
      (leadingOnesPotential (n := n)) x
      (leadingOnesScoreToPotentialIndex i))]
  simp_rw [leadingOnesFixedInitial_finiteHorizonScoreLevelCharge_lintegral
    p hp0 hp1 x i]

/-- Uniform expected charge is the finite uniform average of the fixed-initial total
occupation masses. -/
theorem leadingOnesUniformScoreLevelChargeExpectation_eq_occupationTotal_average
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (i : Fin n) :
    leadingOnesUniformScoreLevelChargeExpectation n p hp0 hp1 i =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          leadingOnesFixedInitialScoreLevelOccupationTotal
            p hp0 hp1 x i := by
  unfold leadingOnesUniformScoreLevelChargeExpectation
  apply congrArg
    (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro x _hx
  exact leadingOnesFixedInitialScoreLevelChargeExpectation_eq_occupationTotal
    p hp0 hp1 x i

/-- A fixed-initial renewal identity is sufficient for the missing uniform one-level
charge/residence bridge.  This reduces the remaining probabilistic proof to a scalar
statement for each deterministic initial state. -/
theorem leadingOnesUniformScoreLevelChargeExpectation_eq_residenceContribution_of_fixedOccupationBridge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n)
    (hfixed : ∀ x : BitString n,
      leadingOnesFixedInitialScoreLevelOccupationTotal
          p hp0.le hp1.le x i =
        leadingOnesFixedInitialEventualExactEntryMass p i x *
          ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i)) :
    leadingOnesUniformScoreLevelChargeExpectation
        n p hp0.le hp1.le i =
      leadingOnesUniformLevelResidenceContribution p i := by
  rw [leadingOnesUniformScoreLevelChargeExpectation_eq_occupationTotal_average
    p hp0.le hp1.le i]
  simp_rw [hfixed]
  rw [← Finset.sum_mul]
  rw [← mul_assoc]
  rw [← leadingOnesUniformLevelVisitMass_eq_uniform_average_fixedInitialExact
    hp0.le hp1.le i]
  exact (leadingOnesUniformLevelResidenceContribution_eq_visitMass_mul_mean p i).symm

/-- Consequently, proving the fixed-initial occupation renewal identity for every score
level and every initial string closes the exact finite-sum runtime theorem immediately. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum_of_fixedOccupationBridge
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hfixed : ∀ (i : Fin n) (x : BitString n),
      leadingOnesFixedInitialScoreLevelOccupationTotal
          p hp0.le hp1.le x i =
        leadingOnesFixedInitialEventualExactEntryMass p i x *
          ENNReal.ofReal (leadingOnesVisitedLevelMeanResidence p i)) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0.le hp1.le =
      ENNReal.ofReal
        ((1 / 2 : ℝ) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹) := by
  apply leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum_of_scoreLevelBridge
    hp0 hp1
  intro i
  exact
    leadingOnesUniformScoreLevelChargeExpectation_eq_residenceContribution_of_fixedOccupationBridge
      hp0 hp1 i (hfixed i)

end ECRuntime
