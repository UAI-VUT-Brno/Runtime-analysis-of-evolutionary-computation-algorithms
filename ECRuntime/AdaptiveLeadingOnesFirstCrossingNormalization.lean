import ECRuntime.AdaptiveLeadingOnesFirstCrossingTotalMass
import ECRuntime.AdaptiveLeadingOnesFirstCrossingFixedInitialAverage
import ECRuntime.AdaptiveLeadingOnesFirstCrossingNonneg
import ECRuntime.LeadingOnesBoundaryEventualCrossing
import ECRuntime.AdaptiveLeadingOnesBoundaryEventualCrossing
import ECRuntime.LeadingOnesExactStayBranch
import ECRuntime.LeadingOnesFirstCrossingMeasure
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
Stage 233: adaptive, uniformly initialized first-crossing normalization.
This proof uses the already certified almost-sure adaptive boundary crossing
(Stage 225), finite-state trajectory marginal identification, finite-time
uniform averaging (Stage 222), and countable exact/skip parity (Stage 220).
No independence of unvisited suffix coordinates is assumed.
-/

/-- The adaptive finite first-crossing history sum is the probability of the
corresponding cylinder event under the adaptive stochastic kernel. -/
private theorem adaptiveFirstCrossing_cylinder_mass
    {n t : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (x : BitString n) :
    transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        (leadingOnesTrajectoryFirstCrossingSet i x t) =
      ENNReal.ofReal
        (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x) := by
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  have htail : Measurable (transitionTrajectoryTail (α := BitString n) t) :=
    measurable_transitionTrajectoryTail (α := BitString n) t
  have hEvent : MeasurableSet (leadingOnesFiniteFirstCrossingSet i x t) :=
    measurableSet_leadingOnesFiniteFirstCrossingSet i x
  unfold leadingOnesTrajectoryFirstCrossingSet
  change transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail t ⁻¹' leadingOnesFiniteFirstCrossingSet i x t) = _
  rw [← Measure.map_apply htail hEvent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]
  rw [finiteTrajectoryMeasure_apply_eq_ofReal_setWeight
    P hP t x (leadingOnesFiniteFirstCrossingSet i x t)]
  rfl

/-- Statewise normalized first-crossing mass is a consequence of the certified
adaptive almost-sure boundary hitting theorem and disjoint cylinders. -/
private theorem adaptiveFirstCrossing_fixedInitial_tsum_one
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) (x : BitString n) :
    (∑' t : Nat, ENNReal.ofReal
      (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x)) = 1 := by
  have hrate' : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1 :=
    fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩
  calc
    (∑' t : Nat, ENNReal.ofReal
      (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x)) =
      transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate') x
        (leadingOnesEventuallyCrossesBoundarySet i x) := by
      symm
      rw [leadingOnesEventuallyCrossesBoundarySet_eq_iUnion_firstCrossingSet i x]
      rw [measure_iUnion
        (pairwise_disjoint_leadingOnesTrajectoryFirstCrossingSet i x)
        (fun t => measurableSet_leadingOnesTrajectoryFirstCrossingSet i x t)]
      apply tsum_congr
      intro t
      exact adaptiveFirstCrossing_cylinder_mass rate hrate' i x
    _ = 1 := proposed_leadingOnesAdaptive_eventuallyCrossesBoundary_ae
      rate hrate i x

/-- Fixed-time adaptive first-crossing mass has the same finite uniform
averaging and `ENNReal.ofReal` conversion as the fixed-rate special case. -/
private theorem adaptiveFirstCrossing_ofReal_uniformAverage
    {n t : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) :
    ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingTotalMass (t := t) rate i) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          ENNReal.ofReal
            (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x) := by
  classical
  rw [proposed_leadingOnesAdaptive_firstCrossingTotal_eq_uniformAverage rate i]
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  have hcardNat : 0 < Fintype.card (BitString n) := Fintype.card_pos
  have hcardReal : 0 < (Fintype.card (BitString n) : Real) := by
    exact_mod_cast hcardNat
  have hnonneg :
      ∀ x ∈ (Finset.univ : Finset (BitString n)),
        0 ≤ leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x := by
    intro x _hx
    exact proposed_leadingOnesAdaptive_fixedInitialFirstCrossingMass_nonneg
      rate hrate i x
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcardReal.le)]
  rw [ENNReal.ofReal_inv_of_pos hcardReal]
  rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
  simp

/-- The sum of the two aggregate crossing branches equals the countable
sum of their finite-time real total masses. This only uses parity, so no
positivity assumption on the mutation-rate schedule is needed. -/
private theorem adaptiveFirstCrossing_total_eq_tsum_finite
    {n : Nat} (rate : Nat → Real) (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingTotalMass rate i =
      ∑' t : Nat,
        ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingTotalMass (t := t) rate i) := by
  calc
    leadingOnesAdaptiveEventualFirstCrossingTotalMass rate i =
      (2 : ENNReal) * leadingOnesAdaptiveEventualFirstCrossingExactMass rate i :=
        proposed_leadingOnesAdaptive_eventualFirstCrossingTotal_eq_twiceExact rate i
    _ = (2 : ENNReal) *
        (∑' t : Nat,
          ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i)) := rfl
    _ = ∑' t : Nat,
        (2 : ENNReal) *
          ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i) := by
      symm
      exact ENNReal.tsum_mul_left
    _ = ∑' t : Nat,
        ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingTotalMass (t := t) rate i) := by
      apply tsum_congr
      intro t
      have hreal :
          leadingOnesAdaptiveFirstCrossingTotalMass (t := t) rate i =
            (2 : Real) * leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i := by
        unfold leadingOnesAdaptiveFirstCrossingTotalMass
        rw [← proposed_leadingOnesAdaptive_firstCrossingExactMass_eq_skipMass
          (t := t) rate i]
        ring
      rw [hreal, ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : Real))]
      norm_num

/-- Under a strictly interior schedule, every first-crossing branch accounts
for a probability-one event in total. -/
theorem proposed_leadingOnesAdaptive_firstCrossingTotal_eq_one
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    leadingOnesAdaptiveEventualFirstCrossingTotalMass rate i = 1 := by
  classical
  letI : MeasurableSpace (BitString n) := ⊤
  letI : MeasurableSingletonClass (BitString n) :=
    ⟨fun _ => by simp⟩
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  have hrate' : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1 :=
    fun j hj => ⟨(hrate j hj).1.le, (hrate j hj).2.le⟩
  calc
    leadingOnesAdaptiveEventualFirstCrossingTotalMass rate i =
        ∑' t : Nat,
          ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingTotalMass (t := t) rate i) :=
      adaptiveFirstCrossing_total_eq_tsum_finite rate i
    _ = ∑' t : Nat,
          ((Fintype.card (BitString n) : ENNReal)⁻¹) *
            ∑ x : BitString n,
              ENNReal.ofReal
                (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x) := by
      apply tsum_congr
      intro t
      exact adaptiveFirstCrossing_ofReal_uniformAverage rate hrate' i
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑' t : Nat,
          ∑ x : BitString n,
            ENNReal.ofReal
              (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x)) := by
      exact ENNReal.tsum_mul_left
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          ∑' t : Nat,
            ENNReal.ofReal
              (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x)) := by
      congr 1
      calc
        (∑' t : Nat, ∑ x : BitString n,
            ENNReal.ofReal
              (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x)) =
          ∑' t : Nat, ∑' x : BitString n,
            ENNReal.ofReal
              (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x) := by
          apply tsum_congr
          intro t
          rw [tsum_fintype]
        _ = ∑' x : BitString n, ∑' t : Nat,
            ENNReal.ofReal
              (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x) := by
          exact ENNReal.tsum_comm
        _ = ∑ x : BitString n, ∑' t : Nat,
            ENNReal.ofReal
              (leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x) := by
          rw [tsum_fintype]
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n, (1 : ENNReal) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      exact adaptiveFirstCrossing_fixedInitial_tsum_one rate hrate i x
    _ = 1 := by
      have hcard : Fintype.card (BitString n) ≠ 0 := Fintype.card_ne_zero
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul, mul_one]
      apply ENNReal.inv_mul_cancel
      · exact_mod_cast hcard
      · exact ENNReal.natCast_ne_top _

end ECRuntime
