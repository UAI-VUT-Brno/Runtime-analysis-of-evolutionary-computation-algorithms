import ECRuntime.UniformFixedTarget
import ECRuntime.UniformMutationExact
import ECRuntime.LevelExitTrajectory
import ECRuntime.MultiplicativeDriftTail
import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.GeometricTail
import Mathlib

open scoped ENNReal
namespace ECRuntime

/-! Stage 123 promotion candidate. Direct geometric-tail refinement of the verified
Stage 118 finite-survival mechanism, for arbitrary attainable superlevel sets.
The theorem header is approved; proof development is authorized. -/

/-- Below the threshold, elitist selection reaches the threshold exactly
when the uniformly generated offspring lies in the superlevel set. -/
private theorem stage123_uniformSelection_iff
    {n : Nat} (fitness : BitString n → Real) (threshold : Real)
    (x : BitString n) (hx : x ∉ candidateFitnessThreshold fitness threshold)
    (mask : MutationMask n) :
    selectedAfterMask fitness x mask ∈ candidateFitnessThreshold fitness threshold ↔
    mutateWithMask x mask ∈ candidateFitnessThreshold fitness threshold := by
  by_cases hacc : Accepts fitness x (mutateWithMask x mask)
  · simp [selectedAfterMask, elitistSelect_of_accepts _ _ _ hacc]
  · have hy : mutateWithMask x mask ∉ candidateFitnessThreshold fitness threshold := by
      intro hth
      have hbelow : fitness x < threshold := lt_of_not_ge hx
      have habove : threshold ≤ fitness (mutateWithMask x mask) := hth
      exact hacc (le_trans hbelow.le habove)
    simp [selectedAfterMask, elitistSelect_of_rejects _ _ _ hacc, hx, hy]

/-- The exact probability of reaching an attainable threshold in one step
under uniform mutation is the target cardinality divided by `2^n`. -/
private theorem stage123_thresholdSuccessMass
    {n : Nat} (fitness : BitString n → Real) (threshold : Real)
    (x : BitString n) (hx : x ∉ candidateFitnessThreshold fitness threshold) :
    finiteEventMass (onePlusOneTransition (1 / 2 : Real) fitness x)
      (fun y => y ∈ candidateFitnessThreshold fitness threshold) =
    (candidateFitnessThresholdCount fitness threshold : Real) /
      (2 : Real) ^ n := by
  classical
  have hevents :
      (fun mask : MutationMask n =>
        selectedAfterMask fitness x mask ∈ candidateFitnessThreshold fitness threshold) =
      (fun mask : MutationMask n =>
        mutateWithMask x mask ∈ candidateFitnessThreshold fitness threshold) := by
    funext mask
    exact propext (stage123_uniformSelection_iff fitness threshold x hx mask)
  unfold onePlusOneTransition
  rw [finiteEventMass_pushforwardWeight, hevents]
  have huniform :
      pushforwardWeight
        (mutationMaskWeight (n := n) (1 / 2 : Real))
        (mutateWithMask x) = fun _ => (1 : Real) / (2 : Real) ^ n := by
    funext y
    exact halfMutation_uniformOffspring x y
  rw [← finiteEventMass_pushforwardWeight, huniform]
  let s : Finset (BitString n) := Finset.univ.filter
    (fun y => y ∈ candidateFitnessThreshold fitness threshold)
  have hsum :
      finiteEventMass (fun _ : BitString n => (1 : Real) / (2 : Real) ^ n)
        (fun y => y ∈ candidateFitnessThreshold fitness threshold) =
      ∑ y ∈ s, (1 : Real) / (2 : Real) ^ n := by
    unfold finiteEventMass
    calc
      (∑ y : BitString n,
        ({y | y ∈ candidateFitnessThreshold fitness threshold} :
          Set (BitString n)).indicator
            (fun _ => (1 : Real) / (2 : Real) ^ n) y) =
        ∑ y : BitString n,
          if y ∈ s then (1 : Real) / (2 : Real) ^ n else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : y ∈ candidateFitnessThreshold fitness threshold
            · have hm : y ∈ ({z : BitString n |
                z ∈ candidateFitnessThreshold fitness threshold} :
                Set (BitString n)) := hy
              rw [Set.indicator_of_mem hm (fun _ => (1 : Real) / (2 : Real) ^ n)]
              simp [s, hy]
            · have hm : y ∉ ({z : BitString n |
                z ∈ candidateFitnessThreshold fitness threshold} :
                Set (BitString n)) := hy
              rw [Set.indicator_of_notMem hm (fun _ => (1 : Real) / (2 : Real) ^ n)]
              simp [s, hy]
      _ = ∑ y ∈ s, (1 : Real) / (2 : Real) ^ n :=
        Finset.sum_ite_mem_eq _ _
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  change (candidateFitnessThresholdCount fitness threshold : Real) *
    ((1 : Real) / (2 : Real) ^ n) = _
  ring


/-- Under independent bit mutation of rate 1/2 and elitist selection,
from below an attainable fitness threshold the first-threshold-hitting
runtime has an exact geometric survival tail. -/
theorem proposed_uniformThreshold_geometricTail
    {n : Nat} (fitness : BitString n → Real) (threshold : Real)
    (hcount : 0 < candidateFitnessThresholdCount fitness threshold)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : x ∉ candidateFitnessThreshold fitness threshold)
    (t : Nat) :
    runtimeTailMass
      (transitionTrajectoryMeasure
        (onePlusOneTransition (1 / 2 : Real) fitness)
        (onePlusOneTransition_stochastic (by norm_num) (by norm_num) fitness) x)
      (transitionTrajectoryFirstHittingTime
        (candidateFitnessThreshold fitness threshold) x) (t : ENNReal) =
      ENNReal.ofReal
        ((1 - (candidateFitnessThresholdCount fitness threshold : Real) /
          (2 : Real) ^ n) ^ t) := by
  classical
  let target : Set (BitString n) := candidateFitnessThreshold fitness threshold
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition (1 / 2 : Real) fitness
  let q : Real := (candidateFitnessThresholdCount fitness threshold : Real) /
    (2 : Real) ^ n
  have hP : IsStochastic P :=
    onePlusOneTransition_stochastic (by norm_num) (by norm_num) fitness
  have hexit : ∀ y : BitString n, y ∈ targetᶜ →
      finiteEventMass (P y) (fun z => z ∉ targetᶜ) = q := by
    intro y hy
    have hy' : y ∉ candidateFitnessThreshold fitness threshold := hy
    have hevent : (fun z : BitString n => z ∉ targetᶜ) =
        (fun z : BitString n => z ∈ target) := by
      funext z
      apply propext
      simp
    rw [hevent]
    exact stage123_thresholdSuccessMass fitness threshold y hy'
  have hsurvival : finiteLevelSurvival P targetᶜ t x = (1 - q) ^ t := by
    by_cases hz : candidateFitnessThresholdCount fitness threshold = 0
    · exact (Nat.ne_of_gt hcount hz).elim
    · apply finiteLevelSurvival_eq_geometric_of_exact_exit_mass
        P targetᶜ hP q hexit t x
      exact hx
  have htarget : targetᶜᶜ = target := by
    ext z
    simp
  have hhit := transitionTrajectoryFirstHittingTime_congr_set
    targetᶜᶜ target htarget x
  have htail := transitionTrajectoryLevelExit_tailMass_eq_finiteLevelSurvival
    P targetᶜ hP x t
  rw [hhit, hsurvival] at htail
  exact htail

end ECRuntime
