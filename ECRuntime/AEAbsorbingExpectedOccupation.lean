import ECRuntime.AbsorbingFirstHittingOccupation
import ECRuntime.LeadingOnesLevelChargeExpectation
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
Stage 288 (P01, research). A generic bridge from almost-sure absorption
of the Markov chain to the exact countable survival law. The underlying
pathwise equality is Stage 284. The remaining measure-theoretic argument
is a substantive obligation; it must not be promoted with an admission.
-/

/-- If the target is pathwise absorbing almost surely, expected first-hitting
time is the sum of the probabilities of being outside the target. This is
valid even if the expected runtime is infinite. -/
theorem proposed_aeAbsorbing_expectedHitting_eq_survivalTsum
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (target : Set α) [DecidablePred (fun y => y ∈ target)]
    (x : α)
    (ha : ∀ᵐ path ∂transitionTrajectoryMeasure P hP x,
      ∀ t : Nat,
        transitionTrajectoryState x path t ∈ target →
        transitionTrajectoryState x path (t + 1) ∈ target) :
    (∫⁻ path : Nat → α,
       transitionTrajectoryFirstHittingTime target x path
       ∂transitionTrajectoryMeasure P hP x) =
      ∑' t : Nat,
        transitionTrajectoryMeasure P hP x
          {path : Nat → α | transitionTrajectoryState x path t ∉ target} := by
  classical
  let μ : Measure (Nat → α) := transitionTrajectoryMeasure P hP x
  let f : Nat → (Nat → α) → ENNReal :=
    fun t path => if transitionTrajectoryState x path t ∈ target then 0 else 1
  have hmeas (t : Nat) : Measurable (f t) := by
    have hg : Measurable
        (fun y : α => if y ∈ target then (0 : ENNReal) else 1) :=
      measurable_of_finite _
    exact hg.comp (measurable_transitionTrajectoryState_fixed x t)
  have hset (t : Nat) : MeasurableSet
      {path : Nat → α | transitionTrajectoryState x path t ∉ target} := by
    have ht : MeasurableSet ({y : α | y ∉ target} : Set α) :=
      ({y : α | y ∉ target} : Set α).to_countable.measurableSet
    exact ht.preimage (measurable_transitionTrajectoryState_fixed x t)
  have hpoint : ∀ᵐ path ∂μ,
      transitionTrajectoryFirstHittingTime target x path =
        ∑' t : Nat, f t path := by
    filter_upwards [ha] with path habsorb
    exact proposed_absorbingPath_firstHittingTime_eq_nonTargetTsum
      target x path habsorb
  calc
    (∫⁻ path : Nat → α,
       transitionTrajectoryFirstHittingTime target x path ∂μ) =
      ∫⁻ path : Nat → α, (∑' t : Nat, f t path) ∂μ :=
        lintegral_congr_ae hpoint
    _ = ∑' t : Nat, (∫⁻ path : Nat → α, f t path ∂μ) := by
      rw [MeasureTheory.lintegral_tsum (fun t => (hmeas t).aemeasurable)]
    _ = ∑' t : Nat,
        μ {path : Nat → α | transitionTrajectoryState x path t ∉ target} := by
      apply tsum_congr
      intro t
      rw [← MeasureTheory.lintegral_indicator_fun_one (hset t)]
      apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (fun path => by
        change (if transitionTrajectoryState x path t ∈ target
          then (0 : ENNReal) else 1) =
          ({path : Nat → α | transitionTrajectoryState x path t ∉ target} :
            Set (Nat → α)).indicator (fun _ => (1 : ENNReal)) path
        by_cases ht : transitionTrajectoryState x path t ∈ target <;>
          simp [ht])

end ECRuntime
