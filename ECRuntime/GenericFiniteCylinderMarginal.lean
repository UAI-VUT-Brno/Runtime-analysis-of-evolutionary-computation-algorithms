import ECRuntime.FiniteMarginalIdentification
import Mathlib

open MeasureTheory
namespace ECRuntime

/-! P01. Exact finite-cylinder marginal identification. This is a genuinely
measure-theoretic statement, but it only concerns finite-coordinate events;
it does not supply strong Markov independence at a first-entry time. -/

/-- The infinite Markov trajectory measure and the explicit finite-path
measure agree on each measurable event depending on a fixed finite tail. -/
theorem proposed_transitionTrajectoryMeasure_finiteCylinder_eq_finiteMeasure
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (x : α) (t : Nat)
    (event : Set (FiniteTrajectory α t)) (hevent : MeasurableSet event) :
    transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail t ⁻¹' event) =
        finiteTrajectoryMeasure P hP t x event := by
  rw [← Measure.map_apply
    (measurable_transitionTrajectoryTail (α := α) t) hevent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]

end ECRuntime
