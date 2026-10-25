import ECRuntime.GenericFiniteCylinderMarginal
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

namespace ECRuntime

/-! P01: generic one-step finite-cylinder decomposition in ENNReal.
This isolates the transport of finite Markov mass to a genuine cylinder
without conflating it with a Markov property at an unbounded stopping time.
-/

/-- Any finite initial time cylinder is governed by its finite joint law. -/
theorem proposed_genericMarkov_firstEntryFiniteCylinder_eq_finite
    {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (P : TransitionMatrix α)
    (hP : IsStochastic P) (x : α) (t : Nat)
    (event : Set (FiniteTrajectory α (t + 1))) (hevent : MeasurableSet event) :
    transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail (t + 1) ⁻¹' event) =
    finiteTrajectoryMeasure P hP (t + 1) x event := by
  exact proposed_transitionTrajectoryMeasure_finiteCylinder_eq_finiteMeasure
    P hP x (t + 1) event hevent

end ECRuntime
