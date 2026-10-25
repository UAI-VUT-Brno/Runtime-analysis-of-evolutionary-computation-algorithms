import ECRuntime.LeadingOnesBoundaryEventualCrossing
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
Stage 226 (NEW, pending approval): generic runtime-to-almost-sure crossing
bridge for the adaptive LeadingOnes kernel.  This is a conditional theorem:
it DOES NOT assert that adaptive expected hitting times are finite.
The pending Stage 225 needs a separate finite runtime certificate.
-/

/-- A finite adaptive unrestricted hitting time implies probability-one
boundary crossing, independently of how the rates depend on the score. -/
theorem proposed_leadingOnesAdaptive_boundaryAE_of_runtimeFinite
    {n : Nat} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat -> Real)
    (hrate : ∀ j : Nat, j <= n -> 0 <= rate j ∧ rate j <= 1)
    (i : Fin n) (x : BitString n)
    (hfinite : runtimeSup (leadingOnesAdaptiveTransition rate)
      (potentialTarget (leadingOnesBoundaryPotential i)) x ≠ ⊤) :
    transitionTrajectoryMeasure
      (leadingOnesAdaptiveTransition rate)
      (proposed_leadingOnesAdaptive_transition_stochastic rate hrate)
      x (leadingOnesEventuallyCrossesBoundarySet i x) = 1 := by
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  have hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  have hlintegral :
      (∫⁻ path : Nat -> BitString n,
        transitionTrajectoryFirstHittingTime
          (potentialTarget (leadingOnesBoundaryPotential i)) x path
        ∂transitionTrajectoryMeasure P hP x) ≠ ⊤ := by
    rw [transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
      P (potentialTarget (leadingOnesBoundaryPotential i)) hP x]
    exact hfinite
  have hae : ∀ᵐ path ∂transitionTrajectoryMeasure P hP x,
      transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesBoundaryPotential i)) x path < ⊤ := by
    exact ae_lt_top
      (measurable_transitionTrajectoryFirstHittingTime
        (potentialTarget (leadingOnesBoundaryPotential i)) x)
      hlintegral
  rw [ae_iff] at hae
  have hcomp :
      transitionTrajectoryMeasure P hP x
        (leadingOnesEventuallyCrossesBoundarySet i x)ᶜ = 0 := by
    have hset :
        (leadingOnesEventuallyCrossesBoundarySet i x)ᶜ =
          {path | transitionTrajectoryFirstHittingTime
            (potentialTarget (leadingOnesBoundaryPotential i)) x path = ⊤} := by
      ext path
      simp [leadingOnesEventuallyCrossesBoundarySet, lt_top_iff_ne_top]
    rw [hset]
    simpa only [not_lt, top_le_iff] using hae
  have hmeas := measurableSet_leadingOnesEventuallyCrossesBoundarySet i x
  have hsum := measure_add_measure_compl
    (μ := transitionTrajectoryMeasure P hP x) hmeas
  rw [hcomp] at hsum
  simpa [P] using hsum

end ECRuntime
