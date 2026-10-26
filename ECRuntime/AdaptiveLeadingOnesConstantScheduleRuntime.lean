import ECRuntime.LeadingOnesOccupationTotalClosure
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-! Stage 261 (P01, new proposed statement). A constant adaptive
schedule is a genuine sample-path model, not merely a residence surrogate.
This theorem uses the already-certified fixed-rate pathwise occupation
identity to validate the adaptive kernel's uniform-runtime semantics. -/

/-- For constant mutation rate `p`, the genuine adaptive-kernel Bellman
runtime average coincides with the exact fixed-rate LeadingOnes formula. -/
theorem proposed_leadingOnesAdaptive_constantSchedule_uniformRuntime
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : Real) (hp0 : 0 < p) (hp1 : p < 1) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      ∑ x : BitString n,
        runtimeSup (leadingOnesAdaptiveTransition (fun _ => p))
          (leadingOnesTarget n) x =
      ENNReal.ofReal
        ((1 / 2 : Real) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹) := by
  have h := leadingOnesUniformFirstHittingTimeExpectation_eq_finiteSum
    (n := n) hp0 hp1
  rw [leadingOnesUniformFirstHittingTimeExpectation_eq_runtimeSup_average] at h
  -- `leadingOnesAdaptiveTransition (fun _ => p)` is definitionally the
  -- constant-rate transition matrix, not a simp rewrite on `runtimeSup`.
  change ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      ∑ x : BitString n,
        runtimeSup (onePlusOneTransition p (leadingOnesReal (n := n)))
          (leadingOnesTarget n) x =
      ENNReal.ofReal
        ((1 / 2 : Real) * ∑ i : Fin n, (p * (1 - p) ^ i.val)⁻¹)
  exact h

end ECRuntime
