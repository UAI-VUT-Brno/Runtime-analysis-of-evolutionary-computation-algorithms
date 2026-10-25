import ECRuntime.LeadingOnesSymmetry
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 216 (NEW, awaiting statement approval): coordinate-flip conjugacy of
fitness-dependent LeadingOnes mutation. Fix a coordinate `i`. Before the
LeadingOnes score reaches `i`, flipping that coordinate does not affect the
score, hence does not change the scheduled rate. The fixed-rate symmetry
can consequently be applied at that parent state.

This is a *one-step, pre-crossing* statement. It does not itself prove equal
first-crossing masses, eventual crossing, or global policy optimality.
-/

/-- Prior to reaching coordinate `i`, the adaptive LeadingOnes transition
kernel is conjugate under flipping that coordinate, for any rate schedule. -/
theorem proposed_leadingOnesAdaptive_coordinateFlip_kernel
    {n : Nat} (rate : Nat → Real) (i : Fin n)
    (parent next : BitString n)
    (hbelow : leadingOnes parent < i.val) :
    leadingOnesAdaptiveTransition rate
      (leadingOnesCoordinateFlip i parent)
      (leadingOnesCoordinateFlip i next) =
      leadingOnesAdaptiveTransition rate parent next := by
  change
    onePlusOneTransition
      (rate (leadingOnes (leadingOnesCoordinateFlip i parent)))
      leadingOnesReal
      (leadingOnesCoordinateFlip i parent)
      (leadingOnesCoordinateFlip i next) =
    onePlusOneTransition (rate (leadingOnes parent))
      leadingOnesReal parent next
  rw [leadingOnes_coordinateFlip_eq_of_lt parent i hbelow]
  exact onePlusOneTransition_leadingOnes_coordinateFlip
    (rate (leadingOnes parent)) parent next i hbelow

end ECRuntime
