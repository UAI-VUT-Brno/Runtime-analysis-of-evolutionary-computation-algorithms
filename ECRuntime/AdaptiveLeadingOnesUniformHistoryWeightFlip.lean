import ECRuntime.AdaptiveLeadingOnesFiniteTrajectoryFlip
import ECRuntime.LeadingOnesFirstCrossingSymmetry
import Mathlib

namespace ECRuntime

/-!
Stage 218 (NEW, awaiting statement approval): transfer the certified
pre-crossing finite-trajectory symmetry to complete uniformly initialized
finite histories. The initial uniform weight is independent of the initial
state and is therefore preserved by the coordinate-flip involution.

The stage does NOT assume that rates at different LeadingOnes levels are
equal, nor does it claim that the process eventually crosses a boundary.
-/

/-- Uniform-start probability weight of a finite history under a
fitness-dependent mutation-rate schedule. -/
noncomputable def leadingOnesAdaptiveUniformFiniteHistoryWeight
    {n t : Nat} (rate : Nat -> Real) (h : LeadingOnesFiniteHistory n t) : Real :=
  ((Fintype.card (BitString n) : Real)⁻¹) *
    finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t h.1 h.2

/-- Uniform-start history weight is invariant under coordinate flip on
pre-crossing histories, for any (possibly nonconstant) rate schedule. -/
theorem proposed_leadingOnesAdaptive_uniformHistoryWeight_flip
    {n t : Nat} (rate : Nat -> Real) (i : Fin n)
    (h : LeadingOnesFiniteHistory n t)
    (hpre : leadingOnesHistoryPreCrossing i h) :
    leadingOnesAdaptiveUniformFiniteHistoryWeight rate
        (leadingOnesFiniteHistoryFlip i h) =
      leadingOnesAdaptiveUniformFiniteHistoryWeight rate h := by
  rcases h with ⟨x, path⟩
  change leadingOnesPreCrossing i t x path at hpre
  unfold leadingOnesAdaptiveUniformFiniteHistoryWeight
  change
    ((Fintype.card (BitString n) : Real)⁻¹) *
      finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t
        (leadingOnesCoordinateFlip i x)
        (leadingOnesFiniteTrajectoryFlip i path) =
    ((Fintype.card (BitString n) : Real)⁻¹) *
      finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t x path
  rw [proposed_leadingOnesAdaptive_finiteTrajectory_flipWeight
    rate i t x path hpre]

end ECRuntime
