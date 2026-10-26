import ECRuntime.LeadingOnesFirstCrossingSymmetry
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import Mathlib

namespace ECRuntime

/-!
Stage 217 (NEW, awaiting statement approval): a finite-history extension
of the adaptive coordinate-flip symmetry. The candidate is self-contained
and depends only on already certified source; after Stage 216 is promoted,
its one-step subproof can be replaced by the Stage 216 lemma.

This is the ingredient for a weight-preserving involution on adaptive
pre-crossing histories, not yet a theorem about visitation probability.
-/

/-- Under any fitness-dependent rate schedule, flipping coordinate `i`
through a whole history preserves its weight whenever every transition
parent remains strictly below `i`. -/
theorem proposed_leadingOnesAdaptive_finiteTrajectory_flipWeight
    {n : Nat} (rate : Nat → Real) (i : Fin n) :
    ∀ (t : Nat) (x : BitString n)
      (path : FiniteTrajectory (BitString n) t),
      leadingOnesPreCrossing i t x path →
      finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t
          (leadingOnesCoordinateFlip i x)
          (leadingOnesFiniteTrajectoryFlip i path) =
        finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t x path := by
  intro t
  induction t with
  | zero =>
      intro x path _h
      rfl
  | succ t ih =>
      intro x path hpre
      rcases hpre with ⟨hx, htail⟩
      change
        leadingOnesAdaptiveTransition rate
            (leadingOnesCoordinateFlip i x)
            (leadingOnesCoordinateFlip i (path 0)) *
          finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t
            (leadingOnesCoordinateFlip i (path 0))
            (Fin.tail (leadingOnesFiniteTrajectoryFlip i path)) =
        leadingOnesAdaptiveTransition rate x (path 0) *
          finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t
            (path 0) (Fin.tail path)
      have hrow :
          leadingOnesAdaptiveTransition rate
              (leadingOnesCoordinateFlip i x)
              (leadingOnesCoordinateFlip i (path 0)) =
            leadingOnesAdaptiveTransition rate x (path 0) := by
        change
          onePlusOneTransition
              (rate (leadingOnes (leadingOnesCoordinateFlip i x)))
              leadingOnesReal
              (leadingOnesCoordinateFlip i x)
              (leadingOnesCoordinateFlip i (path 0)) =
            onePlusOneTransition (rate (leadingOnes x))
              leadingOnesReal x (path 0)
        rw [leadingOnes_coordinateFlip_eq_of_lt x i hx]
        exact onePlusOneTransition_leadingOnes_coordinateFlip
          (rate (leadingOnes x)) x (path 0) i hx
      rw [hrow]
      rw [leadingOnesFiniteTrajectoryFlip_tail]
      rw [ih (path 0) (Fin.tail path) htail]

end ECRuntime
