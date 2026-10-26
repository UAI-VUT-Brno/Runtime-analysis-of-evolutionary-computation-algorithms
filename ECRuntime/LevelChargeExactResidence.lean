import ECRuntime.LevelChargeWaitingBridge
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 27 fix 15: exact level charge / residence-length identity

Stage 27 fix 14 fix 2 is compiler verified warning/error-free.  In particular, the
canonical LeadingOnes distance potential is nonincreasing almost surely under the genuine
`(1+1)`-EA trajectory law, so the exact pathwise runtime decomposition no longer carries
an external monotonicity premise.

The remaining exact-runtime bridge is now local to one level.  The existing residence
machinery already proves that, on a nonincreasing path, the positive-level indicator is
exactly the indicator of the unique residence window `[entry, drop)`.  Stage 26 fix 49
used only the resulting upper bound on the complete charge because stochastic domination
needed no equality.  Exact expectation assembly does need the equality.

This module supplies that missing deterministic identity.  At the first downward-exit
time, the finite-horizon charge is exactly `drop - entry`; since the complete charge is
the supremum over all finite horizons and was already proved to be at most the same
residence length, the two quantities coincide.

No new probability or independence statement is introduced.  After compiler
verification, the next slice can work entirely at the measure level: decompose the
expected exact-level charge by first-entry time, use the promoted exact geometric
survival law after entry, and identify the result with first-entry mass times conditional
mean residence.
-/

/-- Summing the indicator of `[entry, drop)` through horizon `drop` counts the whole
residence window exactly. -/
theorem sum_residenceWindowIndicator_at_drop_eq_sub
    (entry drop : Nat) :
    Finset.sum (Finset.range drop)
        (fun t => residenceWindowIndicator entry drop t) =
      ((drop - entry : Nat) : ENNReal) := by
  classical
  let s : Finset Nat :=
    (Finset.range drop).filter (fun t => entry <= t /\ t < drop)
  have hs : s = Finset.Ico entry drop := by
    ext t
    constructor
    · intro ht
      have ht' := Finset.mem_filter.mp ht
      exact Finset.mem_Ico.mpr ⟨ht'.2.1, ht'.2.2⟩
    · intro ht
      have ht' := Finset.mem_Ico.mp ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht'.2, ht'⟩
  have hsum :
      Finset.sum (Finset.range drop)
          (fun t => residenceWindowIndicator entry drop t) =
        (s.card : ENNReal) := by
    dsimp [s]
    simp only [residenceWindowIndicator]
    rw [← Finset.sum_filter]
    simp
  rw [hsum, hs]
  simp

/-- At the first downward exit from a visited exact level, the finite-horizon charge is
exactly the natural length of the residence interval. -/
theorem finiteHorizonLevelCharge_at_firstExactLevelDrop_eq_exactLevelResidenceLength
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : Exists fun t =>
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : Exists fun t =>
      firstExactLevelEntryTime V x path i hvisit <= t /\
        V (transitionTrajectoryState x path t) < i.val + 1) :
    finiteHorizonLevelCharge V x path
        (firstExactLevelDropTime V x path i hvisit hdrop) i =
      (exactLevelResidenceLength V x path i hvisit hdrop : ENNReal) := by
  unfold finiteHorizonLevelCharge
  simp_rw [positiveLevelIndicator_eq_residenceWindowIndicator
    V x path hmono i hvisit hdrop]
  simpa [exactLevelResidenceLength] using
    (sum_residenceWindowIndicator_at_drop_eq_sub
      (firstExactLevelEntryTime V x path i hvisit)
      (firstExactLevelDropTime V x path i hvisit hdrop))

/-- Exact deterministic bridge between the complete positive-level charge and the unique
residence interval of a visited, eventually left level on a nonincreasing path. -/
theorem trajectoryLevelCharge_eq_exactLevelResidenceLength
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : Exists fun t =>
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : Exists fun t =>
      firstExactLevelEntryTime V x path i hvisit <= t /\
        V (transitionTrajectoryState x path t) < i.val + 1) :
    trajectoryLevelCharge V x i path =
      (exactLevelResidenceLength V x path i hvisit hdrop : ENNReal) := by
  apply le_antisymm
  · exact trajectoryLevelCharge_le_exactLevelResidenceLength
      V x path hmono i hvisit hdrop
  · calc
      (exactLevelResidenceLength V x path i hvisit hdrop : ENNReal) =
          finiteHorizonLevelCharge V x path
            (firstExactLevelDropTime V x path i hvisit hdrop) i := by
        symm
        exact
          finiteHorizonLevelCharge_at_firstExactLevelDrop_eq_exactLevelResidenceLength
            V x path hmono i hvisit hdrop
      _ <= trajectoryLevelCharge V x i path :=
        finiteHorizonLevelCharge_le_trajectoryLevelCharge
          V x path (firstExactLevelDropTime V x path i hvisit hdrop) i

end ECRuntime
