import ECRuntime.LevelExitTrajectory
import ECRuntime.GeometricTail
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 17: one-level domination by the canonical geometric law

`LevelExitTrajectory.lean` turns the finite one-level survival recursion into a genuine
`HasGeometricTailBound` certificate for the conventional first hitting time of the
complement of a level.  This module packages that certificate in the distributional
form needed by the remaining adaptive fitness-level construction.

The key observation is intentionally simple but important for the architecture: for a
nonzero geometric parameter `p`, the verified canonical geometric waiting time has
*exactly* the survival profile used in `HasGeometricTailBound`.  Hence a geometric tail
certificate is equivalent to natural-threshold stochastic domination by either

* `geometricWaitingTime` under `geometricFailureMeasure p`, or
* the identity observable under the pushed-forward law `geometricWaitingMeasure p`.

Specializing this equivalence to `transitionTrajectoryFirstHittingTime (levelᶜ)` gives a
uniform local contract over every possible state at which the process may enter the
level.  The next stage can therefore concentrate on the genuinely adaptive issue:
assembling these history-dependent one-level comparisons with *fresh independent*
geometric coordinates.
-/

/-- A geometric tail certificate is exactly natural-threshold domination by the
canonical one-based geometric waiting time. -/
theorem hasGeometricTailBound_iff_natTailDominated_geometricWaitingTime
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) (p : unitInterval) (hp : p ≠ 0) :
    HasGeometricTailBound μ X p ↔
      NatTailDominated
        μ X
        (geometricFailureMeasure p) geometricWaitingTime := by
  constructor
  · intro h k
    calc
      runtimeTailMass μ X (k : ENNReal) ≤ geometricSurvival p k := h k
      _ = runtimeTailMass
          (geometricFailureMeasure p) geometricWaitingTime (k : ENNReal) :=
        (geometricWaitingTime_tail_exact hp k).symm
  · intro h k
    calc
      runtimeTailMass μ X (k : ENNReal) ≤
          runtimeTailMass
            (geometricFailureMeasure p) geometricWaitingTime (k : ENNReal) := h k
      _ = geometricSurvival p k := geometricWaitingTime_tail_exact hp k

/-- Forward form of
`hasGeometricTailBound_iff_natTailDominated_geometricWaitingTime`. -/
theorem natTailDominated_geometricWaitingTime_of_hasGeometricTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) (p : unitInterval) (hp : p ≠ 0)
    (h : HasGeometricTailBound μ X p) :
    NatTailDominated
      μ X
      (geometricFailureMeasure p) geometricWaitingTime :=
  (hasGeometricTailBound_iff_natTailDominated_geometricWaitingTime
    μ X p hp).mp h

/-- The same equivalence using the pushed-forward waiting-time law on `ENNReal`. -/
theorem hasGeometricTailBound_iff_natTailDominated_geometricWaitingMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) (p : unitInterval) (hp : p ≠ 0) :
    HasGeometricTailBound μ X p ↔
      NatTailDominated μ X (geometricWaitingMeasure p) id := by
  constructor
  · intro h k
    calc
      runtimeTailMass μ X (k : ENNReal) ≤ geometricSurvival p k := h k
      _ = runtimeTailMass (geometricWaitingMeasure p) id (k : ENNReal) :=
        (geometricWaitingMeasure_runtimeTailMass hp k).symm
  · intro h k
    calc
      runtimeTailMass μ X (k : ENNReal) ≤
          runtimeTailMass (geometricWaitingMeasure p) id (k : ENNReal) := h k
      _ = geometricSurvival p k := geometricWaitingMeasure_runtimeTailMass hp k

/-- Forward pushed-law form of the generic one-level domination bridge. -/
theorem natTailDominated_geometricWaitingMeasure_of_hasGeometricTailBound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ENNReal) (p : unitInterval) (hp : p ≠ 0)
    (h : HasGeometricTailBound μ X p) :
    NatTailDominated μ X (geometricWaitingMeasure p) id :=
  (hasGeometricTailBound_iff_natTailDominated_geometricWaitingMeasure
    μ X p hp).mp h

/--
A uniform one-step exit-mass lower bound gives natural-threshold stochastic domination
of the actual level-exit hitting time by the canonical one-based geometric waiting
time.  The statement is valid for every possible entry state `x` in the level.
-/
theorem natTailDominated_transitionTrajectoryLevelExit_geometricWaitingTime
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (hP : IsStochastic P) (p : unitInterval) (hp : p ≠ 0)
    (hexit : ∀ z, z ∈ level →
      (p : ℝ) ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) :
    NatTailDominated
      (transitionTrajectoryMeasure P hP x)
      (transitionTrajectoryFirstHittingTime (levelᶜ) x)
      (geometricFailureMeasure p) geometricWaitingTime := by
  apply natTailDominated_geometricWaitingTime_of_hasGeometricTailBound
    (transitionTrajectoryMeasure P hP x)
    (transitionTrajectoryFirstHittingTime (levelᶜ) x)
    p hp
  exact hasGeometricTailBound_transitionTrajectoryLevelExit
    P level hP p hexit x hx

/-- Pushed-law version of the uniform one-level trajectory domination theorem. -/
theorem natTailDominated_transitionTrajectoryLevelExit_geometricWaitingMeasure
    {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun z => z ∈ level)]
    (hP : IsStochastic P) (p : unitInterval) (hp : p ≠ 0)
    (hexit : ∀ z, z ∈ level →
      (p : ℝ) ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) :
    NatTailDominated
      (transitionTrajectoryMeasure P hP x)
      (transitionTrajectoryFirstHittingTime (levelᶜ) x)
      (geometricWaitingMeasure p) id := by
  apply natTailDominated_geometricWaitingMeasure_of_hasGeometricTailBound
    (transitionTrajectoryMeasure P hP x)
    (transitionTrajectoryFirstHittingTime (levelᶜ) x)
    p hp
  exact hasGeometricTailBound_transitionTrajectoryLevelExit
    P level hP p hexit x hx

end ECRuntime
