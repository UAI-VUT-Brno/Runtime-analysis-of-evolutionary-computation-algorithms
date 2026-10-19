import ECRuntime.InfiniteAdaptiveCoupledMarginals
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 49: level-charge / history-dependent waiting bridge

Stage 26 fix 48 fix 2 is compiler verified warning-free.  The infinite adaptive
state/vector-label law therefore now has the two finite marginals needed downstream and,
almost surely, every realized adaptive coupled transition has positive coupled weight.

One deterministic interface was still missing before the geometric-coordinate extraction
can feed `CouplingDomination.lean`.  `HistoryDependentWaiting.lean` bounds the natural
length of the single exact-level residence interval, whereas `LevelCharges.lean` and the
final coupling bridge use the complete `ENNReal` quantity `trajectoryLevelCharge`.

This file closes that gap.  On a nonincreasing potential path, the exact-level indicator
is the indicator of the residence interval `[entry, drop)`.  Any finite prefix therefore
contains at most `drop-entry` charged times, and taking the supremum over horizons shows
that the complete level charge is bounded by the exact residence length.  Combining this
with the verified first-comparison-success theorem yields a direct bound of the complete
level charge by the one-based history-dependent waiting time.  If an exact level is never
visited, its complete charge is zero and is consequently below every geometric waiting
value.

The last theorem lifts the visited-level statement almost everywhere under the genuine
infinite adaptive coupled law, conditional only on the separate pathwise potential-
monotonicity premise that the eventual fitness-level application must provide.

No new probability law or independence assertion is introduced here.  The next slice can
concentrate purely on the distribution of the extracted waiting coordinates.
-/

/-- A finite prefix contains at most `drop-entry` points in the residence window
`[entry, drop)`. -/
theorem sum_residenceWindowIndicator_le_sub
    (entry drop T : Nat) :
    Finset.sum (Finset.range T)
        (fun t => residenceWindowIndicator entry drop t) <=
      ((drop - entry : Nat) : ENNReal) := by
  classical
  let s : Finset Nat :=
    (Finset.range T).filter (fun t => entry <= t /\ t < drop)
  have hsubset : s ⊆ Finset.Ico entry drop := by
    intro t ht
    have ht' := Finset.mem_filter.mp ht
    exact Finset.mem_Ico.mpr ht'.2
  have hcard : s.card <= drop - entry := by
    calc
      s.card <= (Finset.Ico entry drop).card := Finset.card_le_card hsubset
      _ = drop - entry := by simp
  have hsum :
      Finset.sum (Finset.range T)
          (fun t => residenceWindowIndicator entry drop t) =
        (s.card : ENNReal) := by
    dsimp [s]
    simp only [residenceWindowIndicator]
    rw [← Finset.sum_filter]
    simp
  rw [hsum]
  exact_mod_cast hcard

/-- Every finite-horizon charge of a visited and eventually left level is bounded by
that level's exact residence length. -/
theorem finiteHorizonLevelCharge_le_exactLevelResidenceLength
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : Exists fun t =>
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : Exists fun t =>
      firstExactLevelEntryTime V x path i hvisit <= t /\
        V (transitionTrajectoryState x path t) < i.val + 1)
    (T : Nat) :
    finiteHorizonLevelCharge V x path T i <=
      (exactLevelResidenceLength V x path i hvisit hdrop : ENNReal) := by
  unfold finiteHorizonLevelCharge
  simp_rw [positiveLevelIndicator_eq_residenceWindowIndicator
    V x path hmono i hvisit hdrop]
  simpa [exactLevelResidenceLength] using
    (sum_residenceWindowIndicator_le_sub
      (firstExactLevelEntryTime V x path i hvisit)
      (firstExactLevelDropTime V x path i hvisit hdrop)
      T)

/-- The complete charge of a visited and eventually left exact level is bounded by the
natural length of its unique residence interval. -/
theorem trajectoryLevelCharge_le_exactLevelResidenceLength
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : Exists fun t =>
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : Exists fun t =>
      firstExactLevelEntryTime V x path i hvisit <= t /\
        V (transitionTrajectoryState x path t) < i.val + 1) :
    trajectoryLevelCharge V x i path <=
      (exactLevelResidenceLength V x path i hvisit hdrop : ENNReal) := by
  unfold trajectoryLevelCharge
  apply iSup_le
  intro T
  exact finiteHorizonLevelCharge_le_exactLevelResidenceLength
    V x path hmono i hvisit hdrop T

/-- An exact level that is never visited contributes zero complete level charge. -/
theorem trajectoryLevelCharge_eq_zero_of_never_visits_exactLevel
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (i : Fin m)
    (hskip : forall t : Nat,
      V (transitionTrajectoryState x path t) ≠ i.val + 1) :
    trajectoryLevelCharge V x i path = 0 := by
  apply le_antisymm
  · unfold trajectoryLevelCharge
    apply iSup_le
    intro T
    have hsum :
        Finset.sum (Finset.range T) (fun t =>
          positiveLevelIndicator (V (transitionTrajectoryState x path t)) i) = 0 := by
      apply Finset.sum_eq_zero
      intro t _ht
      simp [positiveLevelIndicator, hskip t]
    simpa [finiteHorizonLevelCharge] using hsum.le
  · exact bot_le

/-- Main deterministic visited-level bridge: under potential monotonicity and positive
adaptive coupled-step support, the complete level charge is bounded by the first
comparison-success waiting time measured from the actual first entry. -/
theorem trajectoryLevelCharge_le_firstComparisonSuccessWaitingAfterEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : Nat -> (Fin m -> Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x path labels)
    (i : Fin m)
    (hvisit : Exists fun t =>
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : Exists fun r =>
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) :
    trajectoryLevelCharge V x i path <=
      (firstComparisonSuccessWaitingAfterEntry
        V x path labels i hvisit hsucc : ENNReal) := by
  obtain ⟨hdrop, hres⟩ :=
    exists_exactLevelDrop_with_residence_bound
      P V hbound p x path hmono labels hsupport i hvisit hsucc
  calc
    trajectoryLevelCharge V x i path <=
        (exactLevelResidenceLength V x path i hvisit hdrop : ENNReal) :=
      trajectoryLevelCharge_le_exactLevelResidenceLength
        V x path hmono i hvisit hdrop
    _ <= (firstComparisonSuccessWaitingAfterEntry
          V x path labels i hvisit hsucc : ENNReal) := by
      exact_mod_cast hres

/-- If the selected first-success offset is `r`, the complete visited-level charge is
bounded by the canonical one-based geometric waiting value `r+1`. -/
theorem trajectoryLevelCharge_le_geometricWaitingTime_of_firstComparisonSuccessOffset
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : Nat -> (Fin m -> Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport
      P V hbound p x path labels)
    (i : Fin m)
    (hvisit : Exists fun t =>
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : Exists fun r =>
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true)
    (r : Nat)
    (hr : firstComparisonSuccessOffsetAfterEntry
      V x path labels i hvisit hsucc = r) :
    trajectoryLevelCharge V x i path <= geometricWaitingTime r := by
  have hboundWait :=
    trajectoryLevelCharge_le_firstComparisonSuccessWaitingAfterEntry
      P V hbound p x path hmono labels hsupport i hvisit hsucc
  simpa [firstComparisonSuccessWaitingAfterEntry, geometricWaitingTime, hr] using
    hboundWait

/-- A permanently skipped exact level is below every canonical geometric waiting value. -/
theorem trajectoryLevelCharge_le_geometricWaitingTime_of_never_visits_exactLevel
    {alpha : Type*} {m : Nat}
    (V : alpha -> Nat) (x : alpha) (path : Nat -> alpha)
    (i : Fin m)
    (hskip : forall t : Nat,
      V (transitionTrajectoryState x path t) ≠ i.val + 1)
    (r : Nat) :
    trajectoryLevelCharge V x i path <= geometricWaitingTime r := by
  rw [trajectoryLevelCharge_eq_zero_of_never_visits_exactLevel
    V x path i hskip]
  exact bot_le

/-- Almost-everywhere version of the visited-level charge/waiting bound on the genuine
infinite adaptive coupled space.  Potential monotonicity is kept as an explicit a.e.
premise; the positive adaptive support premise is discharged by fix 48 fix 2. -/
theorem adaptiveMultiLevelCoupledTrajectoryMeasure_ae_levelCharge_le_waiting_of_monotone
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha)
    (hmono : ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      IsPotentialNonincreasingAlong V x (adaptiveCoupledStatePath path)) :
    ∀ᵐ path ∂(adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x),
      forall (i : Fin m)
        (hvisit : Exists fun t =>
          V (transitionTrajectoryState x (adaptiveCoupledStatePath path) t) =
            i.val + 1)
        (hsucc : Exists fun r =>
          adaptiveCoupledLabelStream path
            (firstExactLevelEntryTime
              V x (adaptiveCoupledStatePath path) i hvisit + r) i = true),
        trajectoryLevelCharge V x i (adaptiveCoupledStatePath path) <=
          (firstComparisonSuccessWaitingAfterEntry
            V x (adaptiveCoupledStatePath path)
            (adaptiveCoupledLabelStream path) i hvisit hsucc : ENNReal) := by
  filter_upwards
    [adaptiveMultiLevelCoupledTrajectoryMeasure_ae_positiveAdaptiveSupport
      P hP V hbound p hp hp1 hexit x, hmono] with path hsupport hmonoPath
  intro i hvisit hsucc
  exact trajectoryLevelCharge_le_firstComparisonSuccessWaitingAfterEntry
    P V hbound p x (adaptiveCoupledStatePath path) hmonoPath
      (adaptiveCoupledLabelStream path) hsupport i hvisit hsucc

end ECRuntime
