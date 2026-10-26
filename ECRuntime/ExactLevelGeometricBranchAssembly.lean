import ECRuntime.EventualExactLevelEntry
import ECRuntime.BernoulliWaitingExtraction
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 46: exact-level entry/skip geometric branch assembly

Stage 26 fix 45 fix 1 compiler-verifies the genuine infinite-path partition for one
exact positive level: the process either eventually enters exact level `i+1`, at a
unique finite first-entry time, or permanently skips that level.  The two measurable
branches have total probability one.  Earlier Stage 26 slices separately verify the
post-entry Bernoulli pattern consisting of `r` failures followed by one success, with
mass `(1-p_i)^r p_i`.

For the final multi-level comparison law, a skipped exact level still needs a fresh
geometric comparison coordinate: its actual residence contribution is zero, so an
independent geometric variable is automatically an admissible upper comparison on that
branch.  On the eventual-entry branch, the same canonical geometric law is attached to
the first-entry component.

This file performs that branch bookkeeping at the level of singleton masses.  It proves
that

* every exact first-entry-time component carries its verified terminal complement mass
  multiplied by the canonical geometric singleton mass;
* the whole eventual-entry branch carries the countable first-entry mass from fix 45
  multiplied by that singleton mass; and
* adding the permanent-skip branch recovers the full canonical geometric singleton law.

Thus level skipping no longer leaves a normalization gap in the comparison coordinate.
The next slice can package these branchwise masses into the joint trajectory/comparison
coupling and use the existing residence and almost-everywhere coupling-domination
interfaces.
-/

/-- A strictly positive real probability parameter gives a nonzero `unitInterval`
value when packaged by `probabilityUnitInterval`. -/
theorem probabilityUnitInterval_ne_zero_of_pos
    (q : Real) (hq : 0 < q) (hq1 : q <= 1) :
    probabilityUnitInterval q (le_of_lt hq) hq1 ≠ 0 := by
  intro hzero
  have hcoe := congrArg (fun r : unitInterval => (r : Real)) hzero
  exact (ne_of_gt hq) (by
    simpa [probabilityUnitInterval] using hcoe)

/-- Joint mass assigned to the branch where exact level `i+1` is first entered at
absolute time `T` and the comparison failure count equals `r`.  This is a branchwise
mass, not yet a measure on a product space. -/
noncomputable def firstExactLevelEntryAtGeometricFailureMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (T r : Nat) : ENNReal :=
  transitionTrajectoryMeasure P hP x
      (transitionTrajectoryFirstExactLevelEntrySet V x i T) *
    geometricFailureMeasure
      (probabilityUnitInterval (p i) hp0 hp1) {r}

/-- The exact-time branch mass is the compiler-verified terminal first-entry complement
mass multiplied by the canonical geometric singleton mass. -/
theorem firstExactLevelEntryAtGeometricFailureMass_eq_terminal
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (T r : Nat) :
    firstExactLevelEntryAtGeometricFailureMass
        P hP V p x i hp0 hp1 T r =
      ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T) *
        geometricFailureMeasure
          (probabilityUnitInterval (p i) hp0 hp1) {r} := by
  unfold firstExactLevelEntryAtGeometricFailureMass
  rw [transitionTrajectoryMeasure_firstExactLevelEntryAt
    P hP V hbound p x i T]

/-- With a strictly positive comparison parameter, the exact-time branch carries the
explicit `r`-failures-then-success factor from the random-entry analysis. -/
theorem firstExactLevelEntryAtGeometricFailureMass_eq_terminal_mul_pattern
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp : 0 < p i) (hp1 : p i <= 1)
    (T r : Nat) :
    firstExactLevelEntryAtGeometricFailureMass
        P hP V p x i (le_of_lt hp) hp1 T r =
      ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T) *
        ENNReal.ofReal ((1 - p i) ^ r * p i) := by
  rw [firstExactLevelEntryAtGeometricFailureMass_eq_terminal
    P hP V hbound p x i (le_of_lt hp) hp1 T r]
  let q : unitInterval :=
    probabilityUnitInterval (p i) (le_of_lt hp) hp1
  have hq : q ≠ 0 := by
    exact probabilityUnitInterval_ne_zero_of_pos (p i) hp hp1
  have hsingle := geometricFailureMeasure_singleton (p := q) hq r
  simpa [q, probabilityUnitInterval] using congrArg
    (fun z : ENNReal =>
      ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T) * z)
    hsingle

/-- Total mass of the eventual-entry branch paired with comparison failure count `r`. -/
noncomputable def eventualExactLevelEntryGeometricFailureMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (r : Nat) : ENNReal :=
  transitionTrajectoryMeasure P hP x
      (transitionTrajectoryEventuallyVisitsExactLevelSet V x i) *
    geometricFailureMeasure
      (probabilityUnitInterval (p i) hp0 hp1) {r}

/-- The eventual-entry branch uses exactly the countable first-entry mass from fix 45. -/
theorem eventualExactLevelEntryGeometricFailureMass_eq_tsum_terminal
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (r : Nat) :
    eventualExactLevelEntryGeometricFailureMass
        P hP V p x i hp0 hp1 r =
      (∑' T : Nat,
        ENNReal.ofReal
          (terminalFirstEntryComplementMass P V hbound p x i T)) *
        geometricFailureMeasure
          (probabilityUnitInterval (p i) hp0 hp1) {r} := by
  unfold eventualExactLevelEntryGeometricFailureMass
  rw [transitionTrajectoryMeasure_eventualExactLevelEntry
    P hP V hbound p x i]

/-- Total mass of the permanent-skip branch paired with comparison failure count `r`.
The comparison variable remains geometric on this branch because the actual residence
contribution of a skipped level is zero. -/
noncomputable def permanentSkipExactLevelGeometricFailureMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (r : Nat) : ENNReal :=
  transitionTrajectoryMeasure P hP x
      (transitionTrajectoryPermanentlySkipsExactLevelSet V x i) *
    geometricFailureMeasure
      (probabilityUnitInterval (p i) hp0 hp1) {r}

/-- Eventual entry and permanent skipping together recover the complete canonical
geometric failure-count singleton mass. -/
theorem eventualEntry_add_permanentSkip_geometricFailureMass
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp0 : 0 <= p i) (hp1 : p i <= 1)
    (r : Nat) :
    eventualExactLevelEntryGeometricFailureMass
        P hP V p x i hp0 hp1 r +
      permanentSkipExactLevelGeometricFailureMass
        P hP V p x i hp0 hp1 r =
      geometricFailureMeasure
        (probabilityUnitInterval (p i) hp0 hp1) {r} := by
  unfold eventualExactLevelEntryGeometricFailureMass
  unfold permanentSkipExactLevelGeometricFailureMass
  rw [← add_mul]
  rw [transitionTrajectoryMeasure_eventualEntry_add_permanentSkip
    P hP V x i]
  simp

/-- Explicit `r`-failures-then-success form of the complete entry/skip branch assembly. -/
theorem eventualEntry_add_permanentSkip_geometricFailureMass_eq_pattern
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (hp : 0 < p i) (hp1 : p i <= 1)
    (r : Nat) :
    eventualExactLevelEntryGeometricFailureMass
        P hP V p x i (le_of_lt hp) hp1 r +
      permanentSkipExactLevelGeometricFailureMass
        P hP V p x i (le_of_lt hp) hp1 r =
      ENNReal.ofReal ((1 - p i) ^ r * p i) := by
  rw [eventualEntry_add_permanentSkip_geometricFailureMass
    P hP V p x i (le_of_lt hp) hp1 r]
  let q : unitInterval :=
    probabilityUnitInterval (p i) (le_of_lt hp) hp1
  have hq : q ≠ 0 := by
    exact probabilityUnitInterval_ne_zero_of_pos (p i) hp hp1
  simpa [q, probabilityUnitInterval] using
    (geometricFailureMeasure_singleton (p := q) hq r)

end ECRuntime
