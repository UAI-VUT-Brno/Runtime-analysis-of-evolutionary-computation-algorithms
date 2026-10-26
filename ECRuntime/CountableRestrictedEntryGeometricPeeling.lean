import ECRuntime.CountableRestrictedFirstEntryWeightedHistory
import ECRuntime.WeightedEntrySkipGeometricPeeling
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 61: countable restricted-entry geometric peeling

Stage 26 fix 60 is compiler verified warning-free.  It represents the genuine
restricted eventual-entry branch as an `ENNReal` `tsum` of the canonical fixed-time
weighted-history masses from fix 59, and combines the corresponding real mass with the
genuine permanent-skip branch to recover the whole restricted outer event.

Fix 53 already proves, for every finite weighted first-entry family, that prescribing
failure count `r` at the current comparison coordinate multiplies its coordinate-
deleted mass by the geometric singleton factor

  `(1 - p i)^r * p i`.

This module instantiates that theorem on each canonical exact-entry-time history type,
then lifts the common factor through the countable exact-time `ENNReal` sum.  No real-
series summability hypothesis is needed: nonnegativity of every fixed-time weighted
mass allows `ENNReal.ofReal_mul`, and `ENNReal.tsum_mul_right` factors the common
`ENNReal` multiplier exactly.

The final endpoint adds the already-verified genuine permanent-skip contribution and
uses the fix-60 entry/skip exhaustion identity.  Thus, under the same per-time cylinder
representation of the outer restriction, one complete coordinate-peeling step has the
form

  `next mass = previous restricted mass * ((1 - p i)^r * p i)`.

This is still a scalar mass interface.  The next stage must use it recursively for an
already-fixed prefix of higher-level failure counts and connect those scalar masses to
the complete failure-vector singleton events required by
`AdaptiveGeometricFailureCouplingSpec`.
-/

/-- Canonical fixed-time visited-branch mass after prescribing failure count `r` at
coordinate `i`.  This is the fix-54 named geometric-pattern mass instantiated on the
fix-59 terminal first-entry history subtype. -/
noncomputable def restrictedTerminalFirstEntryGeometricFailurePatternMass
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) : Real := by
  classical
  let beta := DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i
  letI : Fintype beta := Fintype.ofFinite beta
  exact weightedFirstEntryGeometricFailurePatternMass
    P V hbound p x
      (fun a : beta => deletedCoordinateTerminalFirstEntryStateStream x i a)
      (fun a : beta => deletedCoordinateTerminalFirstEntryLabelStream i a)
      i
      (fun a : beta => deletedCoordinateTerminalFirstEntryVisitWitness V x i a)
      (fun a : beta => deletedCoordinateTerminalFirstEntryRestrictionWeight C a)
      r

/-- Fixed-time canonical prescribed-failure mass equals the fixed-time coordinate-
deleted weighted-history mass times the geometric singleton factor. -/
theorem restrictedTerminalFirstEntryGeometricFailurePatternMass_eq
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) :
    restrictedTerminalFirstEntryGeometricFailurePatternMass
        P V hbound p x i C r =
      restrictedTerminalFirstEntryWeightedHistoryMass
          P V hbound p x i C *
        ((1 - p i) ^ r * p i) := by
  classical
  let beta := DeletedCoordinateTerminalFirstEntryHistory (T := T) V x i
  letI : Fintype beta := Fintype.ofFinite beta
  change
    weightedFirstEntryGeometricFailurePatternMass
        P V hbound p x
          (fun a : beta =>
            deletedCoordinateTerminalFirstEntryStateStream x i a)
          (fun a : beta =>
            deletedCoordinateTerminalFirstEntryLabelStream i a)
          i
          (fun a : beta =>
            deletedCoordinateTerminalFirstEntryVisitWitness V x i a)
          (fun a : beta =>
            deletedCoordinateTerminalFirstEntryRestrictionWeight C a)
          r =
      weightedFirstEntryHistoryComplementMass
          P V hbound p x
            (fun a : beta =>
              deletedCoordinateTerminalFirstEntryStateStream x i a)
            (fun a : beta =>
              deletedCoordinateTerminalFirstEntryLabelStream i a)
            i
            (fun a : beta =>
              deletedCoordinateTerminalFirstEntryVisitWitness V x i a)
            (fun a : beta =>
              deletedCoordinateTerminalFirstEntryRestrictionWeight C a) *
        ((1 - p i) ^ r * p i)
  exact weightedFirstEntryGeometricFailurePatternMass_eq
    P V hbound p x
      (fun a : beta => deletedCoordinateTerminalFirstEntryStateStream x i a)
      (fun a : beta => deletedCoordinateTerminalFirstEntryLabelStream i a)
      i
      (fun a : beta => deletedCoordinateTerminalFirstEntryVisitWitness V x i a)
      (fun a : beta => deletedCoordinateTerminalFirstEntryRestrictionWeight C a)
      r

/-- The real geometric singleton factor is nonnegative under the level-probability
hypotheses. -/
theorem geometricFailureSingletonFactor_nonneg
    {m : Nat} (p : Fin m -> Real) (i : Fin m)
    (hp : 0 < p i) (hp1 : p i <= 1) (r : Nat) :
    0 <= (1 - p i) ^ r * p i := by
  exact mul_nonneg
    (pow_nonneg (sub_nonneg.mpr hp1) r)
    (le_of_lt hp)

/-- The extracted `ENNReal` singleton factor is exactly the singleton mass of the
canonical geometric failure-count law at coordinate `i`. -/
theorem geometricFailureSingletonFactorENNReal_eq_measure_singleton
    {m : Nat} (p : Fin m -> Real) (i : Fin m)
    (hp : 0 < p i) (hp1 : p i <= 1) (r : Nat) :
    ENNReal.ofReal ((1 - p i) ^ r * p i) =
      geometricFailureMeasure
        (probabilityUnitInterval (p i) (le_of_lt hp) hp1) {r} := by
  let q : unitInterval :=
    probabilityUnitInterval (p i) (le_of_lt hp) hp1
  have hq : q ≠ 0 := by
    exact probabilityUnitInterval_ne_zero_of_pos (p i) hp hp1
  have hsingle := geometricFailureMeasure_singleton (p := q) hq r
  symm
  simpa [q, probabilityUnitInterval] using hsingle

/-- Countable `ENNReal` visited-branch mass after prescribing failure count `r` at the
current coordinate on every exact-entry-time slice. -/
noncomputable def countableRestrictedFirstEntryGeometricFailurePatternENNMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) : ENNReal :=
  ∑' T : Nat,
    ENNReal.ofReal
      (restrictedTerminalFirstEntryGeometricFailurePatternMass
        P V hbound p x i (C T) r)

/-- The prescribed-failure factor pulls through the countable exact-entry-time sum. -/
theorem countableRestrictedFirstEntryGeometricFailurePatternENNMass_eq
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) :
    countableRestrictedFirstEntryGeometricFailurePatternENNMass
        P V hbound p x i C r =
      countableRestrictedFirstEntryWeightedHistoryENNMass
          P V hbound p x i C *
        ENNReal.ofReal ((1 - p i) ^ r * p i) := by
  unfold countableRestrictedFirstEntryGeometricFailurePatternENNMass
  unfold countableRestrictedFirstEntryWeightedHistoryENNMass
  calc
    (∑' T : Nat,
      ENNReal.ofReal
        (restrictedTerminalFirstEntryGeometricFailurePatternMass
          P V hbound p x i (C T) r)) =
        ∑' T : Nat,
          ENNReal.ofReal
            (restrictedTerminalFirstEntryWeightedHistoryMass
                P V hbound p x i (C T) *
              ((1 - p i) ^ r * p i)) := by
      apply tsum_congr
      intro T
      rw [restrictedTerminalFirstEntryGeometricFailurePatternMass_eq
        P V hbound p x i (C T) r]
    _ = ∑' T : Nat,
        ENNReal.ofReal
            (restrictedTerminalFirstEntryWeightedHistoryMass
              P V hbound p x i (C T)) *
          ENNReal.ofReal ((1 - p i) ^ r * p i) := by
      apply tsum_congr
      intro T
      rw [ENNReal.ofReal_mul
        (restrictedTerminalFirstEntryWeightedHistoryMass_nonneg
          P hP V hbound p hp hp1 hexit x i (C T))]
    _ = (∑' T : Nat,
        ENNReal.ofReal
          (restrictedTerminalFirstEntryWeightedHistoryMass
            P V hbound p x i (C T))) *
        ENNReal.ofReal ((1 - p i) ^ r * p i) := by
      exact ENNReal.tsum_mul_right

/-- Measure-singleton form of the countable prescribed-failure factorization. -/
theorem countableRestrictedFirstEntryGeometricFailurePatternENNMass_eq_measure_singleton
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) :
    countableRestrictedFirstEntryGeometricFailurePatternENNMass
        P V hbound p x i C r =
      countableRestrictedFirstEntryWeightedHistoryENNMass
          P V hbound p x i C *
        geometricFailureMeasure
          (probabilityUnitInterval (p i) (le_of_lt (hp i)) (hp1 i)) {r} := by
  rw [countableRestrictedFirstEntryGeometricFailurePatternENNMass_eq
    P hP V hbound p hp hp1 hexit x i C r]
  rw [geometricFailureSingletonFactorENNReal_eq_measure_singleton
    p i (hp i) (hp1 i) r]

/-- Real view of the countable prescribed-failure visited-branch mass. -/
noncomputable def countableRestrictedFirstEntryGeometricFailurePatternRealMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) : Real :=
  (countableRestrictedFirstEntryGeometricFailurePatternENNMass
    P V hbound p x i C r).toReal

/-- The real countable visited-branch prescribed-failure mass is the countable entry
mass times the same geometric singleton factor. -/
theorem countableRestrictedFirstEntryGeometricFailurePatternRealMass_eq
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (r : Nat) :
    countableRestrictedFirstEntryGeometricFailurePatternRealMass
        P V hbound p x i C r =
      countableRestrictedFirstEntryWeightedHistoryRealMass
          P V hbound p x i C *
        ((1 - p i) ^ r * p i) := by
  unfold countableRestrictedFirstEntryGeometricFailurePatternRealMass
  unfold countableRestrictedFirstEntryWeightedHistoryRealMass
  rw [countableRestrictedFirstEntryGeometricFailurePatternENNMass_eq
    P hP V hbound p hp hp1 hexit x i C r]
  let entryMass := countableRestrictedFirstEntryWeightedHistoryENNMass
    P V hbound p x i C
  let factor := (1 - p i) ^ r * p i
  have hfactor : 0 <= factor := by
    exact geometricFailureSingletonFactor_nonneg p i (hp i) (hp1 i) r
  calc
    (entryMass * ENNReal.ofReal factor).toReal =
        (ENNReal.ofReal factor * entryMass).toReal := by rw [mul_comm]
    _ = factor * entryMass.toReal := by
      exact ENNReal.toReal_ofReal_mul factor entryMass hfactor
    _ = entryMass.toReal * factor := by ring

/-- Countable visited prescribed-failure mass plus an abstract permanent-skip
prescribed-failure contribution. -/
noncomputable def countableRestrictedEntrySkipGeometricFailurePatternRealMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (skipMass : Real) (r : Nat) : Real :=
  countableRestrictedFirstEntryGeometricFailurePatternRealMass
      P V hbound p x i C r +
    weightedPermanentSkipGeometricFailurePatternMass skipMass (p i) r

/-- Abstract countable entry/skip peeling: both branches carry the same geometric
singleton factor. -/
theorem countableRestrictedEntrySkipGeometricFailurePatternRealMass_eq
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (skipMass : Real) (r : Nat) :
    countableRestrictedEntrySkipGeometricFailurePatternRealMass
        P V hbound p x i C skipMass r =
      (countableRestrictedFirstEntryWeightedHistoryRealMass
          P V hbound p x i C + skipMass) *
        ((1 - p i) ^ r * p i) := by
  unfold countableRestrictedEntrySkipGeometricFailurePatternRealMass
  rw [countableRestrictedFirstEntryGeometricFailurePatternRealMass_eq
    P hP V hbound p hp hp1 hexit x i C r]
  unfold weightedPermanentSkipGeometricFailurePatternMass
  ring

/-- Concrete countable one-coordinate peeling against the genuine restricted adaptive
mass.  The per-time cylinder representation is exactly the fix-60 hypothesis that
identifies the countable weighted entry branch with the actual restricted eventual-
entry branch. -/
theorem countableRestrictedEntrySkipGeometricFailurePatternRealMass_eq_restrictedRealMass_mul_pattern
    {alpha : Type*} [Fintype alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    {m : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (A : Set (Nat -> (alpha × (Fin m -> Bool))))
    (hA : MeasurableSet A)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T))
    (hslice : forall T : Nat,
      A ∩ adaptiveCoupledFirstExactLevelEntrySet V x i T =
        adaptiveCoupledDeletedCoordinatePrefixRestrictionSet i (C T) ∩
          adaptiveCoupledFirstExactLevelEntrySet V x i T)
    (r : Nat) :
    countableRestrictedEntrySkipGeometricFailurePatternRealMass
        P V hbound p x i C
          (adaptiveCoupledRestrictedPermanentSkipRealMass
            P hP V hbound p hp hp1 hexit x i A) r =
      adaptiveCoupledRestrictedRealMass
          P hP V hbound p hp hp1 hexit x A *
        ((1 - p i) ^ r * p i) := by
  rw [countableRestrictedEntrySkipGeometricFailurePatternRealMass_eq
    P hP V hbound p hp hp1 hexit x i C
      (adaptiveCoupledRestrictedPermanentSkipRealMass
        P hP V hbound p hp hp1 hexit x i A) r]
  rw [countableWeightedEntry_add_permanentSkip_eq_restrictedRealMass
    P hP V hbound p hp hp1 hexit x i A hA C hslice]

end ECRuntime
