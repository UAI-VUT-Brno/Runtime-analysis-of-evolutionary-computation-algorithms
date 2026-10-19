import ECRuntime.RestrictedFirstEntryWeightedHistoryBridge
import ECRuntime.RestrictedFirstEntryTimeDecomposition
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 60: countable restricted first-entry weighted histories

Stage 26 fix 59 fix 2 is compiler verified warning-free.  Fix 59 identifies every
fixed exact first-entry-time slice with a canonical finite
`weightedFirstEntryHistoryComplementMass`.  Fix 56 independently proves that the
genuine restricted eventual-entry branch is the disjoint countable sum of its exact
first-entry-time slices.

This module joins those two verified interfaces without forcing all possible entry
times into one finite history type.  A family `C T` describes, on the exact-time-`T`
slice, the deleted-coordinate finite-prefix restriction induced by the outer infinite
restriction `A`.  The only structural assumption is the corresponding event equality
on each slice.

The countable weighted entry mass is kept in `ENNReal`: each fixed-time real mass is
embedded with `ENNReal.ofReal` and the family is summed with `tsum`.  Its real version
is defined only as the `toReal` of the total, so this stage does not interchange
`toReal` with an infinite real series or assume summability that has not yet been
proved.

The main endpoints identify the countable weighted mass with the genuine restricted
eventual-entry mass and then combine it with the already verified genuine permanent-
skip branch.  The next stage can therefore lift the one-coordinate geometric peeling
identity over this countable family directly, rather than returning to the obsolete
finite-`beta` `hentry` interface from fix 55.
-/

/-- Countable `ENNReal` mass obtained by summing the canonical fixed-time weighted
first-entry masses from fix 59. -/
noncomputable def countableRestrictedFirstEntryWeightedHistoryENNMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) : ENNReal :=
  ∑' T : Nat,
    ENNReal.ofReal
      (restrictedTerminalFirstEntryWeightedHistoryMass
        P V hbound p x i (C T))

/-- Real form of the countable weighted first-entry mass.  It is deliberately the
`toReal` of the `ENNReal` total rather than a real `tsum`. -/
noncomputable def countableRestrictedFirstEntryWeightedHistoryRealMass
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (i : Fin m)
    (C : (T : Nat) ->
      Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) : Real :=
  (countableRestrictedFirstEntryWeightedHistoryENNMass
    P V hbound p x i C).toReal

/-- Every fixed-time canonical weighted-history mass is nonnegative under the genuine
coupled-law hypotheses.  This records the positivity needed for the later countable
geometric-factor lift. -/
theorem restrictedTerminalFirstEntryWeightedHistoryMass_nonneg
    {alpha : Type*} [Fintype alpha] {m T : Nat}
    (P : TransitionMatrix alpha) (hP : IsStochastic P)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : alpha) (i : Fin m)
    (C : Set (FiniteTrajectory (alpha × InactiveCoordinateLabelVector i) T)) :
    0 <= restrictedTerminalFirstEntryWeightedHistoryMass
      P V hbound p x i C := by
  rw [restrictedTerminalFirstEntryWeightedHistoryMass_eq_complementMass
    P V hbound p x i C]
  exact restrictedTerminalFirstEntryComplementMass_nonneg
    P hP V hbound p hp hp1 hexit x i C

/-- If the outer infinite-path restriction is represented on each exact-entry slice by
its deleted-coordinate finite-prefix condition `C T`, then the genuine restricted
entry measure is exactly the countable weighted-history `ENNReal` mass. -/
theorem adaptiveCoupled_restricted_eventualEntry_measure_eq_countableWeightedHistory
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
          adaptiveCoupledFirstExactLevelEntrySet V x i T) :
    adaptiveMultiLevelCoupledTrajectoryMeasure
        P hP V hbound p hp hp1 hexit x
        (A ∩ adaptiveCoupledEventuallyVisitsExactLevelSet V x i) =
      countableRestrictedFirstEntryWeightedHistoryENNMass
        P V hbound p x i C := by
  rw [adaptiveCoupled_restricted_eventualEntry_measure_eq_tsum_firstEntry
    P hP V hbound p hp hp1 hexit x i A hA]
  unfold countableRestrictedFirstEntryWeightedHistoryENNMass
  apply tsum_congr
  intro T
  rw [hslice T]
  exact
    adaptiveMultiLevelCoupledTrajectoryMeasure_deletedCoordinatePrefix_restricted_firstEntry_eq_weightedHistory
      P hP V hbound p hp hp1 hexit x i (C T)

/-- Real-mass form of the countable restricted-entry identification. -/
theorem adaptiveCoupledRestrictedEntryRealMass_eq_countableWeightedHistoryRealMass
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
          adaptiveCoupledFirstExactLevelEntrySet V x i T) :
    adaptiveCoupledRestrictedEntryRealMass
        P hP V hbound p hp hp1 hexit x i A =
      countableRestrictedFirstEntryWeightedHistoryRealMass
        P V hbound p x i C := by
  unfold adaptiveCoupledRestrictedEntryRealMass
  unfold adaptiveCoupledRestrictedRealMass
  unfold countableRestrictedFirstEntryWeightedHistoryRealMass
  rw [adaptiveCoupled_restricted_eventualEntry_measure_eq_countableWeightedHistory
    P hP V hbound p hp hp1 hexit x i A hA C hslice]

/-- The countable weighted entry mass plus the genuine permanent-skip mass exhausts the
entire measurable outer restriction.  This is the countable replacement for the
finite-`beta` `hentry` assumption in fix 55. -/
theorem countableWeightedEntry_add_permanentSkip_eq_restrictedRealMass
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
          adaptiveCoupledFirstExactLevelEntrySet V x i T) :
    countableRestrictedFirstEntryWeightedHistoryRealMass
        P V hbound p x i C +
      adaptiveCoupledRestrictedPermanentSkipRealMass
        P hP V hbound p hp hp1 hexit x i A =
      adaptiveCoupledRestrictedRealMass
        P hP V hbound p hp hp1 hexit x A := by
  rw [← adaptiveCoupledRestrictedEntryRealMass_eq_countableWeightedHistoryRealMass
    P hP V hbound p hp hp1 hexit x i A hA C hslice]
  exact adaptiveCoupledRestrictedEntryRealMass_add_permanentSkipRealMass
    P hP V hbound p hp hp1 hexit x i A hA

end ECRuntime
