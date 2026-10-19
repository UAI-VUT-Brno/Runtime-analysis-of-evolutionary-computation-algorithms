import ECRuntime.LeadingOnesExactEntryStep
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 22 fix 1: event-level assembly of the fixed-initial occupation recurrence

Stage 27 fix 21 fix 1 is compiler verified warning/error-free.  The first fix-22 compiler run reached this module and exposed only two local proof-shape failures; fix 22 fix 1 repairs those without changing the theorem surface.  The lower-score branch
of the one-step occupation recursion is therefore promoted: for every deterministic
initial state, the event

  `LO(X_t) < i` and `LO(X_{t+1}) = i`

has exactly the fixed-initial exact-entry mass at time `t+1`.

This module performs the remaining event-level bookkeeping around that fact.  It
introduces the same-level predecessor event, proves that on the already verified
almost-sure elitist trajectories the score-level event at time `t+1` is the disjoint
union of the below-to-exact and equal-to-exact branches, and proves the time-zero base
case of the scalar renewal equation.

The only stochastic statement deliberately left as an explicit local interface is the
one-step Markov lift

  P_x(LO(X_t)=i, LO(X_{t+1})=i)
    = stay_i * P_x(LO(X_t)=i).

The row-level factor `stay_i = 1 - p(1-p)^i` is already compiler verified in
`LeadingOnesOccupationRenewal`.  Once this single lift is supplied, the concrete
`HasLeadingOnesFixedInitialScoreLevelOccupationRenewal` follows immediately, and the
already promoted convolution theorem can be applied without further event algebra.
-/

/-- Two-time event saying that score level `i` is occupied at time `t` and remains
occupied at time `t+1`. -/
def leadingOnesEqualThenExactAtNextSet
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    Set (ℕ → BitString n) :=
  {path |
    leadingOnes (transitionTrajectoryState x path t) = i.val ∧
      leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val}

/-- The same-level two-time event is measurable. -/
theorem measurableSet_leadingOnesEqualThenExactAtNextSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (i : Fin n) (t : ℕ) :
    MeasurableSet (leadingOnesEqualThenExactAtNextSet x i t) := by
  have hexact :
      MeasurableSet
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) :=
    ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)).to_countable.measurableSet
  change MeasurableSet
    ((fun path => transitionTrajectoryState x path t) ⁻¹'
        {y : BitString n | leadingOnes y = i.val} ∩
      (fun path => transitionTrajectoryState x path (t + 1)) ⁻¹'
        {y : BitString n | leadingOnes y = i.val})
  exact (hexact.preimage (measurable_transitionTrajectoryState_fixed x t)).inter
    (hexact.preimage (measurable_transitionTrajectoryState_fixed x (t + 1)))

/-- The below-to-exact and equal-to-exact predecessor events are disjoint. -/
theorem disjoint_leadingOnesBelowThenExactAtNextSet_equalThenExactAtNextSet
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    Disjoint
      (leadingOnesBelowThenExactAtNextSet x i t)
      (leadingOnesEqualThenExactAtNextSet x i t) := by
  rw [Set.disjoint_left]
  intro path hbelow hequal
  exact (ne_of_lt hbelow.1) hequal.1

/-- On every potential-nonincreasing path, occupying score level `i` at time `t+1`
means that the predecessor score was either strictly below `i` or already exactly `i`.
The two alternatives are precisely the two disjoint events used by the renewal split. -/
theorem leadingOnes_scoreLevelAtTime_succ_iff_below_or_equalThenExact_of_nonincreasing
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ)
    (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path) :
    path ∈ leadingOnesScoreLevelAtTimeSet x i (t + 1) ↔
      path ∈
        (leadingOnesBelowThenExactAtNextSet x i t ∪
          leadingOnesEqualThenExactAtNextSet x i t) := by
  change
    leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val ↔
      ((leadingOnes (transitionTrajectoryState x path t) < i.val ∧
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val) ∨
        (leadingOnes (transitionTrajectoryState x path t) = i.val ∧
          leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val))
  constructor
  · intro hnext
    have hscore := leadingOnes_score_nondecreasingAlong_of_potential
      x path hmono (Nat.le_succ t)
    by_cases hcur : leadingOnes (transitionTrajectoryState x path t) = i.val
    · exact Or.inr ⟨hcur, hnext⟩
    · left
      constructor
      · rw [hnext] at hscore
        omega
      · exact hnext
  · rintro (hbelow | hequal)
    · exact hbelow.2
    · exact hequal.2

/-- Under the genuine fixed-initial LeadingOnes law, the score-level occupation mass at
`t+1` is the sum of the below-to-exact and equal-to-exact predecessor masses. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_succ_eq_below_add_equal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesFixedInitialScoreLevelOccupationMass
        p hp0 hp1 x i (t + 1) =
      leadingOnesTrajectoryMeasure p hp0 hp1 x
          (leadingOnesBelowThenExactAtNextSet x i t) +
        leadingOnesTrajectoryMeasure p hp0 hp1 x
          (leadingOnesEqualThenExactAtNextSet x i t) := by
  unfold leadingOnesFixedInitialScoreLevelOccupationMass
  have hcongr :
      leadingOnesTrajectoryMeasure p hp0 hp1 x
          (leadingOnesScoreLevelAtTimeSet x i (t + 1)) =
        leadingOnesTrajectoryMeasure p hp0 hp1 x
          (leadingOnesBelowThenExactAtNextSet x i t ∪
            leadingOnesEqualThenExactAtNextSet x i t) := by
    apply measure_congr
    filter_upwards [leadingOnesTrajectoryMeasure_ae_potentialNonincreasing
      p hp0 hp1 x] with path hmono
    exact propext
      (leadingOnes_scoreLevelAtTime_succ_iff_below_or_equalThenExact_of_nonincreasing
        x i t path hmono)
  rw [hcongr]
  exact MeasureTheory.measure_union'
    (disjoint_leadingOnesBelowThenExactAtNextSet_equalThenExactAtNextSet x i t)
    (measurableSet_leadingOnesBelowThenExactAtNextSet x i t)

/-- After substituting the promoted exact-entry identification, the one-step occupation
split has only the same-level predecessor branch left to evaluate. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_succ_eq_entry_add_equal
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesFixedInitialScoreLevelOccupationMass
        p hp0 hp1 x i (t + 1) =
      leadingOnesFixedInitialExactEntryENNMass p i x (t + 1) +
        leadingOnesTrajectoryMeasure p hp0 hp1 x
          (leadingOnesEqualThenExactAtNextSet x i t) := by
  rw [leadingOnesFixedInitialScoreLevelOccupationMass_succ_eq_below_add_equal
    p hp0 hp1 x i t]
  rw [leadingOnesTrajectoryMeasure_belowThenExactAtNextSet_eq_exactEntryENNMass
    p hp0 hp1 x i t]

/-- At time zero, occupation of score level `i` is already exact first entry into that
level.  This is the base case of the scalar renewal equation. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_zero_eq_exactEntry
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) :
    leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i 0 =
      leadingOnesFixedInitialExactEntryENNMass p i x 0 := by
  unfold leadingOnesFixedInitialScoreLevelOccupationMass
  unfold leadingOnesFixedInitialExactEntryENNMass
  rw [← leadingOnesTrajectoryMeasure_firstCrossingExactSet hp0 hp1 i x 0]
  apply measure_congr
  exact Filter.Eventually.of_forall (fun path => by
    change
      (leadingOnes (transitionTrajectoryState x path 0) = i.val) =
        (path ∈ leadingOnesTrajectoryFirstCrossingExactSet i x 0)
    apply propext
    rw [mem_leadingOnesTrajectoryFirstCrossingExactSet_iff]
    simp)

/-- Local interface for the sole remaining Markov lift in the concrete renewal proof:
the same-level two-time event has the promoted one-step stay factor times the current
occupation mass. -/
def HasLeadingOnesExactStayBranch
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) : Prop :=
  ∀ t : ℕ,
    leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesEqualThenExactAtNextSet x i t) =
      leadingOnesLevelStayENNReal p i *
        leadingOnesFixedInitialScoreLevelOccupationMass
          p hp0 hp1 x i t

/-- The event partition, promoted exact-entry branch, and time-zero base case show that
the same-level Markov lift is sufficient for the full concrete scalar renewal
recurrence. -/
theorem hasLeadingOnesFixedInitialScoreLevelOccupationRenewal_of_exactStayBranch
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n)
    (hstay : HasLeadingOnesExactStayBranch p hp0 hp1 x i) :
    HasLeadingOnesFixedInitialScoreLevelOccupationRenewal
      p hp0 hp1 x i := by
  constructor
  · exact leadingOnesFixedInitialScoreLevelOccupationMass_zero_eq_exactEntry
      p hp0 hp1 x i
  · intro t
    change
      leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i (t + 1) =
        leadingOnesFixedInitialExactEntryENNMass p i x (t + 1) +
          leadingOnesLevelStayENNReal p i *
            leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i t
    calc
      leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i (t + 1) =
          leadingOnesFixedInitialExactEntryENNMass p i x (t + 1) +
            leadingOnesTrajectoryMeasure p hp0 hp1 x
              (leadingOnesEqualThenExactAtNextSet x i t) :=
        leadingOnesFixedInitialScoreLevelOccupationMass_succ_eq_entry_add_equal
          p hp0 hp1 x i t
      _ = leadingOnesFixedInitialExactEntryENNMass p i x (t + 1) +
          leadingOnesLevelStayENNReal p i *
            leadingOnesFixedInitialScoreLevelOccupationMass p hp0 hp1 x i t := by
        rw [hstay t]

/-- Consequently, once the single same-level Markov lift is proved, every exact-time
occupation mass has the already verified entry/stay convolution representation. -/
theorem leadingOnesFixedInitialScoreLevelOccupationMass_eq_entryConvolution_of_exactStayBranch
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n)
    (hstay : HasLeadingOnesExactStayBranch p hp0 hp1 x i)
    (t : ℕ) :
    leadingOnesFixedInitialScoreLevelOccupationMass
        p hp0 hp1 x i t =
      ∑ s ∈ Finset.range (t + 1),
        leadingOnesFixedInitialExactEntryENNMass p i x s *
          (leadingOnesLevelStayENNReal p i) ^ (t - s) := by
  exact
    leadingOnesFixedInitialScoreLevelOccupationMass_eq_entryConvolution_of_renewal
      p hp0 hp1 x i
      (hasLeadingOnesFixedInitialScoreLevelOccupationRenewal_of_exactStayBranch
        p hp0 hp1 x i hstay)
      t

end ECRuntime
