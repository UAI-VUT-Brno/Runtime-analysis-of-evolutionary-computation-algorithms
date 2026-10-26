import ECRuntime.LeadingOnesOccupationRenewal
import ECRuntime.LeadingOnesFirstCrossingMeasure
import ECRuntime.LeadingOnesTrajectoryMonotonicity
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 21: exact first entry as the below-to-level one-step event

Stage 27 fix 20 fix 1 is compiler verified warning/error-free.  The renewal algebra,
positive-support score monotonicity, zero return mass from above a level, and exact
same-level stay factor are therefore promoted.

The only stochastic term in the concrete occupation recurrence that is not already
named is the contribution from predecessor states strictly below score level `i`.  For
an elitist LeadingOnes trajectory this contribution is exactly first entry into score
level `i` at the next time.  This module makes that identification on the genuine
trajectory space.

The proof deliberately stays at the event/measure level.  It first gives the fixed-
initial exact-entry finite-path slice its own measurable cylinder and identifies its
trajectory probability with the already promoted explicit path-weight mass.  It then
uses almost-sure potential monotonicity to show that, at time `t+1`, this exact-entry
cylinder agrees almost surely with the two-time event

  `LO(X_t) < i` and `LO(X_{t+1}) = i`.

Thus the lower-score branch of the pending one-step occupation recurrence is now
exactly the existing fixed-initial exact-entry mass, without any independence or
stopping-time assumption.
-/

/-- Finite post-initial trajectories whose first crossing of boundary `i` occurs at
terminal time `t` and lands exactly on score level `i`. -/
def leadingOnesFiniteFirstCrossingExactSet
    {n : ℕ} (i : Fin n) (x : BitString n) (t : ℕ) :
    Set (FiniteTrajectory (BitString n) t) :=
  {path | leadingOnesFirstCrossingExact i (x, path)}

/-- The finite exact-entry slice is measurable because the finite trajectory space is
finite. -/
theorem measurableSet_leadingOnesFiniteFirstCrossingExactSet
    {n t : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (i : Fin n) (x : BitString n) :
    MeasurableSet (leadingOnesFiniteFirstCrossingExactSet i x t) := by
  exact (leadingOnesFiniteFirstCrossingExactSet i x t).to_countable.measurableSet

/-- The explicit finite-trajectory probability of exact first entry is the `ENNReal`
embedding of the fixed-initial exact-entry path-weight sum from fix 18. -/
theorem finiteTrajectoryMeasure_leadingOnesFiniteFirstCrossingExactSet
    {n t : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) :
    finiteTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
        t x (leadingOnesFiniteFirstCrossingExactSet i x t) =
      ENNReal.ofReal
        (leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have hEvent : MeasurableSet (leadingOnesFiniteFirstCrossingExactSet i x t) :=
    measurableSet_leadingOnesFiniteFirstCrossingExactSet i x
  change finiteTrajectoryMeasure P hP t x
      (leadingOnesFiniteFirstCrossingExactSet i x t) = _
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP t x]
  have hnonneg :
      ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory (BitString n) t)),
        0 ≤
          (if path ∈ leadingOnesFiniteFirstCrossingExactSet i x t then
            finiteTrajectoryWeight P t x path
          else 0) := by
    intro path _hpath
    by_cases hexact : path ∈ leadingOnesFiniteFirstCrossingExactSet i x t
    · simpa [hexact] using finiteTrajectoryWeight_nonneg P hP t x path
    · simp [hexact]
  calc
    (∑ path : FiniteTrajectory (BitString n) t,
        (leadingOnesFiniteFirstCrossingExactSet i x t).indicator
            (fun _ => (1 : ENNReal)) path *
          ENNReal.ofReal (finiteTrajectoryWeight P t x path)) =
        ∑ path : FiniteTrajectory (BitString n) t,
          ENNReal.ofReal
            (if path ∈ leadingOnesFiniteFirstCrossingExactSet i x t then
              finiteTrajectoryWeight P t x path
            else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hexact : path ∈ leadingOnesFiniteFirstCrossingExactSet i x t
      · simp [hexact]
      · simp [hexact]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory (BitString n) t,
          if path ∈ leadingOnesFiniteFirstCrossingExactSet i x t then
            finiteTrajectoryWeight P t x path
          else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal
        (leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x) := by
      rfl

/-- Infinite-path cylinder whose first crossing of boundary `i` occurs at time `t`
and lands exactly on score level `i`. -/
def leadingOnesTrajectoryFirstCrossingExactSet
    {n : ℕ} (i : Fin n) (x : BitString n) (t : ℕ) :
    Set (ℕ → BitString n) :=
  transitionTrajectoryTail t ⁻¹' leadingOnesFiniteFirstCrossingExactSet i x t

/-- Every exact-entry cylinder is measurable. -/
theorem measurableSet_leadingOnesTrajectoryFirstCrossingExactSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (i : Fin n) (x : BitString n) (t : ℕ) :
    MeasurableSet (leadingOnesTrajectoryFirstCrossingExactSet i x t) := by
  unfold leadingOnesTrajectoryFirstCrossingExactSet
  exact (measurableSet_leadingOnesFiniteFirstCrossingExactSet i x).preimage
    (measurable_transitionTrajectoryTail (α := BitString n) t)

/-- The genuine fixed-initial trajectory probability of exact entry at time `t` is the
already promoted fixed-initial exact-entry mass. -/
theorem leadingOnesTrajectoryMeasure_firstCrossingExactSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) (t : ℕ) :
    leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesTrajectoryFirstCrossingExactSet i x t) =
      ENNReal.ofReal
        (leadingOnesFixedInitialFirstCrossingExactMass (t := t) p i x) := by
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have htail : Measurable
      (transitionTrajectoryTail (α := BitString n) t) :=
    measurable_transitionTrajectoryTail (α := BitString n) t
  have hEvent : MeasurableSet (leadingOnesFiniteFirstCrossingExactSet i x t) :=
    measurableSet_leadingOnesFiniteFirstCrossingExactSet i x
  unfold leadingOnesTrajectoryMeasure leadingOnesTrajectoryFirstCrossingExactSet
  change transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail t ⁻¹' leadingOnesFiniteFirstCrossingExactSet i x t) = _
  rw [← Measure.map_apply htail hEvent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]
  exact finiteTrajectoryMeasure_leadingOnesFiniteFirstCrossingExactSet hp0 hp1 i x

/-- Absolute-time semantics of the exact-entry cylinder. -/
theorem mem_leadingOnesTrajectoryFirstCrossingExactSet_iff
    {n : ℕ} (i : Fin n) (x : BitString n)
    (t : ℕ) (path : ℕ → BitString n) :
    path ∈ leadingOnesTrajectoryFirstCrossingExactSet i x t ↔
      (∀ r, r < t →
        leadingOnes (transitionTrajectoryState x path r) < i.val) ∧
      leadingOnes (transitionTrajectoryState x path t) = i.val := by
  unfold leadingOnesTrajectoryFirstCrossingExactSet
  change
    (leadingOnesPreCrossing i t x (transitionTrajectoryTail t path) ∧
      leadingOnes
        (finiteTrajectoryTerminal t x (transitionTrajectoryTail t path)) = i.val) ↔ _
  rw [leadingOnesPreCrossing_transitionTrajectoryTail_iff i t x path]
  simp only [finiteTrajectoryTerminal_transitionTrajectoryTail]

/-- A pointwise nonincreasing natural potential is nonincreasing between arbitrary
ordered absolute times, not only adjacent times. -/
theorem potential_nonincreasingAlong_le_of_le
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    {s t : ℕ} (hst : s ≤ t) :
    V (transitionTrajectoryState x path t) ≤
      V (transitionTrajectoryState x path s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  induction d with
  | zero =>
      exact le_rfl
  | succ d ih =>
      have hstep := hmono (s + d)
      have hstep' :
          V (transitionTrajectoryState x path (s + (d + 1))) ≤
            V (transitionTrajectoryState x path (s + d)) := by
        simpa [Nat.add_assoc] using hstep
      exact le_trans hstep' (ih (by omega))

/-- Along a path whose canonical LeadingOnes distance potential is nonincreasing,
the LeadingOnes score is nondecreasing between arbitrary ordered times. -/
theorem leadingOnes_score_nondecreasingAlong_of_potential
    {n : ℕ} (x : BitString n) (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path)
    {s t : ℕ} (hst : s ≤ t) :
    leadingOnes (transitionTrajectoryState x path s) ≤
      leadingOnes (transitionTrajectoryState x path t) := by
  have hpot := potential_nonincreasingAlong_le_of_le
    (leadingOnesPotential (n := n)) x path hmono hst
  have hs := leadingOnes_le (transitionTrajectoryState x path s)
  have ht := leadingOnes_le (transitionTrajectoryState x path t)
  unfold leadingOnesPotential at hpot
  omega

/-- Two-time event representing a transition from strictly below score `i` at time `t`
to exact score `i` at time `t+1`. -/
def leadingOnesBelowThenExactAtNextSet
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ) :
    Set (ℕ → BitString n) :=
  {path |
    leadingOnes (transitionTrajectoryState x path t) < i.val ∧
      leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val}

/-- The below-to-exact two-time event is measurable. -/
theorem measurableSet_leadingOnesBelowThenExactAtNextSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (i : Fin n) (t : ℕ) :
    MeasurableSet (leadingOnesBelowThenExactAtNextSet x i t) := by
  have hbelow :
      MeasurableSet
        ({y : BitString n | leadingOnes y < i.val} : Set (BitString n)) :=
    ({y : BitString n | leadingOnes y < i.val} : Set (BitString n)).to_countable.measurableSet
  have hexact :
      MeasurableSet
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) :=
    ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)).to_countable.measurableSet
  change MeasurableSet
    ((fun path => transitionTrajectoryState x path t) ⁻¹'
        {y : BitString n | leadingOnes y < i.val} ∩
      (fun path => transitionTrajectoryState x path (t + 1)) ⁻¹'
        {y : BitString n | leadingOnes y = i.val})
  exact (hbelow.preimage (measurable_transitionTrajectoryState_fixed x t)).inter
    (hexact.preimage (measurable_transitionTrajectoryState_fixed x (t + 1)))

/-- On every potential-nonincreasing path, exact first entry at time `t+1` is exactly
one below-to-level transition at that time. -/
theorem leadingOnes_firstCrossingExact_succ_iff_belowThenExact_of_nonincreasing
    {n : ℕ} (x : BitString n) (i : Fin n) (t : ℕ)
    (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path) :
    path ∈ leadingOnesTrajectoryFirstCrossingExactSet i x (t + 1) ↔
      path ∈ leadingOnesBelowThenExactAtNextSet x i t := by
  rw [mem_leadingOnesTrajectoryFirstCrossingExactSet_iff]
  change
    ((∀ r, r < t + 1 →
        leadingOnes (transitionTrajectoryState x path r) < i.val) ∧
      leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val) ↔
    (leadingOnes (transitionTrajectoryState x path t) < i.val ∧
      leadingOnes (transitionTrajectoryState x path (t + 1)) = i.val)
  constructor
  · rintro ⟨hpre, hnext⟩
    exact ⟨hpre t (Nat.lt_succ_self t), hnext⟩
  · rintro ⟨ht, hnext⟩
    constructor
    · intro r hr
      have hrt : r ≤ t := by omega
      have hscore := leadingOnes_score_nondecreasingAlong_of_potential
        x path hmono hrt
      exact lt_of_le_of_lt hscore ht
    · exact hnext

/-- Under the genuine LeadingOnes law, the exact-entry cylinder at time `t+1` and the
below-to-level two-time event have the same probability. -/
theorem leadingOnesTrajectoryMeasure_firstCrossingExact_succ_eq_belowThenExact
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesTrajectoryFirstCrossingExactSet i x (t + 1)) =
      leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesBelowThenExactAtNextSet x i t) := by
  apply measure_congr
  filter_upwards [leadingOnesTrajectoryMeasure_ae_potentialNonincreasing
    p hp0 hp1 x] with path hmono
  exact propext (leadingOnes_firstCrossingExact_succ_iff_belowThenExact_of_nonincreasing
    x i t path hmono)

/-- Therefore the lower-score-to-exact-level branch at time `t+1` has exactly the
fixed-initial exact-entry mass used by the renewal equation. -/
theorem leadingOnesTrajectoryMeasure_belowThenExactAtNextSet_eq_exactEntryENNMass
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : BitString n) (i : Fin n) (t : ℕ) :
    leadingOnesTrajectoryMeasure p hp0 hp1 x
        (leadingOnesBelowThenExactAtNextSet x i t) =
      leadingOnesFixedInitialExactEntryENNMass p i x (t + 1) := by
  rw [← leadingOnesTrajectoryMeasure_firstCrossingExact_succ_eq_belowThenExact
    p hp0 hp1 x i t]
  exact leadingOnesTrajectoryMeasure_firstCrossingExactSet
    hp0 hp1 i x (t + 1)

end ECRuntime
