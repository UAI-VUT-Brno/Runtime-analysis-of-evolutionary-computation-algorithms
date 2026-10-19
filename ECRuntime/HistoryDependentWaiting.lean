import ECRuntime.AdaptiveLevelSupport
import Mathlib

namespace ECRuntime

/-!
# Stage 26 fix 31: history-dependent first-success residence bounds

Fix 30 compiler-verifies the one-step support fact for the adaptive Bernoulli-vector
coupling: while the real state is in exact positive level `i+1`, a positive-weight
transition carrying `true` in coordinate `i` cannot remain in that exact level.
`LevelResidence.lean` independently compiler-verifies that a nonincreasing potential
visits every exact positive level in one contiguous interval.

This module joins those two deterministic interfaces without yet constructing the
infinite joint measure.  An infinite Boolean-vector stream is indexed by transition
time: `labels t` is the vector attached to the transition from absolute state time `t`
to time `t+1`.  For a visited level we define the first success offset of its coordinate
starting at the *actual* first entry time.  The corresponding one-based waiting time is
`offset + 1`.

Under positive adaptive coupled-step support and potential nonincrease, the first such
success forces a downward level drop no later than the end of that transition.  Hence the
exact residence length is bounded by the one-based first-success waiting time.  The main
endpoint also constructs the drop witness from the success itself, so the statement does
not assume eventual exit circularly.

The remaining probabilistic task is deliberately left to a later slice: prove that the
positive-step support property holds almost surely under the infinite coupled law and
prove that each coordinate stream remains fresh after its history-dependent first-entry
time.  Only after that freshness theorem should the waiting vector be identified with the
independent geometric product.
-/

/-- Pathwise support condition for an infinite adaptive coupled trajectory.

`labels t` is the Boolean vector emitted on the transition from absolute state time `t`
to `t+1`.  This predicate records exactly the positivity premise needed to turn the
one-step zero-weight theorem from fix 30 into a pathwise support statement. -/
def HasPositiveAdaptiveCoupledStepSupport
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) : Prop :=
  ∀ t : ℕ,
    0 < multiLevelBernoulliCoupledStepWeight
      P V hbound p
      (transitionTrajectoryState x path t)
      (transitionTrajectoryState x path (t + 1))
      (labels t)

/-- On a path satisfying positive coupled-step support, success of the coordinate
representing the current exact level forces the next state out of that level. -/
theorem comparisonSuccessForcesExactLevelExit_of_positiveAdaptiveCoupledStepSupport
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport P V hbound p x path labels)
    (t : ℕ) (i : Fin m)
    (hx : transitionTrajectoryState x path t ∈ exactPositivePotentialLevel V i)
    (hbit : labels t i = true) :
    transitionTrajectoryState x path (t + 1) ∉ exactPositivePotentialLevel V i := by
  exact multiLevelBernoulliCoupledStepWeight_active_success_forces_exactLevel_exit
    P V hbound p i
    (transitionTrajectoryState x path t)
    (transitionTrajectoryState x path (t + 1))
    (labels t) hx hbit (hsupport t)

/-- Zero-based offset of the first success of coordinate `i`, starting at the actual
first entry time into exact level `i+1`.

A success at offset `r` labels the transition from state time `entry+r` to
`entry+r+1`; therefore the EC waiting time associated with this success is `r+1`. -/
def firstComparisonSuccessOffsetAfterEntry
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) : ℕ :=
  Nat.find hsucc

/-- The selected first-success offset is genuinely a success. -/
theorem firstComparisonSuccessOffsetAfterEntry_spec
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) :
    labels
      (firstExactLevelEntryTime V x path i hvisit +
        firstComparisonSuccessOffsetAfterEntry
          V x path labels i hvisit hsucc) i = true := by
  unfold firstComparisonSuccessOffsetAfterEntry
  exact Nat.find_spec hsucc

/-- Every smaller offset fails the first-success predicate. -/
theorem firstComparisonSuccessOffsetAfterEntry_minimal
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true)
    {r : ℕ}
    (hr : r < firstComparisonSuccessOffsetAfterEntry
      V x path labels i hvisit hsucc) :
    labels (firstExactLevelEntryTime V x path i hvisit + r) i ≠ true := by
  unfold firstComparisonSuccessOffsetAfterEntry at hr
  exact Nat.find_min hsucc hr

/-- Before the first selected success, the Boolean coordinate is `false`. -/
theorem firstComparisonSuccessOffsetAfterEntry_eq_false_of_lt
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true)
    {r : ℕ}
    (hr : r < firstComparisonSuccessOffsetAfterEntry
      V x path labels i hvisit hsucc) :
    labels (firstExactLevelEntryTime V x path i hvisit + r) i = false := by
  have hne := firstComparisonSuccessOffsetAfterEntry_minimal
    V x path labels i hvisit hsucc hr
  cases hbit : labels (firstExactLevelEntryTime V x path i hvisit + r) i with
  | false => rfl
  | true => exact (hne hbit).elim

/-- One-based waiting time from actual level entry to the first coordinate success. -/
def firstComparisonSuccessWaitingAfterEntry
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (labels : ℕ → (Fin m → Bool)) (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) : ℕ :=
  firstComparisonSuccessOffsetAfterEntry V x path labels i hvisit hsucc + 1

/-- The first success after actual entry produces a genuine downward-drop witness no
later than the end of the successful transition.

There are two cases.  The real trajectory may already have dropped before the selected
coordinate success, in which case the current state itself is a drop witness.  Otherwise
the current state is still exactly on level `i+1`; fix 30 then forces the next state out
of that exact level, and potential nonincrease upgrades "not equal" to a strict drop. -/
theorem exists_exactLevelDrop_bounded_by_firstComparisonSuccess
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : ℕ → (Fin m → Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport P V hbound p x path labels)
    (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) :
    ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
      t ≤ firstExactLevelEntryTime V x path i hvisit +
        firstComparisonSuccessOffsetAfterEntry
          V x path labels i hvisit hsucc + 1 ∧
      V (transitionTrajectoryState x path t) < i.val + 1 := by
  let entry : ℕ := firstExactLevelEntryTime V x path i hvisit
  let r : ℕ := firstComparisonSuccessOffsetAfterEntry
    V x path labels i hvisit hsucc
  change ∃ t,
    entry ≤ t ∧
    t ≤ entry + r + 1 ∧
    V (transitionTrajectoryState x path t) < i.val + 1

  have hentryVal :
      V (transitionTrajectoryState x path entry) = i.val + 1 := by
    simpa [entry] using firstExactLevelEntryTime_spec V x path i hvisit

  have hbit : labels (entry + r) i = true := by
    simpa [entry, r] using
      firstComparisonSuccessOffsetAfterEntry_spec
        V x path labels i hvisit hsucc

  have hcurrentLe :
      V (transitionTrajectoryState x path (entry + r)) ≤ i.val + 1 := by
    calc
      V (transitionTrajectoryState x path (entry + r)) ≤
          V (transitionTrajectoryState x path entry) :=
        potential_le_of_nonincreasingAlong V x path hmono (by omega)
      _ = i.val + 1 := hentryVal

  by_cases hcurrentEq :
      V (transitionTrajectoryState x path (entry + r)) = i.val + 1
  · have hcurrentMem :
        transitionTrajectoryState x path (entry + r) ∈
          exactPositivePotentialLevel V i :=
      (mem_exactPositivePotentialLevel V i _).2 hcurrentEq
    have hexit :=
      comparisonSuccessForcesExactLevelExit_of_positiveAdaptiveCoupledStepSupport
        P V hbound p x path labels hsupport (entry + r) i hcurrentMem hbit
    have hnextNe :
        V (transitionTrajectoryState x path (entry + r + 1)) ≠ i.val + 1 := by
      intro hnextEq
      apply hexit
      exact (mem_exactPositivePotentialLevel V i _).2 hnextEq
    have hnextLe :
        V (transitionTrajectoryState x path (entry + r + 1)) ≤ i.val + 1 := by
      calc
        V (transitionTrajectoryState x path (entry + r + 1)) ≤
            V (transitionTrajectoryState x path (entry + r)) := hmono (entry + r)
        _ = i.val + 1 := hcurrentEq
    have hnextLt :
        V (transitionTrajectoryState x path (entry + r + 1)) < i.val + 1 :=
      lt_of_le_of_ne hnextLe hnextNe
    refine ⟨entry + r + 1, ?_, le_rfl, hnextLt⟩
    omega
  · have hcurrentLt :
        V (transitionTrajectoryState x path (entry + r)) < i.val + 1 :=
      lt_of_le_of_ne hcurrentLe hcurrentEq
    refine ⟨entry + r, ?_, ?_, hcurrentLt⟩ <;> omega

/-- In particular, positive coupled-step support plus a first coordinate success is
enough to prove that the visited exact level is eventually left downward. -/
theorem exists_exactLevelDrop_of_firstComparisonSuccess
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : ℕ → (Fin m → Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport P V hbound p x path labels)
    (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) :
    ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
      V (transitionTrajectoryState x path t) < i.val + 1 := by
  obtain ⟨t, hentry, _hboundT, hlt⟩ :=
    exists_exactLevelDrop_bounded_by_firstComparisonSuccess
      P V hbound p x path hmono labels hsupport i hvisit hsucc
  exact ⟨t, hentry, hlt⟩

/-- For any supplied proof that the level is eventually left, its canonical first-drop
time is no later than the transition carrying the first success after actual entry. -/
theorem firstExactLevelDropTime_le_firstComparisonSuccessBoundary
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : ℕ → (Fin m → Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport P V hbound p x path labels)
    (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
      V (transitionTrajectoryState x path t) < i.val + 1) :
    firstExactLevelDropTime V x path i hvisit hdrop ≤
      firstExactLevelEntryTime V x path i hvisit +
        firstComparisonSuccessOffsetAfterEntry
          V x path labels i hvisit hsucc + 1 := by
  let entry : ℕ := firstExactLevelEntryTime V x path i hvisit
  let r : ℕ := firstComparisonSuccessOffsetAfterEntry
    V x path labels i hvisit hsucc
  change firstExactLevelDropTime V x path i hvisit hdrop ≤ entry + r + 1
  have hbounded := exists_exactLevelDrop_bounded_by_firstComparisonSuccess
    P V hbound p x path hmono labels hsupport i hvisit hsucc
  change ∃ t,
    entry ≤ t ∧
    t ≤ entry + r + 1 ∧
    V (transitionTrajectoryState x path t) < i.val + 1 at hbounded
  obtain ⟨t, hentryT, htBound, hlt⟩ := hbounded
  by_contra hnot
  have hBoundLtDrop :
      entry + r + 1 < firstExactLevelDropTime V x path i hvisit hdrop := by
    omega
  have htLtDrop : t < firstExactLevelDropTime V x path i hvisit hdrop :=
    lt_of_le_of_lt htBound hBoundLtDrop
  have hminimal := firstExactLevelDropTime_minimal
    V x path i hvisit hdrop htLtDrop
  exact hminimal ⟨hentryT, hlt⟩

/-- Pathwise residence-time bound at an actual history-dependent level entry.

The left side counts state times in the contiguous interval `[entry, drop)`.  The right
side is the one-based number of Bernoulli comparisons up to and including the first
success of coordinate `i` starting at `entry`. -/
theorem exactLevelResidenceLength_le_firstComparisonSuccessWaitingAfterEntry
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : ℕ → (Fin m → Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport P V hbound p x path labels)
    (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
      V (transitionTrajectoryState x path t) < i.val + 1) :
    exactLevelResidenceLength V x path i hvisit hdrop ≤
      firstComparisonSuccessWaitingAfterEntry
        V x path labels i hvisit hsucc := by
  unfold exactLevelResidenceLength firstComparisonSuccessWaitingAfterEntry
  have hdropLe := firstExactLevelDropTime_le_firstComparisonSuccessBoundary
    P V hbound p x path hmono labels hsupport i hvisit hsucc hdrop
  omega

/-- Non-circular endpoint: the first comparison success simultaneously supplies an
actual drop witness and a proof that the resulting residence length is bounded by the
one-based first-success waiting time. -/
theorem exists_exactLevelDrop_with_residence_bound
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ z, V z ≤ m)
    (p : Fin m → ℝ)
    (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (labels : ℕ → (Fin m → Bool))
    (hsupport : HasPositiveAdaptiveCoupledStepSupport P V hbound p x path labels)
    (i : Fin m)
    (hvisit : ∃ t,
      V (transitionTrajectoryState x path t) = i.val + 1)
    (hsucc : ∃ r,
      labels (firstExactLevelEntryTime V x path i hvisit + r) i = true) :
    ∃ hdrop : (∃ t,
        firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1),
      exactLevelResidenceLength V x path i hvisit hdrop ≤
        firstComparisonSuccessWaitingAfterEntry
          V x path labels i hvisit hsucc := by
  let hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
      V (transitionTrajectoryState x path t) < i.val + 1 :=
    exists_exactLevelDrop_of_firstComparisonSuccess
      P V hbound p x path hmono labels hsupport i hvisit hsucc
  refine ⟨hdrop, ?_⟩
  exact exactLevelResidenceLength_le_firstComparisonSuccessWaitingAfterEntry
    P V hbound p x path hmono labels hsupport i hvisit hsucc hdrop

end ECRuntime
