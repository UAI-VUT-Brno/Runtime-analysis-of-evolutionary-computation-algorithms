import ECRuntime.LevelCharges
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 26 fix 21: contiguous residence intervals for monotone fitness levels

Stage 26 fix 20 compiler-verifies the deterministic charge decomposition

  `T_{V=0} <= sum_i trajectoryLevelCharge i`.

The remaining multi-level theorem must control each charge by a fresh geometric
comparison coordinate.  For an elitist fitness-level process the required structural
fact is that visits to one exact positive potential value cannot disappear and later
return: a nonincreasing natural-valued potential visits every exact level in one
contiguous time interval.

This file isolates that deterministic fact before any probabilistic coupling is
constructed.  For a visited coordinate `i : Fin m`, it defines the first absolute
entry time into potential value `i+1`.  If that level is eventually left downward, it
also defines the first drop time after the entry and proves the exact pointwise
classification

* before the entry, the level indicator is zero;
* from the entry up to (but excluding) the first drop, the indicator is one;
* from the first drop onward, the indicator is zero.

Thus the support of a positive-level charge is a single residence window.  A later
module can sum this classification to identify the complete charge with the residence
length and can then couple that residence time to the one-level geometric comparison
already verified in `LevelExitDomination.lean`.
-/

/-- A nonincreasing potential cannot rise over any finite offset. -/
theorem potential_le_offset_of_nonincreasingAlong
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (s d : ℕ) :
    V (transitionTrajectoryState x path (s + d)) ≤
      V (transitionTrajectoryState x path s) := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := hmono (s + d)
      have htrans :
          V (transitionTrajectoryState x path ((s + d) + 1)) ≤
            V (transitionTrajectoryState x path s) :=
        hstep.trans ih
      simpa [Nat.add_assoc] using htrans

/-- A nonincreasing potential cannot rise between arbitrary ordered absolute times. -/
theorem potential_le_of_nonincreasingAlong
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    {s t : ℕ} (hst : s ≤ t) :
    V (transitionTrajectoryState x path t) ≤
      V (transitionTrajectoryState x path s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  exact potential_le_offset_of_nonincreasingAlong V x path hmono s d

/-- If a nonincreasing potential has the same value at two times, it has that value
at every intermediate time. -/
theorem potential_eq_between_equal_values_of_nonincreasingAlong
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    {a b c k : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (ha : V (transitionTrajectoryState x path a) = k)
    (hc : V (transitionTrajectoryState x path c) = k) :
    V (transitionTrajectoryState x path b) = k := by
  have hba := potential_le_of_nonincreasingAlong V x path hmono hab
  have hcb := potential_le_of_nonincreasingAlong V x path hmono hbc
  omega

/-- Once a nonincreasing potential is strictly below `k`, it stays strictly below
`k` at every later time. -/
theorem potential_lt_persists_of_nonincreasingAlong
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    {s t k : ℕ} (hst : s ≤ t)
    (hs : V (transitionTrajectoryState x path s) < k) :
    V (transitionTrajectoryState x path t) < k := by
  have hle := potential_le_of_nonincreasingAlong V x path hmono hst
  omega

/-- First absolute time at which a supplied trajectory visits the exact positive
level represented by `i`.  The existence witness is explicit so no artificial default
entry time is introduced for skipped levels. -/
def firstExactLevelEntryTime
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1) : ℕ :=
  Nat.find hvisit

/-- The first-entry time really visits the requested exact level. -/
theorem firstExactLevelEntryTime_spec
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1) :
    V (transitionTrajectoryState x path
      (firstExactLevelEntryTime V x path i hvisit)) = i.val + 1 := by
  unfold firstExactLevelEntryTime
  exact Nat.find_spec hvisit

/-- No earlier time visits the requested exact level. -/
theorem firstExactLevelEntryTime_minimal
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    {t : ℕ} (ht : t < firstExactLevelEntryTime V x path i hvisit) :
    V (transitionTrajectoryState x path t) ≠ i.val + 1 := by
  unfold firstExactLevelEntryTime at ht
  exact Nat.find_min hvisit ht

/-- The positive-level indicator vanishes strictly before the first entry. -/
theorem positiveLevelIndicator_eq_zero_before_firstExactLevelEntryTime
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    {t : ℕ} (ht : t < firstExactLevelEntryTime V x path i hvisit) :
    positiveLevelIndicator (V (transitionTrajectoryState x path t)) i = 0 := by
  have hne := firstExactLevelEntryTime_minimal V x path i hvisit ht
  simp [positiveLevelIndicator, hne]

/-- Every finite prefix ending no later than the first level entry has zero charge for
that level. -/
theorem finiteHorizonLevelCharge_eq_zero_before_firstExactLevelEntryTime
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (T : ℕ) (hT : T ≤ firstExactLevelEntryTime V x path i hvisit) :
    finiteHorizonLevelCharge V x path T i = 0 := by
  classical
  unfold finiteHorizonLevelCharge
  apply Finset.sum_eq_zero
  intro t ht
  have htT : t < T := Finset.mem_range.mp ht
  have htEntry : t < firstExactLevelEntryTime V x path i hvisit :=
    lt_of_lt_of_le htT hT
  exact positiveLevelIndicator_eq_zero_before_firstExactLevelEntryTime
    V x path i hvisit htEntry

/-- First absolute time, at or after the first entry into level `i+1`, at which the
potential is strictly smaller than `i+1`.  Again the existence witness is explicit:
levels on which the trajectory remains forever are handled separately by the later
coupling construction. -/
def firstExactLevelDropTime
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1) : ℕ :=
  Nat.find hdrop

/-- The first drop time is after the entry and is genuinely below the level. -/
theorem firstExactLevelDropTime_spec
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1) :
    firstExactLevelEntryTime V x path i hvisit ≤
        firstExactLevelDropTime V x path i hvisit hdrop ∧
      V (transitionTrajectoryState x path
        (firstExactLevelDropTime V x path i hvisit hdrop)) < i.val + 1 := by
  unfold firstExactLevelDropTime
  exact Nat.find_spec hdrop

/-- Before the first drop time there is no time at or after entry whose potential is
already strictly below the level. -/
theorem firstExactLevelDropTime_minimal
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1)
    {t : ℕ} (ht : t < firstExactLevelDropTime V x path i hvisit hdrop) :
    ¬ (firstExactLevelEntryTime V x path i hvisit ≤ t ∧
      V (transitionTrajectoryState x path t) < i.val + 1) := by
  unfold firstExactLevelDropTime at ht
  exact Nat.find_min hdrop ht

/-- A genuine drop happens strictly after the first level entry. -/
theorem firstExactLevelEntryTime_lt_firstExactLevelDropTime
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1) :
    firstExactLevelEntryTime V x path i hvisit <
      firstExactLevelDropTime V x path i hvisit hdrop := by
  have hspec := firstExactLevelDropTime_spec V x path i hvisit hdrop
  have hentry := firstExactLevelEntryTime_spec V x path i hvisit
  have hne :
      firstExactLevelEntryTime V x path i hvisit ≠
        firstExactLevelDropTime V x path i hvisit hdrop := by
    intro heq
    have hlt := hspec.2
    rw [← heq, hentry] at hlt
    exact (Nat.lt_irrefl (i.val + 1)) hlt
  exact lt_of_le_of_ne hspec.1 hne

/-- Under potential monotonicity, every time from the first entry up to but excluding
the first drop remains exactly on the same level. -/
theorem potential_eq_level_between_firstEntry_and_firstDrop
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1)
    {t : ℕ}
    (hEntryT : firstExactLevelEntryTime V x path i hvisit ≤ t)
    (hTDrop : t < firstExactLevelDropTime V x path i hvisit hdrop) :
    V (transitionTrajectoryState x path t) = i.val + 1 := by
  have hle := potential_le_of_nonincreasingAlong
    V x path hmono hEntryT
  have hentry := firstExactLevelEntryTime_spec V x path i hvisit
  have hnot := firstExactLevelDropTime_minimal
    V x path i hvisit hdrop hTDrop
  have hnotlt : ¬ V (transitionTrajectoryState x path t) < i.val + 1 := by
    intro hlt
    exact hnot ⟨hEntryT, hlt⟩
  omega

/-- On the residence window `[entry, drop)`, the positive-level indicator is exactly
one. -/
theorem positiveLevelIndicator_eq_one_between_firstEntry_and_firstDrop
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1)
    {t : ℕ}
    (hEntryT : firstExactLevelEntryTime V x path i hvisit ≤ t)
    (hTDrop : t < firstExactLevelDropTime V x path i hvisit hdrop) :
    positiveLevelIndicator (V (transitionTrajectoryState x path t)) i = 1 := by
  have ht := potential_eq_level_between_firstEntry_and_firstDrop
    V x path hmono i hvisit hdrop hEntryT hTDrop
  simp [positiveLevelIndicator, ht]

/-- Once the first downward exit from an exact level occurs, monotonicity prevents any
later return to that level. -/
theorem positiveLevelIndicator_eq_zero_after_firstExactLevelDropTime
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1)
    {t : ℕ}
    (hDropT : firstExactLevelDropTime V x path i hvisit hdrop ≤ t) :
    positiveLevelIndicator (V (transitionTrajectoryState x path t)) i = 0 := by
  have hspec := firstExactLevelDropTime_spec V x path i hvisit hdrop
  have hlt := potential_lt_persists_of_nonincreasingAlong
    V x path hmono hDropT hspec.2
  have hne : V (transitionTrajectoryState x path t) ≠ i.val + 1 := by
    omega
  simp [positiveLevelIndicator, hne]

/-- One-hot indicator of a deterministic residence window `[entry, drop)`. -/
def residenceWindowIndicator (entry drop t : ℕ) : ENNReal :=
  if entry ≤ t ∧ t < drop then 1 else 0

/-- Exact pointwise residence-window characterization of a visited and eventually
left positive level. -/
theorem positiveLevelIndicator_eq_residenceWindowIndicator
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1)
    (t : ℕ) :
    positiveLevelIndicator (V (transitionTrajectoryState x path t)) i =
      residenceWindowIndicator
        (firstExactLevelEntryTime V x path i hvisit)
        (firstExactLevelDropTime V x path i hvisit hdrop) t := by
  by_cases hBefore : t < firstExactLevelEntryTime V x path i hvisit
  · have hleft := positiveLevelIndicator_eq_zero_before_firstExactLevelEntryTime
      V x path i hvisit hBefore
    have hnotWindow :
        ¬ (firstExactLevelEntryTime V x path i hvisit ≤ t ∧
          t < firstExactLevelDropTime V x path i hvisit hdrop) := by
      intro h
      omega
    rw [hleft]
    simp [residenceWindowIndicator, hnotWindow]
  · have hEntryT : firstExactLevelEntryTime V x path i hvisit ≤ t :=
      Nat.le_of_not_gt hBefore
    by_cases hTDrop : t < firstExactLevelDropTime V x path i hvisit hdrop
    · have hleft := positiveLevelIndicator_eq_one_between_firstEntry_and_firstDrop
        V x path hmono i hvisit hdrop hEntryT hTDrop
      rw [hleft]
      simp [residenceWindowIndicator, hEntryT, hTDrop]
    · have hDropT : firstExactLevelDropTime V x path i hvisit hdrop ≤ t :=
        Nat.le_of_not_gt hTDrop
      have hleft := positiveLevelIndicator_eq_zero_after_firstExactLevelDropTime
        V x path hmono i hvisit hdrop hDropT
      rw [hleft]
      simp [residenceWindowIndicator, hTDrop]

/-- Natural length of the exact-level residence window. -/
def exactLevelResidenceLength
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1) : ℕ :=
  firstExactLevelDropTime V x path i hvisit hdrop -
    firstExactLevelEntryTime V x path i hvisit

/-- A visited level that is eventually left has a strictly positive residence length. -/
theorem exactLevelResidenceLength_pos
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m)
    (hvisit : ∃ t, V (transitionTrajectoryState x path t) = i.val + 1)
    (hdrop : ∃ t,
      firstExactLevelEntryTime V x path i hvisit ≤ t ∧
        V (transitionTrajectoryState x path t) < i.val + 1) :
    0 < exactLevelResidenceLength V x path i hvisit hdrop := by
  unfold exactLevelResidenceLength
  have hlt := firstExactLevelEntryTime_lt_firstExactLevelDropTime
    V x path i hvisit hdrop
  omega

end ECRuntime
