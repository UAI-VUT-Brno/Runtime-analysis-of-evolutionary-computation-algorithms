import ECRuntime.LevelExitDomination
import ECRuntime.CouplingDomination
import ECRuntime.FitnessLevel
import Mathlib

open scoped BigOperators ENNReal
open Finset

namespace ECRuntime

/-!
# Stage 26 fix 20: bounded level charges on complete trajectories

Fixes 15--17 close the one-level distributional argument: a uniform lower bound on
leaving a level gives a geometric tail bound, and hence natural-threshold stochastic
domination by the canonical geometric waiting law, uniformly over every possible
entry state.

The remaining theorem is genuinely multi-level.  Before constructing the adaptive
coupling, this module isolates the deterministic bookkeeping that the coupling must
control.  Fix 20 is a compiler-focused repair of the fix-19 implementation; it does
not change the mathematical charge interface.  The fix-19 compiler review reached the
first `ENNReal` finite-sum definition and required it to be marked `noncomputable`.
A natural-valued potential `V` is assumed globally bounded by `m`; positive value `i+1`
is represented by coordinate `i : Fin m`.

For a complete trajectory we define

* `finiteHorizonLevelCharge`: the number (as an `ENNReal`) of times before a finite
  horizon at which the trajectory occupies one specified positive level;
* `trajectoryLevelCharge`: the supremum of these finite-horizon charges.

The positive levels form a one-hot partition whenever the potential is nonzero and
bounded by `m`.  Consequently every finite prefix before the first zero-potential
state is exactly partitioned by these charges.  Taking the Stage-24 supremum of
truncated hitting costs then yields the pathwise inequality

  `T_{V=0} <= sum_i trajectoryLevelCharge i`.

This is precisely the deterministic `hXW` obligation required by
`CouplingDomination.lean`.  No probabilistic independence is asserted here.  A later
module may use potential monotonicity to identify each nonzero charge with the single
contiguous residence interval of that level and couple that interval to a fresh
geometric coordinate.
-/

/-- One-hot `ENNReal` indicator for the positive level represented by `i : Fin m`.
Coordinate `i` corresponds to natural potential value `i+1`. -/
def positiveLevelIndicator {m : ℕ} (k : ℕ) (i : Fin m) : ENNReal :=
  if k = i.val + 1 then 1 else 0

/-- A positive value `k <= m` belongs to exactly one of the `m` positive level
coordinates. -/
theorem sum_positiveLevelIndicator_eq_one
    {m k : ℕ} (hkpos : 0 < k) (hkm : k ≤ m) :
    (∑ i : Fin m, positiveLevelIndicator k i) = 1 := by
  classical
  let i0 : Fin m := ⟨k - 1, by omega⟩
  have hi0 : k = i0.val + 1 := by
    dsimp [i0]
    omega
  calc
    (∑ i : Fin m, positiveLevelIndicator k i) =
        positiveLevelIndicator k i0 := by
      apply Fintype.sum_eq_single i0
      intro j hji
      unfold positiveLevelIndicator
      rw [if_neg]
      intro hkj
      apply hji
      apply Fin.ext
      dsimp [i0]
      omega
    _ = 1 := by simp [positiveLevelIndicator, hi0]

/-- Charge accumulated by positive level `i+1` during absolute times
`0, ..., T-1`. -/
noncomputable def finiteHorizonLevelCharge
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (T : ℕ) (i : Fin m) : ENNReal :=
  Finset.sum (Finset.range T) (fun t =>
    positiveLevelIndicator (V (transitionTrajectoryState x path t)) i)

@[simp] theorem finiteHorizonLevelCharge_zero
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (i : Fin m) :
    finiteHorizonLevelCharge V x path 0 i = 0 := by
  simp [finiteHorizonLevelCharge]

/-- The full charge of a positive level is the supremum of its finite-horizon visit
counts.  It may be `⊤` if that level is occupied infinitely often. -/
noncomputable def trajectoryLevelCharge
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (i : Fin m) (path : ℕ → α) : ENNReal :=
  ⨆ T : ℕ, finiteHorizonLevelCharge V x path T i

/-- Every finite-horizon charge is bounded by the corresponding complete-trajectory
charge. -/
theorem finiteHorizonLevelCharge_le_trajectoryLevelCharge
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (T : ℕ) (i : Fin m) :
    finiteHorizonLevelCharge V x path T i ≤
      trajectoryLevelCharge V x i path := by
  exact le_iSup (fun U : ℕ => finiteHorizonLevelCharge V x path U i) T

/-- If every state in a finite prefix has a positive potential bounded by `m`, then
that prefix is partitioned exactly by the `m` positive level charges. -/
theorem sum_finiteHorizonLevelCharge_eq_natCast
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (T : ℕ)
    (hpos : ∀ t, t < T → 0 < V (transitionTrajectoryState x path t))
    (hbound : ∀ t, t < T → V (transitionTrajectoryState x path t) ≤ m) :
    (∑ i : Fin m, finiteHorizonLevelCharge V x path T i) =
      (T : ENNReal) := by
  classical
  unfold finiteHorizonLevelCharge
  rw [Finset.sum_comm]
  calc
    (Finset.sum (Finset.range T) (fun t =>
        ∑ i : Fin m,
          positiveLevelIndicator (V (transitionTrajectoryState x path t)) i)) =
        Finset.sum (Finset.range T) (fun _t => (1 : ENNReal)) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htT : t < T := Finset.mem_range.mp ht
      exact sum_positiveLevelIndicator_eq_one
        (hpos t htT) (hbound t htT)
    _ = (T : ENNReal) := by simp

/-- A finite-prefix total charge is bounded by the sum of the complete-trajectory
charges. -/
theorem sum_finiteHorizonLevelCharge_le_finiteRuntimeSum_trajectoryLevelCharge
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α) (T : ℕ) :
    (∑ i : Fin m, finiteHorizonLevelCharge V x path T i) ≤
      finiteRuntimeSum (m := m)
        (fun (i : Fin m) (path' : Nat -> α) => trajectoryLevelCharge (m := m) V x i path') path := by
  unfold finiteRuntimeSum
  exact Finset.sum_le_sum (fun i _ =>
    finiteHorizonLevelCharge_le_trajectoryLevelCharge V x path T i)

/--
Pathwise level-charge decomposition required by the coupling bridge.

If `V` takes values in `0,...,m`, then the conventional hitting time of the zero
potential is at most the sum of the complete positive-level charges.  The proof does
not yet need monotonicity: before the *first* zero every visited state has positive
potential, while visits after the first zero can only increase the right-hand side.
For a monotone elitist potential, those extra visits do not occur and the charges are
the usual single residence intervals.
-/
theorem transitionTrajectoryFirstHittingTime_le_levelChargeSum
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (hbound : ∀ y, V y ≤ m)
    (x : α) (path : ℕ → α) :
    transitionTrajectoryFirstHittingTime (potentialTarget V) x path ≤
      finiteRuntimeSum (m := m)
        (fun (i : Fin m) (path' : Nat -> α) => trajectoryLevelCharge (m := m) V x i path') path := by
  classical
  rw [transitionTrajectoryFirstHittingTime_eq_transitionTrajectoryHittingTime]
  unfold transitionTrajectoryHittingTime
  apply iSup_le
  intro T
  by_cases hhit : ∃ k, transitionTrajectoryState x path k ∈ potentialTarget V
  · let k : ℕ := Nat.find hhit
    have hkHit : transitionTrajectoryState x path k ∈ potentialTarget V := by
      dsimp [k]
      exact Nat.find_spec hhit
    have hkBefore : ∀ j, j < k →
        transitionTrajectoryState x path j ∉ potentialTarget V := by
      intro j hj
      simpa [k] using Nat.find_min hhit hj
    rw [transitionTrajectoryTruncatedHittingCost_eq_min_of_first_hit
      (potentialTarget V) x path k T hkHit hkBefore]
    have hprefix :
        (∑ i : Fin m,
            finiteHorizonLevelCharge V x path (Nat.min k T) i) =
          (Nat.min k T : ENNReal) := by
      apply sum_finiteHorizonLevelCharge_eq_natCast V x path (Nat.min k T)
      · intro t ht
        have htk : t < k := lt_of_lt_of_le ht (Nat.min_le_left k T)
        have hnot := hkBefore t htk
        have hne : V (transitionTrajectoryState x path t) ≠ 0 := by
          simpa [potentialTarget] using hnot
        exact Nat.pos_of_ne_zero hne
      · intro t _ht
        exact hbound (transitionTrajectoryState x path t)
    have hnatCast (n : Nat) :
        ENNReal.ofReal (n : Real) = (n : ENNReal) := by
      simp
    calc
      ENNReal.ofReal (Nat.min k T : Real) = (Nat.min k T : ENNReal) :=
        hnatCast (Nat.min k T)
      _ = ∑ i : Fin m,
          finiteHorizonLevelCharge V x path (Nat.min k T) i := hprefix.symm
      _ ≤ finiteRuntimeSum (m := m)
          (fun (i : Fin m) (path' : Nat -> α) => trajectoryLevelCharge (m := m) V x i path') path :=
        sum_finiteHorizonLevelCharge_le_finiteRuntimeSum_trajectoryLevelCharge
          V x path (Nat.min k T)
  · have hnever : ∀ k,
        transitionTrajectoryState x path k ∉ potentialTarget V := by
      intro k hk
      exact hhit ⟨k, hk⟩
    rw [transitionTrajectoryTruncatedHittingCost_eq_horizon_of_never_hits
      (potentialTarget V) x path hnever T]
    have hprefix :
        (∑ i : Fin m, finiteHorizonLevelCharge V x path T i) =
          (T : ENNReal) := by
      apply sum_finiteHorizonLevelCharge_eq_natCast V x path T
      · intro t ht
        have hnot := hnever t
        have hne : V (transitionTrajectoryState x path t) ≠ 0 := by
          simpa [potentialTarget] using hnot
        exact Nat.pos_of_ne_zero hne
      · intro t _ht
        exact hbound (transitionTrajectoryState x path t)
    calc
      ENNReal.ofReal (T : ℝ) = (T : ENNReal) := by simp
      _ = ∑ i : Fin m, finiteHorizonLevelCharge V x path T i := hprefix.symm
      _ ≤ finiteRuntimeSum (m := m)
          (fun (i : Fin m) (path' : Nat -> α) => trajectoryLevelCharge (m := m) V x i path') path :=
        sum_finiteHorizonLevelCharge_le_finiteRuntimeSum_trajectoryLevelCharge
          V x path T

/-- Pointwise nonincrease of a natural potential along a supplied complete trajectory. -/
def IsPotentialNonincreasingAlong
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α) : Prop :=
  ∀ t, V (transitionTrajectoryState x path (t + 1)) ≤
    V (transitionTrajectoryState x path t)

/-- Once a nonincreasing natural potential reaches zero, it stays zero forever along
that trajectory. -/
theorem potential_zero_persists_of_nonincreasing
    {α : Type*} (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    {k j : ℕ} (hkj : k ≤ j)
    (hk : V (transitionTrajectoryState x path k) = 0) :
    V (transitionTrajectoryState x path j) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  induction d with
  | zero => simpa using hk
  | succ d ih =>
      have hstep := hmono (k + d)
      have hprev : V (transitionTrajectoryState x path (k + d)) = 0 :=
        ih (by omega)
      have hnext :
          V (transitionTrajectoryState x path ((k + d) + 1)) = 0 := by
        omega
      simpa [Nat.add_assoc] using hnext

/-- Under potential monotonicity, a state strictly after the first zero-potential time
cannot contribute to any positive-level charge.  This records the intended residence-
charge semantics used by the upcoming adaptive coupling. -/
theorem positiveLevelIndicator_eq_zero_after_zero_of_nonincreasing
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    {k t : ℕ} (hkt : k ≤ t)
    (hk : V (transitionTrajectoryState x path k) = 0)
    (i : Fin m) :
    positiveLevelIndicator (V (transitionTrajectoryState x path t)) i = 0 := by
  have ht0 := potential_zero_persists_of_nonincreasing
    V x path hmono hkt hk
  simp [positiveLevelIndicator, ht0]

end ECRuntime
