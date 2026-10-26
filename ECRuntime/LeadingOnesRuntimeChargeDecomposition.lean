import ECRuntime.LeadingOnesExpectedRuntimeAssembly
import ECRuntime.LevelCharges
import Mathlib

open scoped BigOperators ENNReal
open Finset MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 13: exact pathwise runtime/level-charge decomposition

Stage 27 fix 12 fix 1 compiler-verifies both canonical sides of the remaining exact
LeadingOnes runtime theorem:

* the genuine uniform-initialization sample-path first-hitting-time expectation;
* the assembled exact-level residence contribution, already equal to
  `(1/2) * sum_i (p * (1-p)^i)^(-1)` after `ENNReal.ofReal`.

The missing bridge is not an algebraic identity any more.  It is a representation
statement saying that the pathwise optimization time is exactly the sum of the times
spent on all positive potential levels.  `LevelCharges.lean` already proves the easy
direction

  `firstHittingTime <= sum_i trajectoryLevelCharge i`

for every bounded natural-valued potential.  For an elitist trajectory, however, the
potential is nonincreasing.  Once the first zero-potential state is reached, every
later positive-level indicator vanishes.  Hence every complete level charge is already
captured by the finite prefix ending at the first zero, and the reverse inequality
holds as well.

This file closes that deterministic gap.  It first proves stabilization of one level
charge after a zero-potential time, then obtains the exact generic pathwise identity
under potential monotonicity, and finally specializes it to the LeadingOnes potential.
No probability or expectation interchange is performed here.  The next slice can lift
this exact pathwise equality through the genuine LeadingOnes trajectory law and identify
the expectation of each level charge with the promoted first-entry-mass times exact
mean residence.
-/

/-- Once a nonincreasing natural potential has reached zero at time `k`, every finite
horizon charge of every positive level is bounded by its charge accumulated before
`k`. -/
theorem finiteHorizonLevelCharge_le_at_zero_of_nonincreasing
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (k T : ℕ)
    (hk : V (transitionTrajectoryState x path k) = 0)
    (i : Fin m) :
    finiteHorizonLevelCharge V x path T i ≤
      finiteHorizonLevelCharge V x path k i := by
  by_cases hTk : T ≤ k
  · unfold finiteHorizonLevelCharge
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro t ht
      simp only [Finset.mem_range] at ht ⊢
      omega
    · intro t _ht _hnot
      exact bot_le
  · have hkT : k ≤ T := by omega
    have heq :
        finiteHorizonLevelCharge V x path T i =
          finiteHorizonLevelCharge V x path k i := by
      unfold finiteHorizonLevelCharge
      symm
      apply Finset.sum_subset
      · intro t ht
        simp only [Finset.mem_range] at ht ⊢
        omega
      · intro t htT hnotK
        simp only [Finset.mem_range] at htT hnotK
        have hkt : k ≤ t := by omega
        have ht0 := potential_zero_persists_of_nonincreasing
          V x path hmono hkt hk
        simp [positiveLevelIndicator, ht0]
    exact heq.le

/-- The complete charge of every positive level is bounded by its finite charge at any
zero-potential time of a nonincreasing trajectory. -/
theorem trajectoryLevelCharge_le_at_zero_of_nonincreasing
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path)
    (k : ℕ)
    (hk : V (transitionTrajectoryState x path k) = 0)
    (i : Fin m) :
    trajectoryLevelCharge V x i path ≤
      finiteHorizonLevelCharge V x path k i := by
  unfold trajectoryLevelCharge
  apply iSup_le
  intro T
  exact finiteHorizonLevelCharge_le_at_zero_of_nonincreasing
    V x path hmono k T hk i

/-- Exact deterministic level-charge decomposition for a bounded nonincreasing natural
potential.  The conventional first zero-potential hitting time is exactly the finite
sum of all complete positive-level charges. -/
theorem transitionTrajectoryFirstHittingTime_eq_levelChargeSum_of_nonincreasing
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (hbound : ∀ y, V y ≤ m)
    (x : α) (path : ℕ → α)
    (hmono : IsPotentialNonincreasingAlong V x path) :
    transitionTrajectoryFirstHittingTime (potentialTarget V) x path =
      finiteRuntimeSum (m := m)
        (fun (i : Fin m) (path' : ℕ → α) =>
          trajectoryLevelCharge (m := m) V x i path') path := by
  classical
  apply le_antisymm
  · exact transitionTrajectoryFirstHittingTime_le_levelChargeSum
      V hbound x path
  · by_cases hhit : ∃ k, transitionTrajectoryState x path k ∈ potentialTarget V
    · let k : ℕ := Nat.find hhit
      have hkHit : transitionTrajectoryState x path k ∈ potentialTarget V := by
        dsimp [k]
        exact Nat.find_spec hhit
      have hkBefore : ∀ j, j < k →
          transitionTrajectoryState x path j ∉ potentialTarget V := by
        intro j hj
        simpa [k] using Nat.find_min hhit hj
      have hk0 : V (transitionTrajectoryState x path k) = 0 := by
        exact hkHit
      have hprefix :
          (∑ i : Fin m, finiteHorizonLevelCharge V x path k i) =
            (k : ENNReal) := by
        apply sum_finiteHorizonLevelCharge_eq_natCast V x path k
        · intro t ht
          have hnot := hkBefore t ht
          change V (transitionTrajectoryState x path t) ≠ 0 at hnot
          exact Nat.pos_of_ne_zero hnot
        · intro t _ht
          exact hbound (transitionTrajectoryState x path t)
      have hsumle :
          finiteRuntimeSum (m := m)
              (fun (i : Fin m) (path' : ℕ → α) =>
                trajectoryLevelCharge (m := m) V x i path') path ≤
            ∑ i : Fin m, finiteHorizonLevelCharge V x path k i := by
        unfold finiteRuntimeSum
        exact Finset.sum_le_sum (fun i _hi =>
          trajectoryLevelCharge_le_at_zero_of_nonincreasing
            V x path hmono k hk0 i)
      have hfirst :
          transitionTrajectoryFirstHittingTime (potentialTarget V) x path =
            ENNReal.ofReal (k : ℝ) := by
        rw [transitionTrajectoryFirstHittingTime_eq_transitionTrajectoryHittingTime]
        exact transitionTrajectoryHittingTime_eq_ofReal_natCast_of_first_hit
          (potentialTarget V) x path k hkHit hkBefore
      rw [hfirst]
      calc
        finiteRuntimeSum (m := m)
            (fun (i : Fin m) (path' : ℕ → α) =>
              trajectoryLevelCharge (m := m) V x i path') path ≤
            ∑ i : Fin m, finiteHorizonLevelCharge V x path k i := hsumle
        _ = (k : ENNReal) := hprefix
        _ = ENNReal.ofReal (k : ℝ) := by simp
    · have hnever : ∀ k,
          transitionTrajectoryState x path k ∉ potentialTarget V := by
        intro k hk
        exact hhit ⟨k, hk⟩
      have hfirstTop :
          transitionTrajectoryFirstHittingTime (potentialTarget V) x path = ⊤ := by
        rw [transitionTrajectoryFirstHittingTime_eq_transitionTrajectoryHittingTime]
        exact transitionTrajectoryHittingTime_eq_top_of_never_hits
          (potentialTarget V) x path hnever
      rw [hfirstTop]
      exact le_top

/-- The zero-potential target of the canonical LeadingOnes distance is exactly the
canonical optimum target. -/
theorem potentialTarget_leadingOnesPotential (n : ℕ) :
    potentialTarget (leadingOnesPotential (n := n)) = leadingOnesTarget n := by
  ext x
  change (leadingOnesPotential x = 0) ↔ x ∈ leadingOnesTarget n
  exact (leadingOnesPotential_isTarget n x).symm

/-- Extensionality of the conventional first-hitting-time observable with respect to
its target set.  The explicit proof also transports the target-dependent
`DecidablePred` instance, avoiding dependent rewrites below. -/
private theorem transitionTrajectoryFirstHittingTime_congr_target_fix13
    {α : Type*}
    (s t : Set α)
    [hs : DecidablePred (fun z => z ∈ s)]
    [ht : DecidablePred (fun z => z ∈ t)]
    (hst : s = t) (x : α) (path : ℕ → α) :
    transitionTrajectoryFirstHittingTime s x path =
      transitionTrajectoryFirstHittingTime t x path := by
  subst t
  have hdec : hs = ht := by
    funext z
    exact Subsingleton.elim (hs z) (ht z)
  cases hdec
  rfl

/-- Exact pathwise LeadingOnes runtime decomposition along every trajectory on which
the canonical distance potential is nonincreasing. -/
theorem leadingOnesFirstHittingTime_eq_levelChargeSum_of_nonincreasing
    {n : ℕ} (x : BitString n) (path : ℕ → BitString n)
    (hmono : IsPotentialNonincreasingAlong
      (leadingOnesPotential (n := n)) x path) :
    transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path =
      ∑ i : Fin n,
        trajectoryLevelCharge (leadingOnesPotential (n := n)) x i path := by
  have hbound : ∀ y : BitString n, leadingOnesPotential y ≤ n := by
    intro y
    unfold leadingOnesPotential
    exact Nat.sub_le _ _
  have hgeneric :=
    transitionTrajectoryFirstHittingTime_eq_levelChargeSum_of_nonincreasing
      (leadingOnesPotential (n := n)) hbound x path hmono
  have htarget :=
    transitionTrajectoryFirstHittingTime_congr_target_fix13
      (potentialTarget (leadingOnesPotential (n := n)))
      (leadingOnesTarget n)
      (potentialTarget_leadingOnesPotential n) x path
  calc
    transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path =
        transitionTrajectoryFirstHittingTime
          (potentialTarget (leadingOnesPotential (n := n))) x path := htarget.symm
    _ = finiteRuntimeSum
          (fun (i : Fin n) (path' : ℕ → BitString n) =>
            trajectoryLevelCharge (leadingOnesPotential (n := n)) x i path') path :=
      hgeneric
    _ = ∑ i : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x i path := by
      rfl


/-- Measure-level lift of the exact pathwise decomposition from a fixed initial state.
The only stochastic premise is that the canonical LeadingOnes potential is
nonincreasing almost surely under the genuine trajectory law. -/
theorem leadingOnesFixedInitialFirstHittingTimeExpectation_eq_levelChargeExpectation_of_ae_nonincreasing
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : BitString n)
    (hmono : ∀ᵐ path ∂leadingOnesTrajectoryMeasure p hp0 hp1 x,
      IsPotentialNonincreasingAlong
        (leadingOnesPotential (n := n)) x path) :
    (∫⁻ path : ℕ → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x) =
      ∫⁻ path : ℕ → BitString n,
        ∑ i : Fin n,
          trajectoryLevelCharge (leadingOnesPotential (n := n)) x i path
      ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
  apply lintegral_congr_ae
  filter_upwards [hmono] with path hmonoPath
  exact leadingOnesFirstHittingTime_eq_levelChargeSum_of_nonincreasing
    x path hmonoPath

/-- Uniform-initialization lift of the exact pathwise charge decomposition, again with
potential monotonicity kept as the sole explicit almost-sure premise. -/
theorem leadingOnesUniformFirstHittingTimeExpectation_eq_levelChargeExpectation_of_ae_nonincreasing
    (n : ℕ) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hmono : ∀ x : BitString n,
      ∀ᵐ path ∂leadingOnesTrajectoryMeasure p hp0 hp1 x,
        IsPotentialNonincreasingAlong
          (leadingOnesPotential (n := n)) x path) :
    leadingOnesUniformFirstHittingTimeExpectation n p hp0 hp1 =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          ∫⁻ path : ℕ → BitString n,
            ∑ i : Fin n,
              trajectoryLevelCharge
                (leadingOnesPotential (n := n)) x i path
          ∂leadingOnesTrajectoryMeasure p hp0 hp1 x := by
  classical
  unfold leadingOnesUniformFirstHittingTimeExpectation
  apply congrArg
    (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro x _hx
  exact
    leadingOnesFixedInitialFirstHittingTimeExpectation_eq_levelChargeExpectation_of_ae_nonincreasing
      p hp0 hp1 x (hmono x)

end ECRuntime
