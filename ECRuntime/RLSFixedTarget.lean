import ECRuntime.RLSOneBitSupport
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LinearPotential
import ECRuntime.FitnessLevel
import ECRuntime.UnrestrictedRuntime
import ECRuntime.RLSFiniteSurvivalCouponBound
import ECRuntime.LevelExitTail
import ECRuntime.BellmanGeometricExactRuntime
import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.OneMaxRLSHarmonicStep
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
Stage 114 compiler-promoted after the full Round 20 verification: exact
fixed-target runtime for one-bit RLS. Its Bellman/coupon-collector proof uses
the already promoted one-bit RLS and geometric-survival framework.
Source context: Buzdalov--Doerr--Doerr--Vinokurov (2020).
-/

/-- The fixed-target event: no more than r zero coordinates remain. -/
def rlsZeroAtMost {n : Nat} (r : Nat) : Set (BitString n) :=
  {x | zeroCount x ≤ r}

/-- Decidable target membership for the runtimeSup interface. This is a
computable comparison of finite zero counts, not a classical assumption. -/
instance instDecidablePredRlsZeroAtMost {n : Nat} (r : Nat) :
    DecidablePred (fun x : BitString n => x ∈ rlsZeroAtMost r) := by
  intro x
  change Decidable (zeroCount x ≤ r)
  infer_instance

/-- The fixed-target RLS runtime depends only on the starting bitstring
and target level, not on the magnitudes or ordering of positive weights. -/
private theorem candidate_rlsFixedTarget_reduce_to_oneMax
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (r : Nat) (x : BitString n) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x =
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        oneMaxReal) (rlsZeroAtMost (n := n) r) x := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw]

/-- A fixed-target harmonic certificate is zero once at most r zeros remain. -/
private theorem stage114_truncatedHarmonic_zero_on_target
    {n : Nat} (r : Nat) (x : BitString n)
    (hx : x ∈ rlsZeroAtMost r) :
    (if zeroCount x ≤ r then (0 : Real) else
      (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r)) = 0 := by
  have hr : zeroCount x ≤ r := hx
  simp [hr]

/-- The same truncated harmonic certificate is everywhere nonnegative. -/
private theorem stage114_truncatedHarmonic_nonneg
    {n : Nat} (r : Nat) (x : BitString n) :
    0 ≤ (if zeroCount x ≤ r then (0 : Real) else
      (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r)) := by
  by_cases hr : zeroCount x ≤ r
  · simp [hr]
  · have hrl : r ≤ zeroCount x := by omega
    have hh : harmonicReal r ≤ harmonicReal (zeroCount x) :=
      harmonicReal_mono hrl
    simp only [if_neg hr]
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hh)

/-- Staying in a smaller set cannot have larger survival probability.
This finite-horizon comparison uses only stochasticity of the kernel. -/
private theorem stage114_survival_mono
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (s t : Set alpha)
    [DecidablePred (fun y => y ∈ s)] [DecidablePred (fun y => y ∈ t)]
    (hP : IsStochastic P) (hst : s ⊆ t) :
    ∀ horizon (x : alpha),
      finiteLevelSurvival P s horizon x ≤ finiteLevelSurvival P t horizon x := by
  classical
  intro horizon
  induction horizon with
  | zero =>
      intro x
      by_cases hx : x ∈ s
      · have ht : x ∈ t := hst hx
        rw [finiteLevelSurvival_zero_of_mem P s x hx,
          finiteLevelSurvival_zero_of_mem P t x ht]
      · rw [finiteLevelSurvival_zero_of_not_mem P s x hx]
        exact finiteLevelSurvival_nonneg P t hP 0 x
  | succ horizon ih =>
      intro x
      by_cases hx : x ∈ s
      · have ht : x ∈ t := hst hx
        rw [finiteLevelSurvival_succ_of_mem P s horizon x hx,
          finiteLevelSurvival_succ_of_mem P t horizon x ht]
        change expectedValueAfter P (finiteLevelSurvival P s horizon) x ≤
          expectedValueAfter P (finiteLevelSurvival P t horizon) x
        exact expectedValueAfter_mono P hP _ _ (ih) x
      · rw [finiteLevelSurvival_succ_of_not_mem P s horizon x hx]
        exact finiteLevelSurvival_nonneg P t hP (horizon + 1) x

/-- RLS survival above any fixed-target zero-count threshold is bounded
by its survival outside the global OneMax optimum. -/
private theorem stage114_fixedTarget_survival_couponBound
    {n : Nat} (hn : 0 < n) (r : Nat) (x : BitString n) (t : Nat) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (rlsZeroAtMost (n := n) r)ᶜ t x ≤
    (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t := by
  classical
  let P : TransitionMatrix (BitString n) :=
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal
  have hP : IsStochastic P :=
    (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition_stochastic oneMaxReal
  have hsubset :
      (rlsZeroAtMost (n := n) r)ᶜ ⊆ (oneMaxTarget n)ᶜ := by
    intro y hy
    have hnotle : ¬ zeroCount y ≤ r := by
      simpa [rlsZeroAtMost] using hy
    have hne : y ≠ allOnes n := by
      intro heq
      apply hnotle
      simp [heq, zeroCount_allOnes]
    simpa [oneMaxTarget_eq_singleton] using hne
  have hmono := stage114_survival_mono P
    (rlsZeroAtMost (n := n) r)ᶜ (oneMaxTarget n)ᶜ
    hP hsubset t x
  exact hmono.trans (proposed_rlsOneMax_finiteSurvival_couponBound hn x t)

/-- The truncated harmonic potential solves the one-step Bellman equation
above the fixed target. The only reachable changes in the zero count are
`k` and `k-1`, and both are at least `r` when `k > r`. -/
private theorem stage114_truncatedHarmonic_bellman_oneMax
    {n : Nat} (hn : 0 < n) (r : Nat) (x : BitString n)
    (hr : ¬ zeroCount x ≤ r) :
    (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) =
      1 + expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
        (fun y : BitString n =>
          if zeroCount y ≤ r then (0 : Real) else
            (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r)) x := by
  classical
  let Q : BitString n → Real := fun y => (n : Real) * harmonicReal (zeroCount y)
  let R : BitString n → Real := fun y =>
    if zeroCount y ≤ r then (0 : Real) else
      (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r)
  let P := (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hselected (i : Fin n) :
      r ≤ zeroCount (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) := by
    have hstep := candidate_rls_selectedZeroCount x i
    by_cases hi : x i = false
    · simp only [if_pos hi] at hstep
      omega
    · simp only [if_neg hi] at hstep
      omega
  have hshift (i : Fin n) :
      R (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
        Q (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) -
          (n : Real) * harmonicReal r := by
    let y := selectedAfterMask oneMaxReal x ({i} : MutationMask n)
    have hge : r ≤ zeroCount y := hselected i
    by_cases heq : zeroCount y ≤ r
    · have hcount : zeroCount y = r := Nat.le_antisymm heq hge
      change (if zeroCount y ≤ r then (0 : Real) else
        (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r)) =
        (n : Real) * harmonicReal (zeroCount y) -
          (n : Real) * harmonicReal r
      rw [if_pos heq, hcount]
      ring
    · change (if zeroCount y ≤ r then (0 : Real) else
          (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r)) =
        (n : Real) * harmonicReal (zeroCount y) -
          (n : Real) * harmonicReal r
      rw [if_neg heq]
      ring
  have hsum :
      (n : Real)⁻¹ * (∑ i : Fin n,
        R (selectedAfterMask oneMaxReal x ({i} : MutationMask n))) =
      (n : Real)⁻¹ * (∑ i : Fin n,
        Q (selectedAfterMask oneMaxReal x ({i} : MutationMask n))) -
        (n : Real) * harmonicReal r := by
    simp_rw [hshift]
    rw [Finset.sum_sub_distrib]
    have hconst : (∑ _i : Fin n, (n : Real) * harmonicReal r) =
        (n : Real) * ((n : Real) * harmonicReal r) := by simp
    rw [hconst]
    field_simp [hn0]
  have hexpect : expectedValueAfter P R x =
      expectedValueAfter P Q x - (n : Real) * harmonicReal r := by
    rw [candidate_rls_expectedValueAfter_eq_singleton_average hn oneMaxReal R x,
      candidate_rls_expectedValueAfter_eq_singleton_average hn oneMaxReal Q x]
    exact hsum
  have hz : zeroCount x ≠ 0 := by omega
  have hH := proposed_oneMaxRLS_harmonic_one_step hn x
  simp only [if_neg hz] at hH
  change expectedValueAfter P Q x = Q x - 1 at hH
  have hRx : R x = Q x - (n : Real) * harmonicReal r := by
    simp only [R, if_neg hr, Q]
    ring
  calc
    (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) = R x := by
      simp only [R, if_neg hr]
    _ = 1 + expectedValueAfter P R x := by
      rw [hRx, hexpect, hH]
      ring

/-- Exact expected mutation iterations to reach at most r remaining zero bits.
The assumption r≤zeroCount(x) includes the already-at-target equality case. -/
theorem rlsLinear_fixedTarget_runtimeSup_eq
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (r : Nat) (x : BitString n) (hr : r ≤ zeroCount x) :
    runtimeSup
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
        (linearFitness w)) (rlsZeroAtMost (n := n) r) x =
      ENNReal.ofReal
        ((n : Real) * (harmonicReal (zeroCount x) - harmonicReal r)) := by
  classical
  let law := StaticUnaryUnbiasedMutation.uniformOneBitLaw hn
  let P : TransitionMatrix (BitString n) := law.transition (linearFitness w)
  let target : Set (BitString n) := rlsZeroAtMost r
  let R : BitString n → Real := fun y =>
    if zeroCount y ≤ r then (0 : Real) else
      (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r)
  have hnpos : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hnge : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hq0 : 0 ≤ (1 : Real) - 1 / (n : Real) := by
    have hdiv : (1 : Real) / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnpos).mpr (by linarith)
    linarith
  have hq1 : (1 : Real) - 1 / (n : Real) < 1 := by
    have hdiv : 0 < (1 : Real) / (n : Real) := by positivity
    linarith
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  have hRnonneg : ∀ y, 0 ≤ R y := by
    intro y
    exact stage114_truncatedHarmonic_nonneg r y
  have hRzero : ∀ y, y ∈ target → R y = 0 := by
    intro y hy
    exact stage114_truncatedHarmonic_zero_on_target r y hy
  have hRbellman : ∀ y, y ∉ target →
      R y = 1 + expectedValueAfter P R y := by
    intro y hy
    have hnot : ¬ zeroCount y ≤ r := by
      simpa only [target, rlsZeroAtMost, Set.mem_setOf_eq] using hy
    have hstep := stage114_truncatedHarmonic_bellman_oneMax hn r y hnot
    have hkernel : P =
        (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal :=
      candidate_rls_linear_transition_eq_oneMax hn w hw
    have hRy : R y =
        (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r) := by
      simp only [R, if_neg hnot]
    calc
      R y = (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r) := hRy
      _ = 1 + expectedValueAfter
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
            (fun z : BitString n => if zeroCount z ≤ r then (0 : Real) else
              (n : Real) * (harmonicReal (zeroCount z) - harmonicReal r)) y := hstep
      _ = 1 + expectedValueAfter P R y := by
        rw [hkernel]
  have hRbound : ∀ y, R y ≤ (n : Real) * harmonicReal n := by
    intro y
    by_cases hy : zeroCount y ≤ r
    · simp only [R, if_pos hy]
      exact mul_nonneg (Nat.cast_nonneg _) (harmonicReal_nonneg n)
    · simp only [R, if_neg hy]
      have hmon : harmonicReal (zeroCount y) ≤ harmonicReal n :=
        harmonicReal_mono (zeroCount_le y)
      calc
        (n : Real) * (harmonicReal (zeroCount y) - harmonicReal r) ≤
            (n : Real) * harmonicReal (zeroCount y) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          linarith [harmonicReal_nonneg r]
        _ ≤ (n : Real) * harmonicReal n :=
          mul_le_mul_of_nonneg_left hmon (Nat.cast_nonneg _)
  have hsurvival : ∀ t (y : BitString n),
      finiteLevelSurvival P targetᶜ t y ≤
        (n : Real) * (1 - 1 / (n : Real)) ^ t := by
    intro t y
    have hstep := stage114_fixedTarget_survival_couponBound hn r y t
    have hnat : (zeroCount y : Real) ≤ (n : Real) := by
      exact_mod_cast zeroCount_le y
    have hmult :
        (zeroCount y : Real) * (1 - 1 / (n : Real)) ^ t ≤
          (n : Real) * (1 - 1 / (n : Real)) ^ t :=
      mul_le_mul_of_nonneg_right hnat (pow_nonneg hq0 _)
    have htransfer : finiteLevelSurvival P targetᶜ t y ≤
        (zeroCount y : Real) * (1 - 1 / (n : Real)) ^ t := by
      simpa only [P, target, law,
        candidate_rls_linear_transition_eq_oneMax hn w hw] using hstep
    exact htransfer.trans hmult
  have hmain := proposed_exactRuntime_of_bellmanAndGeometricSurvival
    P target hP R hRnonneg hRzero hRbellman
    ((n : Real) * harmonicReal n) (n : Real)
    (1 - 1 / (n : Real)) hRbound
    (Nat.cast_nonneg n) hq0 hq1 hsurvival x
  have hRx : R x =
      (n : Real) * (harmonicReal (zeroCount x) - harmonicReal r) := by
    by_cases hxr : zeroCount x ≤ r
    · have heq : zeroCount x = r := Nat.le_antisymm hxr hr
      simp only [R, if_pos hxr]
      rw [heq]
      ring
    · simp only [R, if_neg hxr]
  simpa only [P, target, hRx] using hmain

end ECRuntime
