import ECRuntime.UnrestrictedRuntime
import ECRuntime.LevelExitTail
import ECRuntime.ConstantExitRuntime
import Mathlib

open Filter
namespace ECRuntime

/-!
Provisional public finite-mean survival infrastructure for Stages 127/133.
Copied without altering proof bodies from the Round 16 compiler-clean helper.
Promotion requires the complete pinned eight-gate verification.
-/

/-- A finite-horizon probability of remaining outside a target is at
most one. The induction needs only row-stochasticity, not hitting-time
finiteness. -/
private theorem stage133_survival_le_one
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (level : Set alpha)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) :
    ∀ t (x : alpha), finiteLevelSurvival P level t x ≤ 1 := by
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ level
      · simp [finiteLevelSurvival_zero_of_mem P level x hx]
      · simp [finiteLevelSurvival_zero_of_not_mem P level x hx]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvival_succ_of_mem P level t x hx]
        calc
          (∑ y, P x y * finiteLevelSurvival P level t y) ≤
              ∑ y, P x y * (1 : Real) := by
                apply Finset.sum_le_sum
                intro y _
                exact mul_le_mul_of_nonneg_left (ih y) (hP.1 x y)
          _ = 1 := by simpa using hP.2 x
      · rw [finiteLevelSurvival_succ_of_not_mem P level t x hx]
        norm_num

/-- Survival is nonincreasing as the number of iterations grows.
This is the finite-state monotonicity needed to convert a bounded partial
sum of survival masses into convergence of its individual terms. -/
private theorem stage133_survival_succ_le
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (level : Set alpha)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) :
    ∀ t (x : alpha), finiteLevelSurvival P level (t + 1) x ≤
      finiteLevelSurvival P level t x := by
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvival_zero_of_mem P level x hx]
        exact stage133_survival_le_one P level hP 1 x
      · rw [finiteLevelSurvival_eq_zero_of_not_mem P level 0 x hx,
          finiteLevelSurvival_eq_zero_of_not_mem P level 1 x hx]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvival_succ_of_mem P level (t + 1) x hx,
          finiteLevelSurvival_succ_of_mem P level t x hx]
        change expectedValueAfter P (finiteLevelSurvival P level (t + 1)) x ≤
          expectedValueAfter P (finiteLevelSurvival P level t) x
        exact expectedValueAfter_mono P hP _ _ ih x
      · rw [finiteLevelSurvival_eq_zero_of_not_mem P level (t + 1) x hx,
          finiteLevelSurvival_eq_zero_of_not_mem P level (t + 2) x hx]

/-- Elementary mass bound behind the finite-mean-to-vanishing-survival
argument: all first `t` survival terms dominate the `t`th term.
In particular, finite expected runtime prevents a persistent positive
survival probability. -/
private theorem stage133_time_mul_survival_le_runtime
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : Nat) (x : alpha) :
    (t : Real) * finiteLevelSurvival P targetᶜ t x ≤
      finiteHorizonRuntime P target t x := by
  classical
  rw [candidate_finiteRuntime_eq_sum_survival P target t x]
  have hmono (k : Nat) (hk : k ≤ t) :
      finiteLevelSurvival P targetᶜ t x ≤
        finiteLevelSurvival P targetᶜ k x := by
    induction t, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ t _ ih =>
        exact (stage133_survival_succ_le P targetᶜ hP t x).trans ih
  calc
    (t : Real) * finiteLevelSurvival P targetᶜ t x =
        ∑ _k ∈ Finset.range t, finiteLevelSurvival P targetᶜ t x := by
          simp [mul_comm]
    _ ≤ ∑ k ∈ Finset.range t,
          finiteLevelSurvival P targetᶜ k x := by
          apply Finset.sum_le_sum
          intro k hk
          exact hmono k (Nat.le_of_lt (Finset.mem_range.mp hk))

/-- Every one of the first `t+1` survival probabilities dominates
survival at time `t`. This removes the special `t=0` case from the
finite-mean convergence argument. -/
private theorem stage133_succ_time_mul_survival_le_runtime
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P) (t : Nat) (x : alpha) :
    (((t + 1 : Nat) : Real)) * finiteLevelSurvival P targetᶜ t x ≤
      finiteHorizonRuntime P target (t + 1) x := by
  classical
  rw [candidate_finiteRuntime_eq_sum_survival P target (t + 1) x]
  have hmono (k : Nat) (hk : k ≤ t) :
      finiteLevelSurvival P targetᶜ t x ≤
        finiteLevelSurvival P targetᶜ k x := by
    induction t, hk using Nat.le_induction with
    | base => exact le_rfl
    | succ t _ ih =>
        exact (stage133_survival_succ_le P targetᶜ hP t x).trans ih
  calc
    (((t + 1 : Nat) : Real)) * finiteLevelSurvival P targetᶜ t x =
        ∑ _k ∈ Finset.range (t + 1),
          finiteLevelSurvival P targetᶜ t x := by
          simp [mul_comm]
    _ ≤ ∑ k ∈ Finset.range (t + 1),
          finiteLevelSurvival P targetᶜ k x := by
          apply Finset.sum_le_sum
          intro k hk
          exact hmono k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- Finite unrestricted expected hitting time forces the finite-horizon
non-target survival mass to vanish, without a geometric assumption. -/
theorem candidate_finiteSurvival_tendsto_zero_of_finite_runtime
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P)
    (hFinite : ∀ x, runtimeSup P target x ≠ ⊤)
    (x : alpha) :
    Tendsto (fun t : Nat => finiteLevelSurvival P targetᶜ t x)
      atTop (nhds (0 : Real)) := by
  classical
  let M : Real := (runtimeSup P target x).toReal
  have hBound (t : Nat) : finiteHorizonRuntime P target t x ≤ M := by
    have he := finiteHorizonRuntime_ofReal_le_runtimeSup P target t x
    have hn := finiteHorizonRuntime_nonneg P target hP t x
    have hmono := ENNReal.toReal_mono (hFinite x) he
    simpa only [M, ENNReal.toReal_ofReal hn] using hmono
  have hpoint (t : Nat) :
      finiteLevelSurvival P targetᶜ t x ≤
        M / ((t + 1 : Nat) : Real) := by
    have htpos : (0 : Real) < ((t + 1 : Nat) : Real) := by positivity
    apply (le_div_iff₀ htpos).mpr
    have hsteps := stage133_succ_time_mul_survival_le_runtime
      P target hP t x
    simpa only [mul_comm] using hsteps.trans (hBound (t + 1))
  have hden : Tendsto (fun t : Nat => ((t + 1 : Nat) : Real))
      atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall (fun t : Nat => by
        exact_mod_cast Nat.le_succ t))
      tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun t : Nat => ((t + 1 : Nat) : Real)⁻¹)
      atTop (nhds (0 : Real)) :=
    tendsto_inv_atTop_zero.comp hden
  have hupper : Tendsto
      (fun t : Nat => M / ((t + 1 : Nat) : Real))
      atTop (nhds (0 : Real)) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul M
  apply squeeze_zero
  · intro t
    exact finiteLevelSurvival_nonneg P targetᶜ hP t x
  · intro t
    exact hpoint t
  · exact hupper

end ECRuntime
