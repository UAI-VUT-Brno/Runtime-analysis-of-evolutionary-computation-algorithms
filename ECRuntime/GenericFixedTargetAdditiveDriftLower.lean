import ECRuntime.AdditiveDrift
import ECRuntime.ConstantExitRuntime
import ECRuntime.GenericDriftLowerFiniteHorizonResearch
import ECRuntime.GenericStoppedResidualSurvivalEnvelope
import ECRuntime.FiniteRuntimeSurvivalSupport
import Mathlib

attribute [local instance] Classical.propDecidable
open scoped BigOperators ENNReal
open Filter
namespace ECRuntime

/-! P07: strategically new claim family. Existing certified additive and
multiplicative drift theorems mostly give runtime upper bounds. Lower bounds
require a *maximum* expected progress assumption and a stopped-process
argument. The proof is deliberately not replaced by a self-loop inequality. -/

/-! The Stage-133 survival times horizon estimate is `private` in its
original module. It is unavailable to imports. Retain the checked reasoning
here as local proof infrastructure rather than introducing an axiom or
strengthening the initial-state finiteness assumption. -/

/-- A finite-horizon probability of remaining outside a target is at
most one. The induction needs only row-stochasticity, not hitting-time
finiteness. -/
private theorem proof64_survival_le_one
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
private theorem proof64_survival_succ_le
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
        exact proof64_survival_le_one P level hP 1 x
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
private theorem proof64_time_mul_survival_le_runtime
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
        exact (proof64_survival_succ_le P targetᶜ hP t x).trans ih
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
private theorem proof64_succ_time_mul_survival_le_runtime
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
        exact (proof64_survival_succ_le P targetᶜ hP t x).trans ih
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


/-- Single-start version of the certified finite-mean survival argument.
The existing Stage 133 interface requires finiteness from *every* state;
for lower drift only finiteness from the specified initial state is known.
It reuses the *certified* Stage 133 survival-versus-runtime bound,
plus Mathlib's `tendsto_inv_atTop_zero` and `squeeze_zero`. -/
private theorem proof62_singleStart_finiteSurvival_tendsto_zero
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun y : α => y ∈ target)]
    (hP : IsStochastic P) (x : α)
    (hFinite : runtimeSup P target x ≠ ⊤) :
    Tendsto (fun t : Nat => finiteLevelSurvival P targetᶜ t x)
      atTop (nhds (0 : Real)) := by
  classical
  let M : Real := (runtimeSup P target x).toReal
  have hBound (t : Nat) : finiteHorizonRuntime P target t x ≤ M := by
    have he := finiteHorizonRuntime_ofReal_le_runtimeSup P target t x
    have hn := finiteHorizonRuntime_nonneg P target hP t x
    have hmono := ENNReal.toReal_mono hFinite he
    simpa only [M, ENNReal.toReal_ofReal hn] using hmono
  have hpoint (t : Nat) :
      finiteLevelSurvival P targetᶜ t x ≤
        M / ((t + 1 : Nat) : Real) := by
    have htpos : (0 : Real) < ((t + 1 : Nat) : Real) := by positivity
    apply (le_div_iff₀ htpos).mpr
    have hsteps := proof64_succ_time_mul_survival_le_runtime
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

/-- A bounded one-step expected potential decrease implies a lower bound
on genuine extended expected hitting time, provided the potential is
nonnegative and vanishes at the target. -/
theorem proposed_genericFixedTarget_additiveDrift_runtimeLower
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (target : Set α) (potential : α → Real)
    (hpot : ∀ y : α, 0 ≤ potential y)
    (hzero : ∀ y ∈ target, potential y = 0)
    (delta : Real) (hdelta : 0 < delta)
    (hstep : ∀ y ∉ target,
      (∑ z : α, P y z * (potential y - potential z)) ≤ delta)
    (x : α) (hx : x ∉ target) :
    ENNReal.ofReal (potential x / delta) ≤ runtimeSup P target x := by
  classical
  -- If the initial runtime is infinite, the extended-real comparison
  -- is immediate. Otherwise only *this initial state* needs finite mean.
  by_cases hfinite : runtimeSup P target x = ⊤
  · simp [hfinite]
  · have hsurvival :
        Tendsto (fun t : Nat => finiteLevelSurvival P targetᶜ t x)
          atTop (nhds (0 : Real)) :=
      proof62_singleStart_finiteSurvival_tendsto_zero P target hP x hfinite
    -- Finiteness of the state space and nonnegativity give a concrete
    -- uniform upper bound on all residual potentials.
    let B : Real := ∑ y : α, potential y
    have hbound (y : α) : potential y ≤ B := by
      exact Finset.single_le_sum
        (s := Finset.univ) (fun z _ => hpot z) (Finset.mem_univ y)
    have hres (t : Nat) :
        finiteStoppedPotential P target potential t x ≤
          B * finiteLevelSurvival P targetᶜ t x :=
      proposed_genericDriftLower_stoppedPotential_le_survival
        P target hP potential hzero B hbound t x
    have happrox (t : Nat) :
        ENNReal.ofReal ((potential x -
          B * finiteLevelSurvival P targetᶜ t x) / delta) ≤
          runtimeSup P target x := by
      have hfinite_step := proposed_genericDriftLower_finiteHorizon_withResidual
        P hP target potential hpot hzero delta hdelta hstep x t
      have hd : (potential x -
          B * finiteLevelSurvival P targetᶜ t x) / delta ≤
          finiteHorizonRuntime P target t x := by
        apply (div_le_iff₀ hdelta).2
        have hr := hres t
        nlinarith
      exact (ENNReal.ofReal_le_ofReal hd).trans
        (finiteHorizonRuntime_ofReal_le_runtimeSup P target t x)
    have hprod : Tendsto
        (fun t : Nat => B * finiteLevelSurvival P targetᶜ t x)
        atTop (nhds (0 : Real)) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul hsurvival :
          Tendsto
            (fun t : Nat => B * finiteLevelSurvival P targetᶜ t x)
            atTop (nhds (B * 0)))
    have hlim : Tendsto
        (fun t : Nat => (potential x -
          B * finiteLevelSurvival P targetᶜ t x) / delta)
        atTop (nhds (potential x / delta)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub hprod).div_const delta
    have hlimENN : Tendsto
        (fun t : Nat => ENNReal.ofReal ((potential x -
          B * finiteLevelSurvival P targetᶜ t x) / delta))
        atTop (nhds (ENNReal.ofReal (potential x / delta))) :=
      ENNReal.tendsto_ofReal hlim
    -- The original theorem requires a start outside the target. The
    -- finite-horizon estimate is valid there and indeed at every state.
    have _ : finiteLevelSurvival P targetᶜ 0 x = 1 :=
      finiteLevelSurvival_zero_of_mem P targetᶜ x (by simpa using hx)
    apply le_of_tendsto hlimENN
    exact Filter.Eventually.of_forall happrox

end ECRuntime
