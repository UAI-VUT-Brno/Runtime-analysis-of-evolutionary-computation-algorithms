import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.Transition
import ECRuntime.UnrestrictedRuntime
import ECRuntime.LevelExitTail
import ECRuntime.LeadingOnesOccupationTotalClosure
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-!
Stage 118 provisional public module. The helper lemmas below are local,
so this library module does not rely on imports from `candidates/`.
The one approved public theorem is reproduced without changing its statement.
Full-gate verification and compiler-derived pins are pending.
-/

/-!
Unpromoted helper, separate from public import graph.
For finite-state stochastic transitions, finite runtime increments are
survival probabilities. Telescoping and monotone convergence give the
infinite-horizon geometric waiting-time identity.
-/

/-- The increment of truncated expected hitting time equals probability
of survival at the preceding time. No stochasticity is needed for this
algebraic finite recursion. -/
private theorem stage118_finiteRuntime_increment_eq_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)] :
    ∀ t (x : α),
      finiteHorizonRuntime P target (t + 1) x =
        finiteHorizonRuntime P target t x +
          finiteLevelSurvival P targetᶜ t x := by
  classical
  intro t
  induction t with
  | zero =>
      intro x
      by_cases hx : x ∈ target
      · have hxc : x ∉ targetᶜ := by simpa using hx
        simp [finiteHorizonRuntime_succ_of_mem P target 0 x hx,
          finiteLevelSurvival_eq_zero_of_not_mem P targetᶜ 0 x hxc]
      · have hxc : x ∈ targetᶜ := by simpa using hx
        rw [finiteHorizonRuntime_succ_of_not_mem P target 0 x hx]
        simp [finiteHorizonRuntime_zero, finiteLevelSurvival_zero_of_mem
          P targetᶜ x hxc, expectedValueAfter]
  | succ t ih =>
      intro x
      by_cases hx : x ∈ target
      · have hxc : x ∉ targetᶜ := by simpa using hx
        simp [finiteHorizonRuntime_succ_of_mem P target _ x hx,
          finiteLevelSurvival_eq_zero_of_not_mem P targetᶜ (t + 1) x hxc]
      · have hxc : x ∈ targetᶜ := by simpa using hx
        rw [finiteHorizonRuntime_succ_of_not_mem P target (t + 1) x hx,
          finiteHorizonRuntime_succ_of_not_mem P target t x hx,
          finiteLevelSurvival_succ_of_mem P targetᶜ t x hxc]
        have hsplit :
            expectedValueAfter P (finiteHorizonRuntime P target (t + 1)) x =
              expectedValueAfter P (finiteHorizonRuntime P target t) x +
                expectedValueAfter P (finiteLevelSurvival P targetᶜ t) x := by
          calc
            expectedValueAfter P (finiteHorizonRuntime P target (t + 1)) x =
                expectedValueAfter P
                  (fun y => finiteHorizonRuntime P target t y +
                    finiteLevelSurvival P targetᶜ t y) x := by
                      unfold expectedValueAfter
                      apply Finset.sum_congr rfl
                      intro y _
                      rw [ih y]
            _ = _ := expectedValueAfter_add P _ _ x
        rw [hsplit]
        unfold expectedValueAfter
        ring

/-- The exact finite tail-sum formula. -/
private theorem stage118_finiteRuntime_eq_sum_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (t : Nat) (x : α) :
    finiteHorizonRuntime P target t x =
      ∑ k ∈ Finset.range t, finiteLevelSurvival P targetᶜ k x := by
  classical
  induction t with
  | zero => simp
  | succ t ih =>
      rw [stage118_finiteRuntime_increment_eq_survival P target t x,
        ih, Finset.sum_range_succ]

/-- Expected runtime as the nonnegative survival tail `tsum`. -/
private theorem stage118_runtimeSup_eq_survival_tsum
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (hP : IsStochastic P) (x : α) :
    runtimeSup P target x =
      ∑' t : Nat, ENNReal.ofReal (finiteLevelSurvival P targetᶜ t x) := by
  classical
  unfold runtimeSup
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_congr
  intro t
  rw [stage118_finiteRuntime_eq_sum_survival P target t x]
  exact ENNReal.ofReal_sum_of_nonneg
    (fun k _ => finiteLevelSurvival_nonneg P targetᶜ hP k x)

/-- Exact unrestricted expected runtime for a constant geometric survival
law, not merely an upper bound. -/
private theorem stage118_runtimeSup_eq_inv_of_geometric_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun z => z ∈ target)]
    (hP : IsStochastic P) (q : Real) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (x : α)
    (hsurvival : ∀ t : Nat,
      finiteLevelSurvival P targetᶜ t x = (1 - q) ^ t) :
    runtimeSup P target x = ENNReal.ofReal q⁻¹ := by
  have hstay0 : 0 ≤ 1 - q := by linarith
  rw [stage118_runtimeSup_eq_survival_tsum P target hP x]
  calc
    (∑' t : Nat, ENNReal.ofReal (finiteLevelSurvival P targetᶜ t x)) =
        ∑' t : Nat, (ENNReal.ofReal (1 - q)) ^ t := by
          apply tsum_congr
          intro t
          rw [hsurvival t]
          exact ENNReal.ofReal_pow hstay0 t
    _ = (1 - ENNReal.ofReal (1 - q))⁻¹ :=
      ENNReal.tsum_geometric (ENNReal.ofReal (1 - q))
    _ = ENNReal.ofReal q⁻¹ := by
      have hsub : 1 - ENNReal.ofReal (1 - q) = ENNReal.ofReal q := by
        calc
          1 - ENNReal.ofReal (1 - q) =
              ENNReal.ofReal (1 : Real) - ENNReal.ofReal (1 - q) := by norm_num
          _ = ENNReal.ofReal ((1 : Real) - (1 - q)) := by
                exact (ENNReal.ofReal_sub (1 : Real) hstay0).symm
          _ = ENNReal.ofReal q := by congr 1; ring
      rw [hsub]
      exact (ENNReal.ofReal_inv_of_pos hq0).symm

/-!
Reusable, non-public preliminary lemma for Stage 118. Unlike a fitness-specific
runtime theorem, this identifies the full offspring distribution for p=1/2.
The original Stage 116 theorem is intentionally left unchanged until its
pinned compiler run is confirmed.
-/

/-- Independent bit mutation with rate one half gives every possible child
weight `2^{-n}`, independently of its parent. -/
private theorem stage118_halfMutation_uniformOffspring
    {n : Nat} (parent y : BitString n) :
    (Finset.univ.sum (fun mask : MutationMask n =>
      if mutateWithMask parent mask = y then
        mutationMaskWeight (n := n) (1 / 2 : Real) mask
      else 0)) = (1 : Real) / (2 : Real) ^ n := by
  classical
  let targetMask : MutationMask n :=
    Finset.univ.filter (fun i => parent i ≠ y i)
  have hflip (mask : MutationMask n) (i : Fin n) :
      i ∈ mask ↔ parent i ≠ mutateWithMask parent mask i := by
    by_cases hi : i ∈ mask
    · cases hpi : parent i <;> simp [mutateWithMask, hi, hpi]
    · simp [mutateWithMask, hi]
  have htarget : mutateWithMask parent targetMask = y := by
    funext i
    by_cases heq : parent i = y i
    · simp [mutateWithMask, targetMask, heq]
    · cases hp : parent i <;> cases hy : y i <;>
        simp_all [mutateWithMask, targetMask]
  have hunique (mask : MutationMask n)
      (heq : mutateWithMask parent mask = y) : mask = targetMask := by
    ext i
    rw [hflip]
    rw [heq]
    simp [targetMask]
  have hiff (mask : MutationMask n) :
      mutateWithMask parent mask = y ↔ mask = targetMask := by
    exact ⟨hunique mask, fun h => h ▸ htarget⟩
  have hweight (mask : MutationMask n) :
      mutationMaskWeight (n := n) (1 / 2 : Real) mask =
        (1 / 2 : Real) ^ n := by
    have hcard : mask.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ mask)
    unfold mutationMaskWeight
    have hhalf : (1 : Real) - 1 / 2 = 1 / 2 := by norm_num
    rw [hhalf, ← pow_add, Nat.add_sub_of_le hcard]
  simp_rw [hweight, hiff]
  simp

/-! Approved Stage 118: exact fixed-target runtime under bit mutation at
p=1/2. The target must be a fitness superlevel set, since elitist selection
only preserves feasibility for such a target. Unverified proof candidate. -/

/-- Fitness superlevel target for an elitist maximizer. -/
def candidateFitnessThreshold {n : Nat}
    (fitness : BitString n → Real) (threshold : Real) : Set (BitString n) :=
  {x | threshold ≤ fitness x}

/-- Classical decidability of finite real-valued fitness thresholds. -/
noncomputable instance instCandidateFitnessThresholdDecidable
    {n : Nat} (fitness : BitString n → Real) (threshold : Real) :
    DecidablePred (fun x => x ∈ candidateFitnessThreshold fitness threshold) := by
  classical
  intro x
  change Decidable (threshold ≤ fitness x)
  infer_instance

/-- Number of fitness-threshold solutions. -/
noncomputable def candidateFitnessThresholdCount {n : Nat}
    (fitness : BitString n → Real) (threshold : Real) : Nat := by
  classical
  exact (Finset.univ.filter (fun x : BitString n =>
    x ∈ candidateFitnessThreshold fitness threshold)).card

/-- Below the threshold, elitist selection reaches the threshold exactly
when the uniformly generated offspring lies in the superlevel set. -/
private theorem candidateUniform_thresholdSelection_iff
    {n : Nat} (fitness : BitString n → Real) (threshold : Real)
    (x : BitString n) (hx : x ∉ candidateFitnessThreshold fitness threshold)
    (mask : MutationMask n) :
    selectedAfterMask fitness x mask ∈ candidateFitnessThreshold fitness threshold ↔
    mutateWithMask x mask ∈ candidateFitnessThreshold fitness threshold := by
  by_cases hacc : Accepts fitness x (mutateWithMask x mask)
  · simp [selectedAfterMask, elitistSelect_of_accepts _ _ _ hacc]
  · have hy : mutateWithMask x mask ∉ candidateFitnessThreshold fitness threshold := by
      intro hth
      have hbelow : fitness x < threshold := lt_of_not_ge hx
      have habove : threshold ≤ fitness (mutateWithMask x mask) := hth
      exact hacc (le_trans hbelow.le habove)
    simp [selectedAfterMask, elitistSelect_of_rejects _ _ _ hacc, hx, hy]

/-- The exact probability of reaching an attainable threshold in one step
under uniform mutation is the target cardinality divided by `2^n`. -/
private theorem candidateUniform_thresholdSuccessMass
    {n : Nat} (fitness : BitString n → Real) (threshold : Real)
    (x : BitString n) (hx : x ∉ candidateFitnessThreshold fitness threshold) :
    finiteEventMass (onePlusOneTransition (1 / 2 : Real) fitness x)
      (fun y => y ∈ candidateFitnessThreshold fitness threshold) =
    (candidateFitnessThresholdCount fitness threshold : Real) /
      (2 : Real) ^ n := by
  classical
  have hevents :
      (fun mask : MutationMask n =>
        selectedAfterMask fitness x mask ∈ candidateFitnessThreshold fitness threshold) =
      (fun mask : MutationMask n =>
        mutateWithMask x mask ∈ candidateFitnessThreshold fitness threshold) := by
    funext mask
    exact propext (candidateUniform_thresholdSelection_iff fitness threshold x hx mask)
  unfold onePlusOneTransition
  rw [finiteEventMass_pushforwardWeight, hevents]
  have huniform :
      pushforwardWeight
        (mutationMaskWeight (n := n) (1 / 2 : Real))
        (mutateWithMask x) = fun _ => (1 : Real) / (2 : Real) ^ n := by
    funext y
    exact stage118_halfMutation_uniformOffspring x y
  rw [← finiteEventMass_pushforwardWeight, huniform]
  let s : Finset (BitString n) := Finset.univ.filter
    (fun y => y ∈ candidateFitnessThreshold fitness threshold)
  have hsum :
      finiteEventMass (fun _ : BitString n => (1 : Real) / (2 : Real) ^ n)
        (fun y => y ∈ candidateFitnessThreshold fitness threshold) =
      ∑ y ∈ s, (1 : Real) / (2 : Real) ^ n := by
    unfold finiteEventMass
    calc
      (∑ y : BitString n,
        ({y | y ∈ candidateFitnessThreshold fitness threshold} :
          Set (BitString n)).indicator
            (fun _ => (1 : Real) / (2 : Real) ^ n) y) =
        ∑ y : BitString n,
          if y ∈ s then (1 : Real) / (2 : Real) ^ n else 0 := by
            apply Finset.sum_congr rfl
            intro y _
            by_cases hy : y ∈ candidateFitnessThreshold fitness threshold
            · have hm : y ∈ ({z : BitString n |
                z ∈ candidateFitnessThreshold fitness threshold} :
                Set (BitString n)) := hy
              rw [Set.indicator_of_mem hm (fun _ => (1 : Real) / (2 : Real) ^ n)]
              simp [s, hy]
            · have hm : y ∉ ({z : BitString n |
                z ∈ candidateFitnessThreshold fitness threshold} :
                Set (BitString n)) := hy
              rw [Set.indicator_of_notMem hm (fun _ => (1 : Real) / (2 : Real) ^ n)]
              simp [s, hy]
      _ = ∑ y ∈ s, (1 : Real) / (2 : Real) ^ n :=
        Finset.sum_ite_mem_eq _ _
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  change (candidateFitnessThresholdCount fitness threshold : Real) *
    ((1 : Real) / (2 : Real) ^ n) = _
  ring

/-- Exact geometric runtime from below any attainable fitness threshold. -/
theorem candidateUniform_fixedTarget_runtimeSup_eq
    {n : Nat} (fitness : BitString n → Real) (threshold : Real)
    (hcount : 0 < candidateFitnessThresholdCount fitness threshold)
    (x : BitString n) (hx : x ∉ candidateFitnessThreshold fitness threshold) :
    runtimeSup (onePlusOneTransition (1 / 2 : Real) fitness)
      (candidateFitnessThreshold fitness threshold) x =
      ENNReal.ofReal
        ((2 : Real) ^ n /
          (candidateFitnessThresholdCount fitness threshold : Real)) := by
  classical
  let target : Set (BitString n) := candidateFitnessThreshold fitness threshold
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition (1 / 2 : Real) fitness
  let q : Real := (candidateFitnessThresholdCount fitness threshold : Real) /
    (2 : Real) ^ n
  have hcountReal : 0 < (candidateFitnessThresholdCount fitness threshold : Real) := by
    exact_mod_cast hcount
  have htotal : (candidateFitnessThresholdCount fitness threshold : Real) ≤
      (2 : Real) ^ n := by
    have hsub :
        (Finset.univ.filter (fun y : BitString n =>
          y ∈ target)).card ≤
            (Finset.univ : Finset (BitString n)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hnat : candidateFitnessThresholdCount fitness threshold ≤ 2 ^ n := by
      simpa [candidateFitnessThresholdCount, target, BitString] using hsub
    exact_mod_cast hnat
  have hden : (0 : Real) < 2 ^ n := by positivity
  have hq0 : 0 < q := div_pos hcountReal hden
  have hq1 : q ≤ 1 := (div_le_one hden).2 htotal
  have hP : IsStochastic P :=
    onePlusOneTransition_stochastic (by norm_num) (by norm_num) fitness
  have hexit : ∀ y : BitString n, y ∈ targetᶜ →
      finiteEventMass (P y) (fun z => z ∉ targetᶜ) = q := by
    intro y hy
    have hy' : y ∉ candidateFitnessThreshold fitness threshold := hy
    have hevent : (fun z : BitString n => z ∉ targetᶜ) =
        (fun z : BitString n => z ∈ target) := by
      funext z
      apply propext
      simp
    rw [hevent]
    exact candidateUniform_thresholdSuccessMass fitness threshold y hy'
  have hsurvival : ∀ t : Nat,
      finiteLevelSurvival P targetᶜ t x = (1 - q) ^ t := by
    intro t
    apply finiteLevelSurvival_eq_geometric_of_exact_exit_mass
      P targetᶜ hP q hexit t x
    exact hx
  have hmean := stage118_runtimeSup_eq_inv_of_geometric_survival
    P target hP q hq0 hq1 x hsurvival
  calc
    runtimeSup (onePlusOneTransition (1 / 2 : Real) fitness)
        (candidateFitnessThreshold fitness threshold) x = ENNReal.ofReal q⁻¹ := hmean
    _ = ENNReal.ofReal
        ((2 : Real) ^ n / (candidateFitnessThresholdCount fitness threshold : Real)) := by
      congr 1
      simp only [q, inv_div]

end ECRuntime
