import ECRuntime.LeadingOnesVisitProbability
import ECRuntime.LevelExitTail
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 27 fix 10: exact geometric residence law for LeadingOnes levels

Stage 27 fix 9 fix 2 compiler-verifies the classical uniform level-visit mass `1/2`.
To turn that visit law into an exact expected runtime, the remaining local ingredient is
an exact residence-time law at every visited level.

For a parent with `leadingOnes x = i`, the canonical exit-mask family from
`LeadingOnesExit.lean` is not merely a progress subfamily: it is exactly the family of
mutation masks whose selected offspring leaves exact level `i`.  Consequently the
actual `(1+1)`-EA transition leaves level `i` with probability

  `q_i = p * (1-p)^i`.

This file first supplies a finite push-forward/event-mass identity, then proves the
exact one-step exit mass.  Finally it strengthens the generic one-level survival bound
to an equality when the exit mass is exact and specializes it to LeadingOnes:

  `P(residence lasts more than k steps | level i entered) = (1-q_i)^k`.

This is the geometric residence law needed by the next slice, which can sum the mean
residence `1/q_i` against the verified visit mass `1/2` and identify the result with the
uniform-initialization expected optimization time.
-/

/-- Finite event mass commutes with deterministic push-forward of a finite weight
function. -/
theorem finiteEventMass_pushforwardWeight
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (f : α → β) (event : β → Prop) :
    finiteEventMass (pushforwardWeight w f) event =
      finiteEventMass w (fun x => event (f x)) := by
  classical
  let indicator : β → ℝ := fun y => if event y then 1 else 0
  calc
    finiteEventMass (pushforwardWeight w f) event =
        ∑ y : β, pushforwardWeight w f y * indicator y := by
      unfold finiteEventMass indicator
      apply Finset.sum_congr rfl
      intro y _hy
      by_cases he : event y
      · have hmem : y ∈ ({z | event z} : Set β) := he
        rw [Set.indicator_of_mem hmem]
        simp [he]
      · have hnotmem : y ∉ ({z | event z} : Set β) := he
        rw [Set.indicator_of_notMem hnotmem]
        simp [he]
    _ = ∑ x : α, w x * indicator (f x) :=
      pushforwardWeight_expectation w f indicator
    _ = finiteEventMass w (fun x => event (f x)) := by
      unfold finiteEventMass indicator
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases he : event (f x)
      · have hmem : x ∈ ({z | event (f z)} : Set α) := he
        rw [Set.indicator_of_mem hmem]
        simp [he]
      · have hnotmem : x ∉ ({z | event (f z)} : Set α) := he
        rw [Set.indicator_of_notMem hnotmem]
        simp [he]

/-- A finite event whose predicate is characterized by membership in a supplied
`Finset` has event mass equal to the weight sum over that finite family. -/
theorem finiteEventMass_eq_sum_finset_of_iff
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (s : Finset α)
    (hiff : ∀ x, event x ↔ x ∈ s) :
    finiteEventMass w event = ∑ x ∈ s, w x := by
  classical
  have hset : ({x | event x} : Set α) = (s : Set α) := by
    ext x
    exact hiff x
  unfold finiteEventMass
  rw [hset]
  calc
    (∑ x : α, (s : Set α).indicator w x) =
        ∑ x ∈ s, (s : Set α).indicator w x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro x _hxuniv hxnot
      rw [Set.indicator_of_notMem hxnot]
    _ = ∑ x ∈ s, w x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Set.indicator_of_mem hx]

/-- The canonical exit-mask family is exactly the mask event characterized in
`LeadingOnesExit.lean`. -/
theorem leadingOnesExitMaskEvent_iff_mem_family
    {n : ℕ} (i : Fin n) (mask : MutationMask n) :
    leadingOnesExitMaskEvent i mask ↔ mask ∈ leadingOnesExitMaskFamily i := by
  classical
  constructor
  · intro hevent
    rcases (leadingOnesExitMaskEvent_iff_existsUnique_suffix i mask).1 hevent with
      ⟨suffix, hsuffix, _hunique⟩
    unfold leadingOnesExitMaskFamily
    rw [Finset.mem_image]
    exact ⟨suffix, Finset.mem_univ suffix, hsuffix⟩
  · intro hmem
    unfold leadingOnesExitMaskFamily at hmem
    rw [Finset.mem_image] at hmem
    rcases hmem with ⟨suffix, _hsuffix, hmask⟩
    rw [← hmask]
    exact leadingOnesExitMask_event i suffix

/-- At exact level `i`, the selected offspring leaves that level upward iff the
mutation mask belongs to the canonical exit event. -/
theorem leadingOnes_selectedAfterMask_gt_iff_exitMaskEvent
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hlevel : leadingOnes x = i.val) (mask : MutationMask n) :
    i.val < leadingOnes
        (selectedAfterMask (leadingOnesReal (n := n)) x mask) ↔
      leadingOnesExitMaskEvent i mask := by
  unfold selectedAfterMask elitistSelect
  by_cases hacc : leadingOnesReal x ≤ leadingOnesReal (mutateWithMask x mask)
  · rw [if_pos hacc]
    exact leadingOnes_mutation_exits_iff x i mask hlevel
  · rw [if_neg hacc]
    constructor
    · intro hgt
      rw [hlevel] at hgt
      omega
    · intro hevent
      have hmut := (leadingOnes_mutation_exits_iff x i mask hlevel).2 hevent
      have haccNat :
          leadingOnes x ≤ leadingOnes (mutateWithMask x mask) := by
        rw [hlevel]
        exact Nat.le_of_lt hmut
      have haccReal :
          leadingOnesReal x ≤ leadingOnesReal (mutateWithMask x mask) := by
        unfold leadingOnesReal
        exact_mod_cast haccNat
      exact (hacc haccReal).elim

/-- At exact level `i`, leaving the exact level after selection is equivalent to the
canonical exit-mask event.  Elitism excludes downward moves. -/
theorem leadingOnes_selectedAfterMask_ne_level_iff_exitMaskEvent
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hlevel : leadingOnes x = i.val) (mask : MutationMask n) :
    leadingOnes
        (selectedAfterMask (leadingOnesReal (n := n)) x mask) ≠ i.val ↔
      leadingOnesExitMaskEvent i mask := by
  have hmono := leadingOnes_selectedAfterMask_mono x mask
  constructor
  · intro hne
    have hgt :
        i.val < leadingOnes
          (selectedAfterMask (leadingOnesReal (n := n)) x mask) := by
      rw [hlevel] at hmono
      omega
    exact (leadingOnes_selectedAfterMask_gt_iff_exitMaskEvent
      x i hlevel mask).1 hgt
  · intro hevent
    have hgt := (leadingOnes_selectedAfterMask_gt_iff_exitMaskEvent
      x i hlevel mask).2 hevent
    omega

/-- Exact one-step probability mass of leaving a visited LeadingOnes level. -/
theorem onePlusOneTransition_leadingOnes_exactLevel_exitMass_eq
    {n : ℕ} (p : ℝ) (x : BitString n) (i : Fin n)
    (hlevel : leadingOnes x = i.val) :
    finiteEventMass
        (onePlusOneTransition p (leadingOnesReal (n := n)) x)
        (fun y => leadingOnes y ≠ i.val) =
      p * (1 - p) ^ i.val := by
  classical
  unfold onePlusOneTransition
  rw [finiteEventMass_pushforwardWeight]
  calc
    finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask =>
          leadingOnes
            (selectedAfterMask (leadingOnesReal (n := n)) x mask) ≠ i.val) =
      finiteEventMass
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask => leadingOnesExitMaskEvent i mask) := by
      apply congrArg
        (finiteEventMass
          (fun mask : MutationMask n => mutationMaskWeight p mask))
      funext mask
      apply propext
      exact leadingOnes_selectedAfterMask_ne_level_iff_exitMaskEvent
        x i hlevel mask
    _ = ∑ mask ∈ leadingOnesExitMaskFamily i, mutationMaskWeight p mask := by
      exact finiteEventMass_eq_sum_finset_of_iff
        (fun mask : MutationMask n => mutationMaskWeight p mask)
        (fun mask => leadingOnesExitMaskEvent i mask)
        (leadingOnesExitMaskFamily i)
        (fun mask => leadingOnesExitMaskEvent_iff_mem_family i mask)
    _ = p * (1 - p) ^ i.val :=
      leadingOnesExitMaskFamily_weight_eq p i

/-- Exact-survival version of the generic one-level recursion: if every state in a
level has the same one-step exit mass `q`, then survival for `k` transitions is exactly
`(1-q)^k`. -/
theorem finiteLevelSurvival_eq_geometric_of_exact_exit_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (hP : IsStochastic P) (q : ℝ)
    (hexit : ∀ x, x ∈ level →
      finiteEventMass (P x) (fun y => y ∉ level) = q) :
    ∀ k x, x ∈ level →
      finiteLevelSurvival P level k x = (1 - q) ^ k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simp [finiteLevelSurvival, hx]
  | succ k ih =>
      intro x hx
      rw [finiteLevelSurvival_succ_of_mem P level k x hx]
      have hpartition := finiteEventMass_add_compl (P x) (fun y => y ∈ level)
      have hrow : (∑ y, P x y) = 1 := hP.2 x
      have hstay :
          finiteEventMass (P x) (fun y => y ∈ level) = 1 - q := by
        rw [hrow, hexit x hx] at hpartition
        linarith
      calc
        (∑ y, P x y * finiteLevelSurvival P level k y) =
            ∑ y,
              ({z | z ∈ level} : Set α).indicator (P x) y * (1 - q) ^ k := by
          apply Finset.sum_congr rfl
          intro y _hy
          by_cases hylevel : y ∈ level
          · have hmem : y ∈ ({z | z ∈ level} : Set α) := hylevel
            rw [Set.indicator_of_mem hmem, ih y hylevel]
          · have hnotmem : y ∉ ({z | z ∈ level} : Set α) := hylevel
            rw [Set.indicator_of_notMem hnotmem]
            rw [finiteLevelSurvival_eq_zero_of_not_mem P level k y hylevel]
            simp
        _ = finiteEventMass (P x) (fun y => y ∈ level) * (1 - q) ^ k := by
          unfold finiteEventMass
          rw [Finset.sum_mul]
        _ = (1 - q) ^ (k + 1) := by
          rw [hstay, pow_succ]
          ring

/-- Exact finite-horizon residence survival for a visited LeadingOnes level. -/
theorem finiteLevelSurvival_leadingOnes_exact
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (k : ℕ) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    finiteLevelSurvival
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
        k x =
      (1 - p * (1 - p) ^ i.val) ^ k := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  have hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have hexit : ∀ z : BitString n,
      z ∈ ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) →
      finiteEventMass (P z)
          (fun y => y ∉ ({u : BitString n | leadingOnes u = i.val} : Set (BitString n))) =
        p * (1 - p) ^ i.val := by
    intro z hz
    change leadingOnes z = i.val at hz
    change finiteEventMass
        (onePlusOneTransition p (leadingOnesReal (n := n)) z)
        (fun y => leadingOnes y ≠ i.val) = p * (1 - p) ^ i.val
    exact onePlusOneTransition_leadingOnes_exactLevel_exitMass_eq p z i hz
  have hx : x ∈ ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) := hlevel
  simpa [P] using
    (finiteLevelSurvival_eq_geometric_of_exact_exit_mass
      P
      ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
      hP (p * (1 - p) ^ i.val) hexit k x hx)

/-- The exact level-exit parameter used by the geometric residence law. -/
def leadingOnesLevelExitProbability {n : ℕ} (p : ℝ) (i : Fin n) : ℝ :=
  p * (1 - p) ^ i.val

/-- Candidate mean residence contribution of a visited LeadingOnes level.  The next
slice will identify this reciprocal with the expectation of the exact geometric
residence law and combine it with the promoted one-half visit mass. -/
noncomputable def leadingOnesVisitedLevelMeanResidence
    {n : ℕ} (p : ℝ) (i : Fin n) : ℝ :=
  (leadingOnesLevelExitProbability p i)⁻¹

end ECRuntime
