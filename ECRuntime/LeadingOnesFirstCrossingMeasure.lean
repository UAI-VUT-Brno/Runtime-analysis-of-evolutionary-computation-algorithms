import ECRuntime.LeadingOnesBoundaryEventualCrossing
import ECRuntime.FiniteMarginalIdentification
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 8: first-crossing finite-history / trajectory-measure bridge

Stage 27 fix 7 fix 2 compiler-verifies that, for `0 < p < 1`, the genuine
Ionescu--Tulcea LeadingOnes trajectory reaches every fixed nonterminal boundary almost
surely.  Stage 27 fix 6 independently compiler-verifies the countable exact-entry / skip
mass aggregation built from explicit finite histories.

This file supplies the representation layer between those two developments for one fixed
initial state.  A finite first-crossing set is defined directly on the explicit
`FiniteTrajectory` space.  Its real path-weight sum is identified with its
`finiteTrajectoryMeasure` probability, then transported through the verified finite
marginal bridge to an infinite-path cylinder.  The cylinders for distinct first-crossing
times are pairwise disjoint and their union is exactly
`leadingOnesEventuallyCrossesBoundarySet`.

Consequently, under `0 < p < 1`, the countable sum of the fixed-initial first-crossing
masses is one.  The next slice only needs to average this identity over the finite uniform
initial distribution and identify that average with the Stage-27 fix-6 aggregate mass.
-/

/-- Finite post-initial trajectories whose first crossing of boundary `i` occurs at the
terminal time `t`.  All transition-parent states are strictly below `i`, while the
terminal state is at or above `i`. -/
def leadingOnesFiniteFirstCrossingSet
    {n : ℕ} (i : Fin n) (x : BitString n) (t : ℕ) :
    Set (FiniteTrajectory (BitString n) t) :=
  {path |
    leadingOnesPreCrossing i t x path ∧
      i.val ≤ leadingOnes (finiteTrajectoryTerminal t x path)}

/-- The fixed-initial real mass of first crossing boundary `i` exactly at time `t`. -/
noncomputable def leadingOnesFixedInitialFirstCrossingMass
    {n t : ℕ} (p : ℝ) (i : Fin n) (x : BitString n) : ℝ := by
  classical
  exact ∑ path : FiniteTrajectory (BitString n) t,
    if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
      finiteTrajectoryWeight
        (onePlusOneTransition p (leadingOnesReal (n := n))) t x path
    else 0

/-- The finite first-crossing event is exactly the disjoint exact-entry/strict-skip
partition already used in Stage 27 fixes 4--6. -/
theorem mem_leadingOnesFiniteFirstCrossingSet_iff_exact_or_skip
    {n t : ℕ} (i : Fin n) (x : BitString n)
    (path : FiniteTrajectory (BitString n) t) :
    path ∈ leadingOnesFiniteFirstCrossingSet i x t ↔
      leadingOnesFirstCrossingExact i (x, path) ∨
        leadingOnesFirstCrossingSkip i (x, path) := by
  change
    (leadingOnesPreCrossing i t x path ∧
      i.val ≤ leadingOnes (finiteTrajectoryTerminal t x path)) ↔
    ((leadingOnesPreCrossing i t x path ∧
        leadingOnes (finiteTrajectoryTerminal t x path) = i.val) ∨
      (leadingOnesPreCrossing i t x path ∧
        i.val < leadingOnes (finiteTrajectoryTerminal t x path)))
  constructor
  · rintro ⟨hpre, hterm⟩
    rcases eq_or_lt_of_le hterm with heq | hlt
    · exact Or.inl ⟨hpre, heq.symm⟩
    · exact Or.inr ⟨hpre, hlt⟩
  · rintro (hexact | hskip)
    · exact ⟨hexact.1, by omega⟩
    · exact ⟨hskip.1, Nat.le_of_lt hskip.2⟩

/-- Every finite first-crossing set is measurable because the state space is finite. -/
theorem measurableSet_leadingOnesFiniteFirstCrossingSet
    {n t : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (i : Fin n) (x : BitString n) :
    MeasurableSet (leadingOnesFiniteFirstCrossingSet i x t) := by
  exact (leadingOnesFiniteFirstCrossingSet i x t).to_countable.measurableSet

/-- The explicit finite trajectory measure of a first-crossing slice is the `ENNReal`
embedding of its explicit real path-weight mass. -/
theorem finiteTrajectoryMeasure_leadingOnesFiniteFirstCrossingSet
    {n t : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) :
    finiteTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n)))
        t x (leadingOnesFiniteFirstCrossingSet i x t) =
      ENNReal.ofReal (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have hEvent : MeasurableSet (leadingOnesFiniteFirstCrossingSet i x t) :=
    measurableSet_leadingOnesFiniteFirstCrossingSet i x
  change finiteTrajectoryMeasure P hP t x
      (leadingOnesFiniteFirstCrossingSet i x t) = _
  rw [← MeasureTheory.lintegral_indicator_fun_one hEvent]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [finiteTrajectoryMeasure_singleton P hP t x]
  have hnonneg :
      ∀ path ∈ (Finset.univ : Finset (FiniteTrajectory (BitString n) t)),
        0 ≤
          (if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
            finiteTrajectoryWeight P t x path
          else 0) := by
    intro path _hpath
    by_cases hcross : path ∈ leadingOnesFiniteFirstCrossingSet i x t
    · simpa [hcross] using finiteTrajectoryWeight_nonneg P hP t x path
    · simp [hcross]
  calc
    (∑ path : FiniteTrajectory (BitString n) t,
        (leadingOnesFiniteFirstCrossingSet i x t).indicator
            (fun _ => (1 : ENNReal)) path *
          ENNReal.ofReal (finiteTrajectoryWeight P t x path)) =
        ∑ path : FiniteTrajectory (BitString n) t,
          ENNReal.ofReal
            (if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
              finiteTrajectoryWeight P t x path
            else 0) := by
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hcross : path ∈ leadingOnesFiniteFirstCrossingSet i x t
      · simp [hcross]
      · simp [hcross]
    _ = ENNReal.ofReal
        (∑ path : FiniteTrajectory (BitString n) t,
          if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
            finiteTrajectoryWeight P t x path
          else 0) := by
      symm
      exact ENNReal.ofReal_sum_of_nonneg hnonneg
    _ = ENNReal.ofReal
        (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
      rfl

/-- The terminal state of the first `t` post-initial coordinates is the absolute
trajectory state at time `t`. -/
@[simp] theorem finiteTrajectoryTerminal_transitionTrajectoryTail
    {α : Type*} (t : ℕ) (x : α) (path : ℕ → α) :
    finiteTrajectoryTerminal t x (transitionTrajectoryTail t path) =
      transitionTrajectoryState x path t := by
  cases t <;> rfl

/-- Infinite-path cylinder whose first crossing of boundary `i` occurs at time `t`. -/
def leadingOnesTrajectoryFirstCrossingSet
    {n : ℕ} (i : Fin n) (x : BitString n) (t : ℕ) : Set (ℕ → BitString n) :=
  transitionTrajectoryTail t ⁻¹' leadingOnesFiniteFirstCrossingSet i x t

/-- Each exact-time first-crossing cylinder is measurable. -/
theorem measurableSet_leadingOnesTrajectoryFirstCrossingSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (i : Fin n) (x : BitString n) (t : ℕ) :
    MeasurableSet (leadingOnesTrajectoryFirstCrossingSet i x t) := by
  unfold leadingOnesTrajectoryFirstCrossingSet
  exact (measurableSet_leadingOnesFiniteFirstCrossingSet i x).preimage
    (measurable_transitionTrajectoryTail (α := BitString n) t)

/-- The genuine trajectory probability of one exact-time first-crossing cylinder equals
its explicit finite path-weight mass. -/
theorem transitionTrajectoryMeasure_leadingOnesTrajectoryFirstCrossingSet
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) (t : ℕ) :
    transitionTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))) x
        (leadingOnesTrajectoryFirstCrossingSet i x t) =
      ENNReal.ofReal (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  have htail : Measurable
      (transitionTrajectoryTail (α := BitString n) t) :=
    measurable_transitionTrajectoryTail (α := BitString n) t
  have hEvent : MeasurableSet (leadingOnesFiniteFirstCrossingSet i x t) :=
    measurableSet_leadingOnesFiniteFirstCrossingSet i x
  unfold leadingOnesTrajectoryFirstCrossingSet
  change transitionTrajectoryMeasure P hP x
      (transitionTrajectoryTail t ⁻¹' leadingOnesFiniteFirstCrossingSet i x t) = _
  rw [← Measure.map_apply htail hEvent]
  rw [transitionTrajectoryMeasure_map_tail_eq_finiteTrajectoryMeasure P hP x t]
  exact finiteTrajectoryMeasure_leadingOnesFiniteFirstCrossingSet hp0 hp1 i x

/-- Pre-crossing of the finite tail is equivalent to every absolute state strictly
before the terminal time lying below boundary `i`. -/
theorem leadingOnesPreCrossing_transitionTrajectoryTail_iff
    {n : ℕ} (i : Fin n) :
    ∀ (t : ℕ) (x : BitString n) (path : ℕ → BitString n),
      leadingOnesPreCrossing i t x (transitionTrajectoryTail t path) ↔
        ∀ r, r < t →
          leadingOnes (transitionTrajectoryState x path r) < i.val := by
  intro t
  induction t with
  | zero =>
      intro x path
      simp [leadingOnesPreCrossing]
  | succ t ih =>
      intro x path
      constructor
      · intro hpre r hr
        rcases hpre with ⟨hx, htail⟩
        cases r with
        | zero =>
            simpa using hx
        | succ r =>
            have hrlt : r < t := by omega
            have htail' := htail
            rw [Fin_tail_transitionTrajectoryTail t path] at htail'
            change
              leadingOnesPreCrossing i t (path 1)
                (transitionTrajectoryTail t (transitionTrajectoryShift path)) at htail'
            have hrec :=
              (ih (path 1) (transitionTrajectoryShift path)).1 htail' r hrlt
            rw [transitionTrajectoryState_shift x path r] at hrec
            exact hrec
      · intro hall
        constructor
        · have h0 := hall 0 (Nat.zero_lt_succ t)
          simpa using h0
        · have hrec :
              ∀ r, r < t →
                leadingOnes
                    (transitionTrajectoryState (path 1)
                      (transitionTrajectoryShift path) r) < i.val := by
            intro r hr
            have h := hall (r + 1) (by omega)
            rw [transitionTrajectoryState_shift x path r]
            exact h
          have htail :=
            (ih (path 1) (transitionTrajectoryShift path)).2 hrec
          change
            leadingOnesPreCrossing i t (path 1)
              (Fin.tail (transitionTrajectoryTail (t + 1) path))
          rw [Fin_tail_transitionTrajectoryTail t path]
          exact htail

/-- Pointwise absolute-time semantics of the exact-time first-crossing cylinder. -/
theorem mem_leadingOnesTrajectoryFirstCrossingSet_iff
    {n : ℕ} (i : Fin n) (x : BitString n)
    (t : ℕ) (path : ℕ → BitString n) :
    path ∈ leadingOnesTrajectoryFirstCrossingSet i x t ↔
      (∀ r, r < t →
        leadingOnes (transitionTrajectoryState x path r) < i.val) ∧
      i.val ≤ leadingOnes (transitionTrajectoryState x path t) := by
  unfold leadingOnesTrajectoryFirstCrossingSet
  change
    (leadingOnesPreCrossing i t x (transitionTrajectoryTail t path) ∧
      i.val ≤ leadingOnes
        (finiteTrajectoryTerminal t x (transitionTrajectoryTail t path))) ↔ _
  rw [leadingOnesPreCrossing_transitionTrajectoryTail_iff i t x path]
  simp only [finiteTrajectoryTerminal_transitionTrajectoryTail]

/-- Exact-time first-crossing cylinders are pairwise disjoint. -/
theorem pairwise_disjoint_leadingOnesTrajectoryFirstCrossingSet
    {n : ℕ} (i : Fin n) (x : BitString n) :
    Pairwise (Function.onFun Disjoint
      (leadingOnesTrajectoryFirstCrossingSet i x)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro path hs ht
  rw [mem_leadingOnesTrajectoryFirstCrossingSet_iff i x s path] at hs
  rw [mem_leadingOnesTrajectoryFirstCrossingSet_iff i x t path] at ht
  by_cases hlt : s < t
  · have hbelow := ht.1 s hlt
    omega
  · have hts : t < s := by omega
    have hbelow := hs.1 t hts
    omega

/-- Eventual boundary crossing is exactly the disjoint union over its unique finite
first-crossing time. -/
theorem leadingOnesEventuallyCrossesBoundarySet_eq_iUnion_firstCrossingSet
    {n : ℕ} (i : Fin n) (x : BitString n) :
    leadingOnesEventuallyCrossesBoundarySet i x =
      ⋃ t : ℕ, leadingOnesTrajectoryFirstCrossingSet i x t := by
  ext path
  constructor
  · intro hevent
    have hex : ∃ t : ℕ,
        i.val ≤ leadingOnes (transitionTrajectoryState x path t) :=
      (mem_leadingOnesEventuallyCrossesBoundarySet_iff i x path).1 hevent
    let t0 : ℕ := Nat.find hex
    have ht0 : i.val ≤ leadingOnes (transitionTrajectoryState x path t0) :=
      Nat.find_spec hex
    have hbefore : ∀ r, r < t0 →
        leadingOnes (transitionTrajectoryState x path r) < i.val := by
      intro r hr
      have hnot : ¬ i.val ≤ leadingOnes (transitionTrajectoryState x path r) :=
        Nat.find_min hex hr
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨t0, ?_⟩
    exact (mem_leadingOnesTrajectoryFirstCrossingSet_iff i x t0 path).2
      ⟨hbefore, ht0⟩
  · intro hunion
    rcases Set.mem_iUnion.mp hunion with ⟨t, ht⟩
    have ht' :=
      (mem_leadingOnesTrajectoryFirstCrossingSet_iff i x t path).1 ht
    exact (mem_leadingOnesEventuallyCrossesBoundarySet_iff i x path).2
      ⟨t, ht'.2⟩

/-- The eventual-crossing probability from one fixed initial state is exactly the
countable sum of the explicit finite first-crossing masses. -/
theorem transitionTrajectoryMeasure_eventualCrossing_eq_tsum_fixedInitialFirstCrossingMass
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) :
    transitionTrajectoryMeasure
        (onePlusOneTransition p (leadingOnesReal (n := n)))
        (onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))) x
        (leadingOnesEventuallyCrossesBoundarySet i x) =
      ∑' t : ℕ,
        ENNReal.ofReal (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
  rw [leadingOnesEventuallyCrossesBoundarySet_eq_iUnion_firstCrossingSet i x]
  rw [measure_iUnion
    (pairwise_disjoint_leadingOnesTrajectoryFirstCrossingSet i x)
    (fun t => measurableSet_leadingOnesTrajectoryFirstCrossingSet i x t)]
  apply tsum_congr
  intro t
  exact transitionTrajectoryMeasure_leadingOnesTrajectoryFirstCrossingSet
    hp0 hp1 i x t

/-- In the nondegenerate mutation regime, the fixed-initial first-crossing masses are
normalized: their countable sum is exactly one. -/
theorem tsum_leadingOnesFixedInitialFirstCrossingMass_eq_one
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (i : Fin n) (x : BitString n) :
    (∑' t : ℕ,
      ENNReal.ofReal (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x)) = 1 := by
  calc
    (∑' t : ℕ,
        ENNReal.ofReal (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x)) =
        transitionTrajectoryMeasure
          (onePlusOneTransition p (leadingOnesReal (n := n)))
          (onePlusOneTransition_stochastic hp0.le hp1.le
            (leadingOnesReal (n := n))) x
          (leadingOnesEventuallyCrossesBoundarySet i x) := by
      symm
      exact transitionTrajectoryMeasure_eventualCrossing_eq_tsum_fixedInitialFirstCrossingMass
        hp0.le hp1.le i x
    _ = 1 :=
      transitionTrajectoryMeasure_leadingOnesEventuallyCrossesBoundarySet
        hp0 hp1 i x

end ECRuntime
