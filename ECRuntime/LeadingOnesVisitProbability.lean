import ECRuntime.LeadingOnesFirstCrossingAggregate
import ECRuntime.LeadingOnesFirstCrossingMeasure
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
# Stage 27 fix 9: the one-half LeadingOnes visit probability

Stage 27 fix 8 fix 1 compiler-verifies the representation bridge between explicit
finite first-crossing path weights and the genuine infinite trajectory law.  In
particular, for every fixed initial state and every boundary `i`, the countable sum of
fixed-initial first-crossing masses is one when `0 < p < 1`.  Stage 27 fix 6 separately
compiler-verifies that the uniformly initialized exact-entry and strict-skip branches
have equal aggregate mass.

This file performs the remaining finite uniform-initialization averaging.  First, the
total finite first-crossing mass at one time is rewritten as the uniform average over
fixed initial states.  After embedding into `ENNReal`, the finite initial-state sum and
the countable time sum are interchanged.  The fixed-initial normalization then gives
unit total first-crossing mass under uniform initialization.  Finally, the already
verified per-time one-half identity is factored through the countable sum, yielding the
classical probability `1/2` of visiting any nonterminal LeadingOnes level.
-/

/-- The fixed-initial finite first-crossing mass is nonnegative for a stochastic
mutation parameter. -/
theorem leadingOnesFixedInitialFirstCrossingMass_nonneg
    {n t : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) (x : BitString n) :
    0 ≤ leadingOnesFixedInitialFirstCrossingMass (t := t) p i x := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition p (leadingOnesReal (n := n))
  let hP : IsStochastic P :=
    onePlusOneTransition_stochastic hp0 hp1 (leadingOnesReal (n := n))
  unfold leadingOnesFixedInitialFirstCrossingMass
  apply Finset.sum_nonneg
  intro path _hpath
  by_cases hcross : path ∈ leadingOnesFiniteFirstCrossingSet i x t
  · simp only [hcross, if_true]
    exact finiteTrajectoryWeight_nonneg P hP t x path
  · simp [hcross]

/-- At one fixed crossing time, the total uniformly initialized first-crossing mass is
exactly the uniform average of the corresponding fixed-initial masses. -/
theorem leadingOnesFirstCrossingMass_eq_uniform_average_fixedInitial
    {n t : ℕ} (p : ℝ) (i : Fin n) :
    leadingOnesFirstCrossingMass (t := t) p i =
      ((Fintype.card (BitString n) : ℝ)⁻¹) *
        ∑ x : BitString n,
          leadingOnesFixedInitialFirstCrossingMass (t := t) p i x := by
  classical
  unfold leadingOnesFirstCrossingMass
    leadingOnesFirstCrossingExactMass leadingOnesFirstCrossingSkipMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ h : LeadingOnesFiniteHistory n t,
        ((if leadingOnesFirstCrossingExact i h then
            leadingOnesUniformFiniteHistoryWeight p h
          else 0) +
         (if leadingOnesFirstCrossingSkip i h then
            leadingOnesUniformFiniteHistoryWeight p h
          else 0))) =
        ∑ h : LeadingOnesFiniteHistory n t,
          if h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t then
            leadingOnesUniformFiniteHistoryWeight p h
          else 0 := by
      apply Finset.sum_congr rfl
      intro h _hh
      by_cases hexact : leadingOnesFirstCrossingExact i h
      · have hcross : h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t :=
          (mem_leadingOnesFiniteFirstCrossingSet_iff_exact_or_skip i h.1 h.2).2
            (Or.inl hexact)
        have hnotSkip : ¬ leadingOnesFirstCrossingSkip i h := by
          intro hskip
          have htermEq := hexact.2
          have htermLt := hskip.2
          omega
        simp [hexact, hnotSkip, hcross]
      · by_cases hskip : leadingOnesFirstCrossingSkip i h
        · have hcross : h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t :=
            (mem_leadingOnesFiniteFirstCrossingSet_iff_exact_or_skip i h.1 h.2).2
              (Or.inr hskip)
          simp [hexact, hskip, hcross]
        · have hnotCross : h.2 ∉ leadingOnesFiniteFirstCrossingSet i h.1 t := by
            intro hcross
            rcases
                (mem_leadingOnesFiniteFirstCrossingSet_iff_exact_or_skip i h.1 h.2).1
                  hcross with hexact' | hskip'
            · exact hexact hexact'
            · exact hskip hskip'
          simp [hexact, hskip, hnotCross]
    _ = ∑ x : BitString n,
          ∑ path : FiniteTrajectory (BitString n) t,
            if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
              leadingOnesUniformFiniteHistoryWeight p (x, path)
            else 0 := by
      exact Fintype.sum_prod_type
        (fun h : BitString n × FiniteTrajectory (BitString n) t =>
          if h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t then
            leadingOnesUniformFiniteHistoryWeight p h
          else 0)
    _ = ∑ x : BitString n,
          ((Fintype.card (BitString n) : ℝ)⁻¹) *
            ∑ path : FiniteTrajectory (BitString n) t,
              if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
                finiteTrajectoryWeight
                  (onePlusOneTransition p (leadingOnesReal (n := n))) t x path
              else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hcross : path ∈ leadingOnesFiniteFirstCrossingSet i x t
      · simp [hcross, leadingOnesUniformFiniteHistoryWeight]
      · simp [hcross]
    _ = ((Fintype.card (BitString n) : ℝ)⁻¹) *
          ∑ x : BitString n,
            leadingOnesFixedInitialFirstCrossingMass (t := t) p i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rfl

/-- `ENNReal` form of the fixed-time uniform averaging identity. -/
theorem ofReal_leadingOnesFirstCrossingMass_eq_uniform_average_fixedInitial
    {n t : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin n) :
    ENNReal.ofReal (leadingOnesFirstCrossingMass (t := t) p i) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          ENNReal.ofReal
            (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
  classical
  rw [leadingOnesFirstCrossingMass_eq_uniform_average_fixedInitial p i]
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  have hcardNat : 0 < Fintype.card (BitString n) := Fintype.card_pos
  have hcardReal : 0 < (Fintype.card (BitString n) : ℝ) := by
    exact_mod_cast hcardNat
  have hfixed :
      ∀ x ∈ (Finset.univ : Finset (BitString n)),
        0 ≤ leadingOnesFixedInitialFirstCrossingMass (t := t) p i x := by
    intro x _hx
    exact leadingOnesFixedInitialFirstCrossingMass_nonneg hp0 hp1 i x
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcardReal.le)]
  rw [ENNReal.ofReal_inv_of_pos hcardReal]
  rw [ENNReal.ofReal_sum_of_nonneg hfixed]
  simp

/-- Summing total finite first-crossing mass over all crossing times gives unit mass under
uniform initialization. -/
theorem tsum_ofReal_leadingOnesFirstCrossingMass_eq_one
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    (∑' t : ℕ,
      ENNReal.ofReal (leadingOnesFirstCrossingMass (t := t) p i)) = 1 := by
  classical
  haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
  calc
    (∑' t : ℕ,
        ENNReal.ofReal (leadingOnesFirstCrossingMass (t := t) p i)) =
        ∑' t : ℕ,
          ((Fintype.card (BitString n) : ENNReal)⁻¹) *
            ∑ x : BitString n,
              ENNReal.ofReal
                (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
      apply tsum_congr
      intro t
      exact ofReal_leadingOnesFirstCrossingMass_eq_uniform_average_fixedInitial
        hp0.le hp1.le i
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑' t : ℕ,
          ∑ x : BitString n,
            ENNReal.ofReal
              (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x)) := by
      exact ENNReal.tsum_mul_left
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          ∑' t : ℕ,
            ENNReal.ofReal
              (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x)) := by
      congr 1
      calc
        (∑' t : ℕ,
            ∑ x : BitString n,
              ENNReal.ofReal
                (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x)) =
            ∑' t : ℕ,
              ∑' x : BitString n,
                ENNReal.ofReal
                  (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
          apply tsum_congr
          intro t
          rw [tsum_fintype]
        _ = ∑' x : BitString n,
              ∑' t : ℕ,
                ENNReal.ofReal
                  (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
          exact ENNReal.tsum_comm
        _ = ∑ x : BitString n,
              ∑' t : ℕ,
                ENNReal.ofReal
                  (leadingOnesFixedInitialFirstCrossingMass (t := t) p i x) := by
          rw [tsum_fintype]
    _ = ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n, (1 : ENNReal) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _hx
      exact tsum_leadingOnesFixedInitialFirstCrossingMass_eq_one hp0 hp1 i x
    _ = 1 := by
      have hcard : Fintype.card (BitString n) ≠ 0 := Fintype.card_ne_zero
      rw [Finset.sum_const, Finset.card_univ]
      simp only [nsmul_eq_mul, mul_one]
      apply ENNReal.inv_mul_cancel
      · exact_mod_cast hcard
      · exact ENNReal.natCast_ne_top _

/-- The uniformly initialized aggregate exact-entry mass is one half. -/
theorem leadingOnesEventualFirstCrossingExactMass_eq_ofReal_half
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesEventualFirstCrossingExactMass p i =
      ENNReal.ofReal (1 / 2 : ℝ) := by
  unfold leadingOnesEventualFirstCrossingExactMass
  calc
    (∑' t : ℕ,
        ENNReal.ofReal (leadingOnesFirstCrossingExactMass (t := t) p i)) =
        ∑' t : ℕ,
          ENNReal.ofReal (1 / 2 : ℝ) *
            ENNReal.ofReal (leadingOnesFirstCrossingMass (t := t) p i) := by
      apply tsum_congr
      intro t
      rw [leadingOnesFirstCrossingExactMass_eq_half_crossingMass (t := t) p i]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ = ENNReal.ofReal (1 / 2 : ℝ) *
        (∑' t : ℕ,
          ENNReal.ofReal (leadingOnesFirstCrossingMass (t := t) p i)) := by
      exact ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [tsum_ofReal_leadingOnesFirstCrossingMass_eq_one hp0 hp1 i]
      simp

/-- `ENNReal` normalization of the real one-half constant. -/
theorem ENNReal_ofReal_half :
    ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The classical one-half visit probability for every nonterminal LeadingOnes level. -/
theorem leadingOnesEventualFirstCrossingExactMass_eq_half
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesEventualFirstCrossingExactMass p i = (2 : ENNReal)⁻¹ := by
  rw [leadingOnesEventualFirstCrossingExactMass_eq_ofReal_half hp0 hp1 i]
  exact ENNReal_ofReal_half

/-- By symmetry, the aggregate strict-skip mass is also one half. -/
theorem leadingOnesEventualFirstCrossingSkipMass_eq_half
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesEventualFirstCrossingSkipMass p i = (2 : ENNReal)⁻¹ := by
  rw [← leadingOnesEventualFirstCrossingExactMass_eq_skipMass p i]
  exact leadingOnesEventualFirstCrossingExactMass_eq_half hp0 hp1 i

/-- Consequently the aggregate total first-crossing mass is one. -/
theorem leadingOnesEventualFirstCrossingMass_eq_one
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesEventualFirstCrossingMass p i = 1 := by
  unfold leadingOnesEventualFirstCrossingMass
  rw [leadingOnesEventualFirstCrossingExactMass_eq_half hp0 hp1 i]
  rw [leadingOnesEventualFirstCrossingSkipMass_eq_half hp0 hp1 i]
  rw [← ENNReal_ofReal_half]
  rw [← ENNReal.ofReal_add
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

/-- Canonical name for the uniform probability mass of ever visiting exact LeadingOnes
level `i`: by elitist monotonicity this is precisely the aggregate exact first-crossing
mass. -/
noncomputable def leadingOnesUniformLevelVisitMass
    {n : ℕ} (p : ℝ) (i : Fin n) : ENNReal :=
  leadingOnesEventualFirstCrossingExactMass p i

/-- Under nondegenerate standard bit mutation, every nonterminal LeadingOnes level is
visited with probability exactly one half from uniform initialization. -/
theorem leadingOnesUniformLevelVisitMass_eq_half
    {n : ℕ} [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (i : Fin n) :
    leadingOnesUniformLevelVisitMass p i = (2 : ENNReal)⁻¹ := by
  unfold leadingOnesUniformLevelVisitMass
  exact leadingOnesEventualFirstCrossingExactMass_eq_half hp0 hp1 i

end ECRuntime
