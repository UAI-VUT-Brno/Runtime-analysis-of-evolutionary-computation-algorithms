import ECRuntime.AdaptiveLeadingOnesFiniteCrossingParity
import ECRuntime.LeadingOnesFirstCrossingMeasure
import Mathlib

namespace ECRuntime

/-!
Stage 222 (NEW, unapproved): a finite-time averaging identity for an
adaptive LeadingOnes process. This follows the fixed-rate analogue from
LeadingOnesVisitProbability. It is needed to connect the history-sum
normalization to statewise hitting-time semantics.
-/

/-- From one specified initial state, the unnormalized mass of the first
crossing at time `t` of boundary `i` under an adaptive rate schedule. -/
noncomputable def leadingOnesAdaptiveFixedInitialFirstCrossingMass
    {n t : Nat} (rate : Nat -> Real) (i : Fin n) (x : BitString n) : Real := by
  classical
  exact ∑ path : FiniteTrajectory (BitString n) t,
    if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
      finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t x path
    else 0

/-- Total mass (both exact entry and skip) at one finite crossing time. -/
noncomputable def leadingOnesAdaptiveFirstCrossingTotalMass
    {n t : Nat} (rate : Nat -> Real) (i : Fin n) : Real :=
  leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i +
    leadingOnesAdaptiveFirstCrossingSkipMass (t := t) rate i

/-- At every finite time, uniformly initialized crossing mass is the uniform
average of the corresponding fixed-initial-state first-crossing masses. -/
theorem proposed_leadingOnesAdaptive_firstCrossingTotal_eq_uniformAverage
    {n t : Nat} (rate : Nat -> Real) (i : Fin n) :
    leadingOnesAdaptiveFirstCrossingTotalMass (t := t) rate i =
      ((Fintype.card (BitString n) : Real)⁻¹) *
        ∑ x : BitString n,
          leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x := by
  classical
  unfold leadingOnesAdaptiveFirstCrossingTotalMass
    leadingOnesAdaptiveFirstCrossingExactMass
    leadingOnesAdaptiveFirstCrossingSkipMass
  rw [← Finset.sum_add_distrib]
  calc
    (∑ h : LeadingOnesFiniteHistory n t,
        ((if leadingOnesFirstCrossingExact i h then
            leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0) +
         (if leadingOnesFirstCrossingSkip i h then
            leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0))) =
        ∑ h : LeadingOnesFiniteHistory n t,
          if h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t then
            leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0 := by
      apply Finset.sum_congr rfl
      intro h _hh
      by_cases hexact : leadingOnesFirstCrossingExact i h
      · have hcross : h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t :=
          (mem_leadingOnesFiniteFirstCrossingSet_iff_exact_or_skip i h.1 h.2).2
            (Or.inl hexact)
        have hnotSkip : ¬ leadingOnesFirstCrossingSkip i h := by
          intro hskip
          have heq := hexact.2
          have hlt := hskip.2
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
              leadingOnesAdaptiveUniformFiniteHistoryWeight rate (x, path)
            else 0 := by
      exact Fintype.sum_prod_type
        (fun h : BitString n × FiniteTrajectory (BitString n) t =>
          if h.2 ∈ leadingOnesFiniteFirstCrossingSet i h.1 t then
            leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0)
    _ = ∑ x : BitString n,
          ((Fintype.card (BitString n) : Real)⁻¹) *
            ∑ path : FiniteTrajectory (BitString n) t,
              if path ∈ leadingOnesFiniteFirstCrossingSet i x t then
                finiteTrajectoryWeight (leadingOnesAdaptiveTransition rate) t x path
              else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro path _hpath
      by_cases hcross : path ∈ leadingOnesFiniteFirstCrossingSet i x t
      · simp [hcross, leadingOnesAdaptiveUniformFiniteHistoryWeight]
      · simp [hcross]
    _ = ((Fintype.card (BitString n) : Real)⁻¹) *
          ∑ x : BitString n,
            leadingOnesAdaptiveFixedInitialFirstCrossingMass (t := t) rate i x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rfl

end ECRuntime
