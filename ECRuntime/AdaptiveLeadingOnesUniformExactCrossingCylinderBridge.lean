import ECRuntime.AdaptiveLeadingOnesFiniteCrossingParity
import ECRuntime.LeadingOnesExactEntryStep
import ECRuntime.LeadingOnesExactStayBranch
import ECRuntime.GenericFiniteCylinderMarginal
import ECRuntime.AdaptiveLeadingOnesFirstCrossingFixedInitialAverage
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! P01: the remaining finite-history *exact* branch. The existing
Stage-222 averaging theorem concerns first crossing into `>= i` (the
sum of exact and skip branches). This stage must NOT use that total
as if it were the exact branch. The exact terminal-level restriction
must be carried through finite-cylinder marginalization before
uniform averaging. -/

/-- Uniform average of the genuine *exact-landing* crossing cylinders
is the finite-history exact branch. There is deliberately no
factor of two: the skip branch is excluded on both sides. -/
theorem proposed_leadingOnesAdaptive_uniformExactCrossingCylinder_eq_historyMass
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (t : Nat) :
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
      (∑ x : BitString n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          (leadingOnesTrajectoryFirstCrossingExactSet i x t)) =
      ENNReal.ofReal (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i) := by
  classical
  let P : TransitionMatrix (BitString n) := leadingOnesAdaptiveTransition rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  let a : BitString n → Real := fun x =>
    ∑ path : FiniteTrajectory (BitString n) t,
      if path ∈ leadingOnesFiniteFirstCrossingExactSet i x t then
        finiteTrajectoryWeight P t x path else 0
  have hfinite (x : BitString n) :
      transitionTrajectoryMeasure P hP x
        (leadingOnesTrajectoryFirstCrossingExactSet i x t) =
        ENNReal.ofReal (a x) := by
    change transitionTrajectoryMeasure P hP x
      ((transitionTrajectoryTail t) ⁻¹'
        (leadingOnesFiniteFirstCrossingExactSet i x t)) = _
    rw [proposed_transitionTrajectoryMeasure_finiteCylinder_eq_finiteMeasure
      P hP x t (leadingOnesFiniteFirstCrossingExactSet i x t)
      (measurableSet_leadingOnesFiniteFirstCrossingExactSet i x)]
    rw [finiteTrajectoryMeasure_apply_eq_ofReal_setWeight
      P hP t x (leadingOnesFiniteFirstCrossingExactSet i x t)]
    rfl
  have ha (x : BitString n) : 0 ≤ a x := by
    apply Finset.sum_nonneg
    intro path _
    by_cases he : path ∈ leadingOnesFiniteFirstCrossingExactSet i x t
    · simpa [a, he] using finiteTrajectoryWeight_nonneg P hP t x path
    · simp [he]
  have hcard : 0 < (Fintype.card (BitString n) : Real) := by
    haveI : Nonempty (BitString n) := ⟨fun _ => false⟩
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (BitString n))
  have hreal :
      leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i =
        ((Fintype.card (BitString n) : Real)⁻¹) *
          (∑ x : BitString n, a x) := by
    unfold leadingOnesAdaptiveFirstCrossingExactMass
    calc
      (∑ h : LeadingOnesFiniteHistory n t,
        if leadingOnesFirstCrossingExact i h then
          leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0) =
          ∑ x : BitString n,
            ∑ path : FiniteTrajectory (BitString n) t,
              if leadingOnesFirstCrossingExact i (x, path) then
                leadingOnesAdaptiveUniformFiniteHistoryWeight rate (x, path)
              else 0 := by
                exact Fintype.sum_prod_type
                  (fun h : BitString n × FiniteTrajectory (BitString n) t =>
                    if leadingOnesFirstCrossingExact i h then
                      leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0)
      _ = ∑ x : BitString n,
            ((Fintype.card (BitString n) : Real)⁻¹) * a x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro path _
          change
            (if path ∈ leadingOnesFiniteFirstCrossingExactSet i x t then
              ((Fintype.card (BitString n) : Real)⁻¹) *
                finiteTrajectoryWeight P t x path else 0) =
            ((Fintype.card (BitString n) : Real)⁻¹) *
              (if path ∈ leadingOnesFiniteFirstCrossingExactSet i x t then
                finiteTrajectoryWeight P t x path else 0)
          split_ifs <;> simp
      _ = ((Fintype.card (BitString n) : Real)⁻¹) *
            (∑ x : BitString n, a x) := by
          rw [Finset.mul_sum]
  have hnonneg : ∀ x ∈ (Finset.univ : Finset (BitString n)), 0 ≤ a x :=
    fun x _ => ha x
  calc
    ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          transitionTrajectoryMeasure P hP x
            (leadingOnesTrajectoryFirstCrossingExactSet i x t)) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n, ENNReal.ofReal (a x)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro x _
          exact hfinite x
    _ = ENNReal.ofReal
          (((Fintype.card (BitString n) : Real)⁻¹) *
            (∑ x : BitString n, a x)) := by
          rw [ENNReal.ofReal_mul (inv_nonneg.mpr hcard.le)]
          rw [ENNReal.ofReal_inv_of_pos hcard]
          rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
          simp
    _ = ENNReal.ofReal
          (leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i) := by
          rw [hreal]

end ECRuntime
