import ECRuntime.WittStandardPotential
import ECRuntime.LinearRuntime
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 31: one-step drift interface for Witt's standard-rate potential

Stage 30 introduced the refined geometric potential used in Witt's sharp `p = 1/n`
linear-function argument.  This module starts the stochastic part of that proof while
keeping the genuinely delicate aggregate estimates isolated.

The main facts established here are:

* exact one-step drift as a finite mutation-mask sum;
* exact accepted/rejected potential-drop formulas;
* exact contribution of the zero-singleton masks;
* the zero-singleton contribution alone is at least `V/(e n)` at standard mutation;
* C1 masks contribute zero for every auxiliary error potential;
* accepted C2B masks have zero Witt-potential drop because the forced swap is between
  equal objective weights, hence equal Witt coefficients;
* exact decomposition into the proved singleton term plus a non-singleton remainder;
* a clean certificate saying that nonnegativity of this remainder implies the desired
  multiplicative drift theorem.

Thus the remaining mathematical work is no longer hidden inside the transition kernel:
for ordered positive linear objectives and `n >= 4`, it suffices to prove that the
aggregate non-singleton remainder is nonnegative.  In Witt's proof this is the union of
the C2A multi-flip branch and the C3 branch.
-/

/-- The refined Witt potential is the sum of its coefficients over currently-zero bits. -/
theorem wittStandardLinearPotential_eq_sum_zeroPositions {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) :
    wittStandardLinearPotential w x =
      ∑ i ∈ zeroPositions x, wittStandardPotentialWeight w i := by
  exact linearErrorPotential_eq_sum_zeroPositions
    (wittStandardPotentialWeight w) x

/-- Accepted mutations expose the raw signed Witt-potential change. -/
theorem wittStandardLinearPotential_selected_drop_of_accepts {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) =
      ∑ i, flipContribution (wittStandardPotentialWeight w) x mask i := by
  simpa [wittStandardLinearPotential] using
    (linearErrorPotential_selected_drop_of_accepts
      w (wittStandardPotentialWeight w) x mask hacc)

/-- Rejected mutations leave the Witt potential unchanged. -/
theorem wittStandardLinearPotential_selected_drop_of_rejects {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : ¬ Accepts (linearFitness w) x (mutateWithMask x mask)) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  simpa [wittStandardLinearPotential] using
    (linearErrorPotential_selected_drop_of_rejects
      w (wittStandardPotentialWeight w) x mask hacc)

/-- A singleton zero-to-one mutation is accepted and drops the Witt potential by its coefficient. -/
theorem wittStandardLinearPotential_selected_single_zero_flip_drop {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x ({i} : MutationMask n)) =
      wittStandardPotentialWeight w i := by
  have himprove := linearFitness_single_zero_flip_improves w hw x i hi
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask n)) := by
    exact le_of_lt himprove
  rw [wittStandardLinearPotential_selected_drop_of_accepts
    w x ({i} : MutationMask n) hacc]
  simp [flipContribution, hi]

/-- One-step Witt-potential drift written directly as a mutation-mask expectation. -/
theorem wittStandardLinear_drift_eq_mask_sum {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (wittStandardLinearPotential w) x =
      ∑ mask : MutationMask n,
        mutationMaskWeight p mask *
          (wittStandardLinearPotential w x -
            wittStandardLinearPotential w
              (selectedAfterMask (linearFitness w) x mask)) := by
  exact onePlusOneTransition_drift_eq_mask_sum
    p (linearFitness w) (wittStandardLinearPotential w) x

/-- The simple zero-singleton events contribute exactly the singleton rate times the Witt potential. -/
theorem wittStandard_zeroSingleton_contribution_eq
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ zeroSingletonMasks x,
      mutationMaskWeight p mask *
        (wittStandardLinearPotential w x -
          wittStandardLinearPotential w
            (selectedAfterMask (linearFitness w) x mask))) =
      linearSingletonRate n p * wittStandardLinearPotential w x := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))
  have hcoord :
      ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) =
        linearSingletonRate n p * wittStandardLinearPotential w x := by
    rw [wittStandardLinearPotential_eq_sum_zeroPositions, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hzero : x i = false := (mem_zeroPositions x i).mp hi
    dsimp [F]
    rw [mutationMaskWeight_singleton,
      wittStandardLinearPotential_selected_single_zero_flip_drop w hw x i hzero]
    rfl
  calc
    (∑ mask ∈ zeroSingletonMasks x,
      mutationMaskWeight p mask *
        (wittStandardLinearPotential w x -
          wittStandardLinearPotential w
            (selectedAfterMask (linearFitness w) x mask))) =
        ∑ mask ∈ zeroSingletonMasks x, F mask := by rfl
    _ = ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) := by
      unfold zeroSingletonMasks
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Finset.singleton_injective hab
    _ = linearSingletonRate n p * wittStandardLinearPotential w x := hcoord

/-- The sharp standard-rate drift constant `1/(e n)`. -/
noncomputable def wittStandardLinearDriftRate (n : ℕ) : ℝ :=
  1 / (Real.exp 1 * (n : ℝ))

/-- The sharp standard-rate drift constant is positive in positive dimension. -/
theorem wittStandardLinearDriftRate_pos {n : ℕ} (hn : 0 < n) :
    0 < wittStandardLinearDriftRate n := by
  unfold wittStandardLinearDriftRate
  exact div_pos (by norm_num) (mul_pos (Real.exp_pos 1) (by exact_mod_cast hn))

/-- The sharp drift constant is no larger than the exact standard singleton rate. -/
theorem wittStandardLinearDriftRate_le_standardSingletonRate
    {n : ℕ} (hn : 2 ≤ n) :
    wittStandardLinearDriftRate n ≤
      linearSingletonRate n (standardMutationRate n) := by
  simpa [wittStandardLinearDriftRate] using
    (standard_linearSingletonRate_ge_inv_en hn)

/-- The zero-singleton branch alone already supplies the target `V/(e n)` contribution. -/
theorem wittStandardLinearDriftRate_mul_potential_le_zeroSingletonContribution
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    wittStandardLinearDriftRate n * wittStandardLinearPotential w x ≤
      ∑ mask ∈ zeroSingletonMasks x,
        mutationMaskWeight (standardMutationRate n) mask *
          (wittStandardLinearPotential w x -
            wittStandardLinearPotential w
              (selectedAfterMask (linearFitness w) x mask)) := by
  rw [wittStandard_zeroSingleton_contribution_eq
    (p := standardMutationRate n) w hw x]
  exact mul_le_mul_of_nonneg_right
    (wittStandardLinearDriftRate_le_standardSingletonRate hn)
    (wittStandardLinearPotential_nonneg w x)

/--
For positive objective weights, a C1 mutation changes no auxiliary weighted-error
potential after elitist selection.  This generic form is useful beyond the Witt weights.
-/
theorem linearErrorPotential_selected_drop_eq_zero_of_caseC1 {n : ℕ}
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n)
    (hC1 : IsClassicalLinearCaseC1 x mask) :
    linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) = 0 := by
  have hzeroempty : zeroToOneFlips x mask = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [IsClassicalLinearCaseC1, zeroToOneFlipCount] using hC1
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · have hbalance := (accepts_linearFitness_iff_flip_sums w x mask).mp hacc
    rw [hzeroempty] at hbalance
    simp at hbalance
    have hnonneg : 0 ≤ ∑ i ∈ oneToZeroFlips x mask, w i := by
      apply Finset.sum_nonneg
      intro i hi
      exact (hw i).le
    have hsum0 : (∑ i ∈ oneToZeroFlips x mask, w i) = 0 :=
      le_antisymm hbalance hnonneg
    have honeempty : oneToZeroFlips x mask = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hle : w i ≤ ∑ j ∈ oneToZeroFlips x mask, w j :=
        Finset.single_le_sum (fun j hj => (hw j).le) hi
      rw [hsum0] at hle
      exact (not_le_of_gt (hw i)) hle
    rw [linearErrorPotential_selected_drop_of_accepts w g x mask hacc,
      flipContribution_sum_eq_flip_sums, hzeroempty, honeempty]
    simp
  · exact linearErrorPotential_selected_drop_of_rejects w g x mask hacc

/-- C1 masks therefore have exactly zero Witt-potential drop. -/
theorem wittStandardLinearPotential_selected_drop_eq_zero_of_caseC1 {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n)
    (hC1 : IsClassicalLinearCaseC1 x mask) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  simpa [wittStandardLinearPotential] using
    (linearErrorPotential_selected_drop_eq_zero_of_caseC1
      w (wittStandardPotentialWeight w) hw x mask hC1)

/-- The complete C1 contribution to Witt drift is zero. -/
theorem wittStandard_caseC1_contribution_eq_zero
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ classicalLinearCaseC1Masks x,
      mutationMaskWeight p mask *
        (wittStandardLinearPotential w x -
          wittStandardLinearPotential w
            (selectedAfterMask (linearFitness w) x mask))) = 0 := by
  apply Finset.sum_eq_zero
  intro mask hmask
  have hC1 : IsClassicalLinearCaseC1 x mask :=
    (mem_classicalLinearCaseC1Masks x mask).mp hmask
  rw [wittStandardLinearPotential_selected_drop_eq_zero_of_caseC1
    w hw x mask hC1]
  ring

/--
The accepted C2B swap has zero Witt-potential drop.  The deterministic C2B structure
forces an equal-objective-weight pair, and Stage 30 proved that equal objective weights
receive equal Witt coefficients.
-/
theorem wittStandardLinearPotential_selected_drop_eq_zero_of_caseC2B_of_accepts
    {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hB : IsClassicalLinearCaseC2B x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  rcases accepted_caseC2B_eq_equalWeight_pair w hw hmono x mask i hB hacc with
    ⟨j, _hj, _hji, hwji, hone, _hmask⟩
  have hzero : zeroToOneFlips x mask = {i} := hB.1
  rw [wittStandardLinearPotential_selected_drop_of_accepts w x mask hacc,
    flipContribution_sum_eq_flip_sums, hzero, hone]
  simp only [Finset.sum_singleton]
  rw [wittStandardPotentialWeight_eq_of_weight_eq w hwji]
  ring

/-- Rejected or accepted, every C2B mask has zero selected Witt-potential drop. -/
theorem wittStandardLinearPotential_selected_drop_eq_zero_of_caseC2B
    {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hB : IsClassicalLinearCaseC2B x mask i) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · exact wittStandardLinearPotential_selected_drop_eq_zero_of_caseC2B_of_accepts
      w hw hmono x mask i hB hacc
  · exact wittStandardLinearPotential_selected_drop_of_rejects w x mask hacc

/-- Mutation masks outside the already-accounted-for zero-singleton events. -/
def wittStandardRemainderMasks {n : ℕ} (x : BitString n) : Finset (MutationMask n) :=
  Finset.univ \ zeroSingletonMasks x

/-- Aggregate contribution of all non-zero-singleton masks to one-step Witt drift. -/
noncomputable def wittStandardRemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ wittStandardRemainderMasks x,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Exact decomposition of Witt drift into the singleton term and one remainder. -/
theorem wittStandardLinear_drift_eq_singleton_add_remainder
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (wittStandardLinearPotential w) x =
      linearSingletonRate n p * wittStandardLinearPotential w x +
        wittStandardRemainderContribution p w x := by
  rw [wittStandardLinear_drift_eq_mask_sum]
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))
  change (∑ mask : MutationMask n, F mask) =
    linearSingletonRate n p * wittStandardLinearPotential w x +
      wittStandardRemainderContribution p w x
  have hsubset : zeroSingletonMasks x ⊆
      (Finset.univ : Finset (MutationMask n)) := Finset.subset_univ _
  have hsplit := Finset.sum_sdiff (f := F) hsubset
  have hsum :
      (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ wittStandardRemainderMasks x, F mask) := by
    change (∑ mask : MutationMask n, F mask) =
      (∑ mask ∈ zeroSingletonMasks x, F mask) +
        (∑ mask ∈ ((Finset.univ : Finset (MutationMask n)) \ zeroSingletonMasks x), F mask)
    simpa only [add_comm] using hsplit.symm
  calc
    (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ wittStandardRemainderMasks x, F mask) := hsum
    _ = linearSingletonRate n p * wittStandardLinearPotential w x +
        wittStandardRemainderContribution p w x := by
      have hsingle :
          (∑ mask ∈ zeroSingletonMasks x, F mask) =
            linearSingletonRate n p * wittStandardLinearPotential w x := by
        simpa [F] using
          (wittStandard_zeroSingleton_contribution_eq (p := p) w hw x)
      rw [hsingle]
      rfl

/-- The isolated Stage-31 certificate left by Witt's non-singleton case analysis. -/
def HasWittStandardRemainderNonnegativity {n : ℕ} (w : Fin n → ℝ) : Prop :=
  ∀ x : BitString n,
    0 ≤ wittStandardRemainderContribution (standardMutationRate n) w x

/-- A nonnegative non-singleton remainder yields the sharp `1/(e n)` pointwise drift. -/
theorem wittStandardLinearDriftRate_mul_potential_le_drift_of_remainder_nonnegative
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hrem : HasWittStandardRemainderNonnegativity w)
    (x : BitString n) :
    wittStandardLinearDriftRate n * wittStandardLinearPotential w x ≤
      driftAt
        (onePlusOneTransition (standardMutationRate n) (linearFitness w))
        (wittStandardLinearPotential w) x := by
  rw [wittStandardLinear_drift_eq_singleton_add_remainder
    (p := standardMutationRate n) w hw x]
  have hV : 0 ≤ wittStandardLinearPotential w x :=
    wittStandardLinearPotential_nonneg w x
  have hrate := wittStandardLinearDriftRate_le_standardSingletonRate hn
  have hsingle := mul_le_mul_of_nonneg_right hrate hV
  have hrest := hrem x
  linarith

/-- The same reduction packaged in the generic multiplicative-drift interface. -/
theorem wittStandard_hasMultiplicativeDriftLowerBound_of_remainder_nonnegative
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hrem : HasWittStandardRemainderNonnegativity w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (standardMutationRate n) (linearFitness w))
      (wittStandardLinearPotential w)
      (wittStandardLinearDriftRate n) := by
  intro x _hx
  exact wittStandardLinearDriftRate_mul_potential_le_drift_of_remainder_nonnegative
    hn w hw hrem x

end ECRuntime
