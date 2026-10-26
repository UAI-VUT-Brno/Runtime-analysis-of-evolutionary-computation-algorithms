import ECRuntime.WittMutationPotential
import ECRuntime.WittStandardDrift
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 43: one-step drift interface for the mutation-rate parameterized Witt potential

Stage 42 introduced the potential

`V_p(x) = linearErrorPotential (wittMutationPotentialWeight p w) x`,

whose geometric base is reciprocal to the survival factor `1-p`.  This module lifts the
compiler-promoted Stage-31 one-step decomposition to that parameterized potential without
yet replaying the aggregate C3 or strict-tail estimates.

The main facts are deliberately rate-agnostic:

* accepted/rejected mutations expose the same signed coefficient change;
* a singleton zero-to-one mutation drops `V_p` by its parameterized coefficient;
* all zero-singleton masks contribute exactly `p(1-p)^(n-1) * V_p(x)`;
* C1 masks contribute zero;
* accepted or rejected C2B masks contribute zero because equal objective weights receive
  equal parameterized Witt coefficients;
* the full drift splits exactly into the singleton term plus a non-singleton remainder;
* nonnegativity of that remainder yields multiplicative drift with the exact singleton
  rate `linearSingletonRate n p`.

At `p = 1/n`, the new remainder is proved equal to the already promoted standard-rate
remainder.  Hence the general-rate branch is an exact extension of Stage 31 rather than a
parallel formalization.
-/

/-- The parameterized Witt potential is the sum of its coefficients over currently-zero bits. -/
theorem wittMutationLinearPotential_eq_sum_zeroPositions {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittMutationLinearPotential p w x =
      ∑ i ∈ zeroPositions x, wittMutationPotentialWeight p w i := by
  exact linearErrorPotential_eq_sum_zeroPositions
    (wittMutationPotentialWeight p w) x

/-- Accepted mutations expose the raw signed parameterized-Witt potential change. -/
theorem wittMutationLinearPotential_selected_drop_of_accepts {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) =
      ∑ i, flipContribution (wittMutationPotentialWeight p w) x mask i := by
  simpa [wittMutationLinearPotential] using
    (linearErrorPotential_selected_drop_of_accepts
      w (wittMutationPotentialWeight p w) x mask hacc)

/-- Rejected mutations leave the parameterized Witt potential unchanged. -/
theorem wittMutationLinearPotential_selected_drop_of_rejects {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : ¬ Accepts (linearFitness w) x (mutateWithMask x mask)) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  simpa [wittMutationLinearPotential] using
    (linearErrorPotential_selected_drop_of_rejects
      w (wittMutationPotentialWeight p w) x mask hacc)

/-- A singleton zero-to-one mutation is accepted and drops the parameterized potential
by the coefficient of the improved coordinate. -/
theorem wittMutationLinearPotential_selected_single_zero_flip_drop {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x ({i} : MutationMask n)) =
      wittMutationPotentialWeight p w i := by
  have himprove := linearFitness_single_zero_flip_improves w hw x i hi
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask n)) := by
    exact le_of_lt himprove
  rw [wittMutationLinearPotential_selected_drop_of_accepts
    p w x ({i} : MutationMask n) hacc]
  simp [flipContribution, hi]

/-- One-step drift of the parameterized Witt potential written as a mutation-mask sum. -/
theorem wittMutationLinear_drift_eq_mask_sum {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (wittMutationLinearPotential p w) x =
      ∑ mask : MutationMask n,
        mutationMaskWeight p mask *
          (wittMutationLinearPotential p w x -
            wittMutationLinearPotential p w
              (selectedAfterMask (linearFitness w) x mask)) := by
  exact onePlusOneTransition_drift_eq_mask_sum
    p (linearFitness w) (wittMutationLinearPotential p w) x

/-- The zero-singleton branch contributes exactly the singleton mutation rate times
`V_p(x)`. -/
theorem wittMutation_zeroSingleton_contribution_eq
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ zeroSingletonMasks x,
      mutationMaskWeight p mask *
        (wittMutationLinearPotential p w x -
          wittMutationLinearPotential p w
            (selectedAfterMask (linearFitness w) x mask))) =
      linearSingletonRate n p * wittMutationLinearPotential p w x := by
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))
  have hcoord :
      ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) =
        linearSingletonRate n p * wittMutationLinearPotential p w x := by
    rw [wittMutationLinearPotential_eq_sum_zeroPositions, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hzero : x i = false := (mem_zeroPositions x i).mp hi
    dsimp [F]
    rw [mutationMaskWeight_singleton,
      wittMutationLinearPotential_selected_single_zero_flip_drop p w hw x i hzero]
    rfl
  calc
    (∑ mask ∈ zeroSingletonMasks x,
      mutationMaskWeight p mask *
        (wittMutationLinearPotential p w x -
          wittMutationLinearPotential p w
            (selectedAfterMask (linearFitness w) x mask))) =
        ∑ mask ∈ zeroSingletonMasks x, F mask := by rfl
    _ = ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) := by
      unfold zeroSingletonMasks
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Finset.singleton_injective hab
    _ = linearSingletonRate n p * wittMutationLinearPotential p w x := hcoord

/-- C1 masks have zero selected drop for the parameterized Witt potential. -/
theorem wittMutationLinearPotential_selected_drop_eq_zero_of_caseC1 {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n)
    (hC1 : IsClassicalLinearCaseC1 x mask) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  simpa [wittMutationLinearPotential] using
    (linearErrorPotential_selected_drop_eq_zero_of_caseC1
      w (wittMutationPotentialWeight p w) hw x mask hC1)

/-- The complete C1 contribution to the parameterized Witt drift is zero. -/
theorem wittMutation_caseC1_contribution_eq_zero
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ classicalLinearCaseC1Masks x,
      mutationMaskWeight p mask *
        (wittMutationLinearPotential p w x -
          wittMutationLinearPotential p w
            (selectedAfterMask (linearFitness w) x mask))) = 0 := by
  apply Finset.sum_eq_zero
  intro mask hmask
  have hC1 : IsClassicalLinearCaseC1 x mask :=
    (mem_classicalLinearCaseC1Masks x mask).mp hmask
  rw [wittMutationLinearPotential_selected_drop_eq_zero_of_caseC1
    p w hw x mask hC1]
  ring

/-- An accepted C2B swap has zero parameterized Witt-potential drop because the two
forced coordinates have equal objective weights and therefore equal coefficients. -/
theorem wittMutationLinearPotential_selected_drop_eq_zero_of_caseC2B_of_accepts
    {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hB : IsClassicalLinearCaseC2B x mask i)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  rcases accepted_caseC2B_eq_equalWeight_pair w hw hmono x mask i hB hacc with
    ⟨j, _hj, _hji, hwji, hone, _hmask⟩
  have hzero : zeroToOneFlips x mask = {i} := hB.1
  rw [wittMutationLinearPotential_selected_drop_of_accepts p w x mask hacc,
    flipContribution_sum_eq_flip_sums, hzero, hone]
  simp only [Finset.sum_singleton]
  rw [wittMutationPotentialWeight_eq_of_weight_eq p w hwji]
  ring

/-- Rejected or accepted, every C2B mask has zero selected parameterized-Witt drop. -/
theorem wittMutationLinearPotential_selected_drop_eq_zero_of_caseC2B
    {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (mask : MutationMask n) (i : Fin n)
    (hB : IsClassicalLinearCaseC2B x mask i) :
    wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) = 0 := by
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · exact wittMutationLinearPotential_selected_drop_eq_zero_of_caseC2B_of_accepts
      p w hw hmono x mask i hB hacc
  · exact wittMutationLinearPotential_selected_drop_of_rejects p w x mask hacc

/-- Mutation masks outside the already-accounted-for zero-singleton events. -/
def wittMutationRemainderMasks {n : ℕ} (x : BitString n) : Finset (MutationMask n) :=
  Finset.univ \ zeroSingletonMasks x

/-- The parameterized and standard Stage-31 remainder partitions are literally the same
mask set. -/
theorem wittMutationRemainderMasks_eq_wittStandardRemainderMasks {n : ℕ}
    (x : BitString n) :
    wittMutationRemainderMasks x = wittStandardRemainderMasks x := by
  rfl

/-- Aggregate contribution of all non-zero-singleton masks to parameterized Witt drift. -/
noncomputable def wittMutationRemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ wittMutationRemainderMasks x,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

/-- Exact decomposition into the singleton term and one non-singleton remainder. -/
theorem wittMutationLinear_drift_eq_singleton_add_remainder
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (wittMutationLinearPotential p w) x =
      linearSingletonRate n p * wittMutationLinearPotential p w x +
        wittMutationRemainderContribution p w x := by
  rw [wittMutationLinear_drift_eq_mask_sum]
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))
  change (∑ mask : MutationMask n, F mask) =
    linearSingletonRate n p * wittMutationLinearPotential p w x +
      wittMutationRemainderContribution p w x
  have hsubset : zeroSingletonMasks x ⊆
      (Finset.univ : Finset (MutationMask n)) := Finset.subset_univ _
  have hsplit := Finset.sum_sdiff (f := F) hsubset
  have hsum :
      (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ wittMutationRemainderMasks x, F mask) := by
    change (∑ mask : MutationMask n, F mask) =
      (∑ mask ∈ zeroSingletonMasks x, F mask) +
        (∑ mask ∈ ((Finset.univ : Finset (MutationMask n)) \ zeroSingletonMasks x),
          F mask)
    simpa only [add_comm] using hsplit.symm
  calc
    (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ wittMutationRemainderMasks x, F mask) := hsum
    _ = linearSingletonRate n p * wittMutationLinearPotential p w x +
        wittMutationRemainderContribution p w x := by
      have hsingle :
          (∑ mask ∈ zeroSingletonMasks x, F mask) =
            linearSingletonRate n p * wittMutationLinearPotential p w x := by
        simpa [F] using
          (wittMutation_zeroSingleton_contribution_eq (p := p) w hw x)
      rw [hsingle]
      rfl

/-- The general-rate non-singleton certificate left for the C2/C3 analysis. -/
def HasWittMutationRemainderNonnegativity {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ x : BitString n, 0 ≤ wittMutationRemainderContribution p w x

/-- Nonnegative non-singleton remainder gives multiplicative drift at the exact
singleton mutation rate. -/
theorem linearSingletonRate_mul_wittMutationPotential_le_drift_of_remainder_nonnegative
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hrem : HasWittMutationRemainderNonnegativity p w)
    (x : BitString n) :
    linearSingletonRate n p * wittMutationLinearPotential p w x ≤
      driftAt (onePlusOneTransition p (linearFitness w))
        (wittMutationLinearPotential p w) x := by
  rw [wittMutationLinear_drift_eq_singleton_add_remainder w hw x]
  have hrest := hrem x
  linarith

/-- The same reduction packaged in the generic multiplicative-drift interface. -/
theorem wittMutation_hasMultiplicativeDriftLowerBound_of_remainder_nonnegative
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hrem : HasWittMutationRemainderNonnegativity p w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition p (linearFitness w))
      (wittMutationLinearPotential p w)
      (linearSingletonRate n p) := by
  intro x _hx
  exact linearSingletonRate_mul_wittMutationPotential_le_drift_of_remainder_nonnegative
    w hw hrem x

/-! ### Exact compatibility with the compiler-promoted Stage-31 remainder -/

/-- At standard mutation, the parameterized remainder contribution is exactly the
Stage-31 standard-potential remainder. -/
theorem wittMutationRemainderContribution_standardMutationRate_eq_wittStandard
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (x : BitString n) :
    wittMutationRemainderContribution (standardMutationRate n) w x =
      wittStandardRemainderContribution (standardMutationRate n) w x := by
  unfold wittMutationRemainderContribution wittStandardRemainderContribution
  rw [wittMutationRemainderMasks_eq_wittStandardRemainderMasks]
  apply Finset.sum_congr rfl
  intro mask hmask
  rw [wittMutationLinearPotential_standardMutationRate_eq_wittStandardLinearPotential
      hn w x,
    wittMutationLinearPotential_standardMutationRate_eq_wittStandardLinearPotential
      hn w (selectedAfterMask (linearFitness w) x mask)]

/-- At `p = 1/n`, the new remainder certificate is equivalent to the promoted Stage-31
certificate. -/
theorem hasWittMutationRemainderNonnegativity_standardMutationRate_iff
    {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ) :
    HasWittMutationRemainderNonnegativity (standardMutationRate n) w ↔
      HasWittStandardRemainderNonnegativity w := by
  constructor
  · intro h x
    rw [← wittMutationRemainderContribution_standardMutationRate_eq_wittStandard hn w x]
    exact h x
  · intro h x
    rw [wittMutationRemainderContribution_standardMutationRate_eq_wittStandard hn w x]
    exact h x

end ECRuntime
