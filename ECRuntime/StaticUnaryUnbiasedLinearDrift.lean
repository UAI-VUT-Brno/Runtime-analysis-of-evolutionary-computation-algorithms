import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.LinearPotential
import ECRuntime.Drift
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Linear-function singleton drift for static unary-unbiased mutation

This module is the first objective-specific layer above `StaticUnaryUnbiasedMutation`.
It isolates the part of the linear-function drift argument that depends only on the
one-bit mass `p₁`, without making any independent-bit assumption.

For a static unary-unbiased mutation law, every specified singleton mask has weight
`p₁ / n`.  Consequently, all accepted singleton zero-to-one mutations contribute
exactly `(p₁ / n) * V(x)` to any linear-error potential `V` whose coefficients are
summed over zero positions.  The remaining difficulty for coefficient-independent
linear-function bounds is therefore localized in a named non-singleton remainder.
-/

/-- Per-coordinate mass of a specified one-bit mutation, i.e. `p₁ / n`. -/
noncomputable def singletonCoordinateRate {n : ℕ} (law : StaticUnaryUnbiasedMutation n) : ℝ :=
  law.oneBitMass / (n : ℝ)

/-- The per-coordinate singleton rate is nonnegative. -/
theorem singletonCoordinateRate_nonneg {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) :
    0 ≤ law.singletonCoordinateRate := by
  exact div_nonneg law.oneBitMass_nonneg (Nat.cast_nonneg n)

/-- Positive one-bit mass gives a positive per-coordinate singleton rate in positive dimension. -/
theorem singletonCoordinateRate_pos {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) (hp1 : 0 < law.oneBitMass) :
    0 < law.singletonCoordinateRate := by
  unfold singletonCoordinateRate
  exact div_pos hp1 (by exact_mod_cast hn)

/--
One-step drift under a static unary-unbiased law can be computed directly as an
expectation over mutation masks.
-/
theorem drift_eq_mask_sum {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (fitness V : BitString n → ℝ) (x : BitString n) :
    driftAt (law.transition fitness) V x =
      ∑ mask : MutationMask n,
        law.weight mask * (V x - V (selectedAfterMask fitness x mask)) := by
  have hEV :
      expectedValueAfter (law.transition fitness) V x =
        ∑ mask : MutationMask n,
          law.weight mask * V (selectedAfterMask fitness x mask) := by
    unfold expectedValueAfter transition finiteRandomTransition
    exact pushforwardWeight_expectation
      (w := law.weight) (f := selectedAfterMask fitness x) V
  unfold driftAt
  rw [hEV]
  calc
    V x - ∑ mask : MutationMask n,
        law.weight mask * V (selectedAfterMask fitness x mask) =
      (∑ mask : MutationMask n, law.weight mask) * V x -
        ∑ mask : MutationMask n,
          law.weight mask * V (selectedAfterMask fitness x mask) := by
            rw [law.weight_sum, one_mul]
    _ = ∑ mask : MutationMask n,
        law.weight mask * (V x - V (selectedAfterMask fitness x mask)) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro mask hmask
      ring

/--
A singleton zero-to-one mutation is accepted for a positive linear objective and drops
an arbitrary linear-error potential by exactly the coefficient of the improved bit.
-/
theorem selected_single_zero_flip_linearError_drop {n : ℕ}
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    linearErrorPotential g x -
        linearErrorPotential g
          (selectedAfterMask (linearFitness w) x ({i} : MutationMask n)) =
      g i := by
  have himprove := linearFitness_single_zero_flip_improves w hw x i hi
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask n)) := by
    exact le_of_lt himprove
  rw [linearErrorPotential_selected_drop_of_accepts
    w g x ({i} : MutationMask n) hacc]
  simp [flipContribution, hi]

/--
The zero-singleton branch contributes exactly `(p₁ / n) * V(x)` for every linear-error
potential.  No independence assumption on coordinates is used.
-/
theorem zeroSingleton_linearError_contribution_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ zeroSingletonMasks x,
      law.weight mask *
        (linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask))) =
      law.singletonCoordinateRate * linearErrorPotential g x := by
  let F : MutationMask n → ℝ := fun mask =>
    law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask))
  have hcoord :
      ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) =
        law.singletonCoordinateRate * linearErrorPotential g x := by
    rw [linearErrorPotential_eq_sum_zeroPositions, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hzero : x i = false := (mem_zeroPositions x i).mp hi
    dsimp [F]
    rw [law.singletonWeight_eq_oneBitMass_div hn i,
      selected_single_zero_flip_linearError_drop w g hw x i hzero]
    rfl
  calc
    (∑ mask ∈ zeroSingletonMasks x,
      law.weight mask *
        (linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask))) =
        ∑ mask ∈ zeroSingletonMasks x, F mask := by rfl
    _ = ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) := by
      unfold zeroSingletonMasks
      rw [Finset.sum_image]
      intro a ha b hb hab
      exact Finset.singleton_injective hab
    _ = law.singletonCoordinateRate * linearErrorPotential g x := hcoord

/-- The singleton contribution specialized to the bounded rank potential. -/
theorem rankLinear_zeroSingleton_contribution_eq {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    (∑ mask ∈ zeroSingletonMasks x,
      law.weight mask *
        (rankLinearPotential x -
          rankLinearPotential (selectedAfterMask (linearFitness w) x mask))) =
      law.singletonCoordinateRate * rankLinearPotential x := by
  simpa [rankLinearPotential] using
    (law.zeroSingleton_linearError_contribution_eq
      hn w (rankPotentialWeight n) hw x)

/-- Mutation masks outside the already-accounted-for zero-singleton events. -/
def rankLinearRemainderMasks {n : ℕ} (x : BitString n) : Finset (MutationMask n) :=
  Finset.univ \ zeroSingletonMasks x

/-- Aggregate non-zero-singleton contribution to rank-potential drift. -/
noncomputable def rankLinearRemainderContribution {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ rankLinearRemainderMasks x,
    law.weight mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))

/--
Exact rank-drift decomposition into the `p₁/n` singleton term and one non-singleton
remainder.  Future unary-unbiased linear-function work only needs to control this
remainder; the positive singleton term is completely operator-generic.
-/
theorem rankLinear_drift_eq_singleton_add_remainder {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    driftAt (law.transition (linearFitness w))
        (rankLinearPotential (n := n)) x =
      law.singletonCoordinateRate * rankLinearPotential x +
        law.rankLinearRemainderContribution w x := by
  rw [law.drift_eq_mask_sum]
  let F : MutationMask n → ℝ := fun mask =>
    law.weight mask *
      (rankLinearPotential x -
        rankLinearPotential (selectedAfterMask (linearFitness w) x mask))
  change (∑ mask : MutationMask n, F mask) =
    law.singletonCoordinateRate * rankLinearPotential x +
      law.rankLinearRemainderContribution w x
  have hsubset : zeroSingletonMasks x ⊆
      (Finset.univ : Finset (MutationMask n)) := Finset.subset_univ _
  have hsplit := Finset.sum_sdiff (f := F) hsubset
  have hsum :
      (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ rankLinearRemainderMasks x, F mask) := by
    change (∑ mask : MutationMask n, F mask) =
      (∑ mask ∈ zeroSingletonMasks x, F mask) +
        (∑ mask ∈ ((Finset.univ : Finset (MutationMask n)) \ zeroSingletonMasks x),
          F mask)
    simpa only [add_comm] using hsplit.symm
  calc
    (∑ mask : MutationMask n, F mask) =
        (∑ mask ∈ zeroSingletonMasks x, F mask) +
          (∑ mask ∈ rankLinearRemainderMasks x, F mask) := hsum
    _ = law.singletonCoordinateRate * rankLinearPotential x +
        law.rankLinearRemainderContribution w x := by
      have hsingle :
          (∑ mask ∈ zeroSingletonMasks x, F mask) =
            law.singletonCoordinateRate * rankLinearPotential x := by
        simpa [F] using
          (law.rankLinear_zeroSingleton_contribution_eq hn w hw x)
      rw [hsingle]
      rfl

/--
As a coefficient-sensitive baseline, objective error itself has multiplicative drift
`p₁/n` under every static unary-unbiased mutation law.  This uses only that elitist
selection makes objective-error drop nonnegative on every other mask.
-/
theorem linearObjectiveError_hasMultiplicativeDriftLowerBound {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) :
    HasMultiplicativeDriftLowerBound
      (law.transition (linearFitness w))
      (linearErrorPotential w)
      law.singletonCoordinateRate := by
  intro x _hx
  rw [law.drift_eq_mask_sum]
  let F : MutationMask n → ℝ := fun mask =>
    law.weight mask *
      (linearErrorPotential w x -
        linearErrorPotential w (selectedAfterMask (linearFitness w) x mask))
  have hsingle :
      (∑ mask ∈ zeroSingletonMasks x, F mask) =
        law.singletonCoordinateRate * linearErrorPotential w x := by
    simpa [F] using
      (law.zeroSingleton_linearError_contribution_eq hn w w hw x)
  calc
    law.singletonCoordinateRate * linearErrorPotential w x =
        ∑ mask ∈ zeroSingletonMasks x, F mask := hsingle.symm
    _ ≤ ∑ mask : MutationMask n, F mask := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro mask hmask hnotmem
        dsimp [F]
        exact mul_nonneg
          (law.weight_nonneg mask)
          (linearErrorPotential_selected_drop_nonneg w x mask)

end StaticUnaryUnbiasedMutation
end ECRuntime
