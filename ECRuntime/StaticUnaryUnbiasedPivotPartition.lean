import ECRuntime.StaticUnaryUnbiasedPivotDrift
import ECRuntime.StaticUnaryUnbiasedLinearAcceptedEvents
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Exhaustive accepted-pivot partition for positive linear objectives

Stage 81 controls the unnormalized drift restricted to one accepted leftmost-zero
pivot event. To pass to unrestricted drift, one must first account for every
mutation mask, rather than discard accepted masks of potentially negative
corrected-potential drop.

This stage separates the argument into three theorem targets:

* an accepted mask with a zero-to-one flip belongs to exactly one pivot event;
* a mask with no zero-to-one flip has zero selected drop for **any** error
  coefficient vector when the objective weights are strictly positive;
* the unrestricted mask-weighted drop is the exact sum of its pivot-event
  contributions, including every signed summand.

No independence of mutation bits or pointwise nonnegativity of a corrected
potential drop is assumed. The result is a finite accounting identity, not yet
a global multiplicative-drift lower bound.
-/

/-- An accepted mask with an improving flip has exactly one most-important
flipped-zero pivot. The construction uses the minimum element of the finite
set of zero-to-one flips, and does not depend on positive objective weights. -/
theorem acceptedLeftmostZeroEvent_existsUnique_of_accepts {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask))
    (hflip : (zeroToOneFlips x mask).Nonempty) :
    ∃! i : Fin n, mask ∈ acceptedLeftmostZeroEvent w x i := by
  classical
  let i : Fin n := (zeroToOneFlips x mask).min' hflip
  have hi : i ∈ zeroToOneFlips x mask :=
    Finset.min'_mem (zeroToOneFlips x mask) hflip
  have hleast : ∀ j ∈ zeroToOneFlips x mask, i.val ≤ j.val := by
    intro j hj
    change i ≤ j
    exact Finset.min'_le (zeroToOneFlips x mask) j hj
  have hmember : mask ∈ acceptedLeftmostZeroEvent w x i :=
    (mem_acceptedLeftmostZeroEvent_iff w x i mask).2
      ⟨hi, hleast, hacc⟩
  refine ⟨i, hmember, ?_⟩
  intro j hj
  have hjdata := (mem_acceptedLeftmostZeroEvent_iff w x j mask).1 hj
  have hji : j.val ≤ i.val := hjdata.2.1 i hi
  have hij : i.val ≤ j.val := hleast j hjdata.1
  exact Fin.ext (Nat.le_antisymm hji hij)

/-- If no zero bit flips, elitist selection changes no error potential for a
positive linear objective. This holds for arbitrary (even signed) coefficients
`g`: acceptance forces every one-to-zero flip to be absent, whereas rejection
keeps the parent. -/
theorem linearErrorPotential_selected_drop_eq_zero_of_noZeroToOneFlips
    {n : ℕ} (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (mask : MutationMask n)
    (hzero : zeroToOneFlips x mask = ∅) :
    linearErrorPotential g x -
      linearErrorPotential g (selectedAfterMask (linearFitness w) x mask) = 0 := by
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · have hbalance :=
      (accepts_linearFitness_iff_flip_sums w x mask).1 hacc
    rw [hzero] at hbalance
    simp only [Finset.sum_empty] at hbalance
    have hnonneg : 0 ≤ ∑ j ∈ oneToZeroFlips x mask, w j := by
      apply Finset.sum_nonneg
      intro j hj
      exact (hw j).le
    have hsumzero : (∑ j ∈ oneToZeroFlips x mask, w j) = 0 :=
      le_antisymm hbalance hnonneg
    have honeempty : oneToZeroFlips x mask = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hle : w j ≤ ∑ k ∈ oneToZeroFlips x mask, w k :=
        Finset.single_le_sum (fun k hk => (hw k).le) hj
      rw [hsumzero] at hle
      exact (not_le_of_gt (hw j)) hle
    rw [linearErrorPotential_selected_drop_of_accepts w g x mask hacc,
      flipContribution_sum_eq_flip_sums, hzero, honeempty]
    simp
  · exact linearErrorPotential_selected_drop_of_rejects w g x mask hacc

-- The proposition-valued `if` in the next theorem is elaborated *before*
-- its proof begins. A proof-local `classical` cannot supply its Decidable
-- instance, so register classical decidability only for this statement.
section PivotIndicatorDecidability
attribute [local instance] Classical.propDecidable

/-- A finite combinatorial indicator identity: exactly one accepted pivot
contributes if and only if the mask is accepted and has an improving flip.
This contains no probabilistic assumptions or sign conditions. -/
theorem sum_zeroPositions_acceptedLeftmostZeroEvent_indicator {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n) (a : ℝ) :
    (∑ i ∈ zeroPositions x,
        if mask ∈ acceptedLeftmostZeroEvent w x i then a else 0) =
      if Accepts (linearFitness w) x (mutateWithMask x mask) ∧
          (zeroToOneFlips x mask).Nonempty then a else 0 := by
  classical
  by_cases hcase : Accepts (linearFitness w) x (mutateWithMask x mask) ∧
      (zeroToOneFlips x mask).Nonempty
  · obtain ⟨i, hi, hunique⟩ :=
      acceptedLeftmostZeroEvent_existsUnique_of_accepts w x mask
        hcase.1 hcase.2
    have hzero : i ∈ zeroPositions x := by
      apply (mem_zeroPositions x i).2
      exact ((mem_zeroToOneFlips x mask i).1
        ((mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hi).1).2
    have hsingle :
        (∑ j ∈ zeroPositions x,
          if mask ∈ acceptedLeftmostZeroEvent w x j then a else 0) =
          (if mask ∈ acceptedLeftmostZeroEvent w x i then a else 0) := by
      apply Finset.sum_eq_single i
      · intro j hj hji
        have hjnot : mask ∉ acceptedLeftmostZeroEvent w x j := by
          intro hjmem
          exact hji (hunique j hjmem)
        simp [hjnot]
      · intro hni
        exact False.elim (hni hzero)
    rw [hsingle]
    simp [hi, hcase]
  · have hnone : ∀ i ∈ zeroPositions x,
        mask ∉ acceptedLeftmostZeroEvent w x i := by
      intro i hi hm
      have hdata := (mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hm
      exact hcase ⟨hdata.2.2, ⟨i, hdata.1⟩⟩
    have hsumzero :
        (∑ i ∈ zeroPositions x,
          if mask ∈ acceptedLeftmostZeroEvent w x i then a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hnone i hi]
    simpa [hcase] using hsumzero

end PivotIndicatorDecidability

/-- The unnormalized global selected-potential drop is the exact sum over
accepted leftmost-zero pivot events. No negative accepted contribution is
omitted: masks outside this union have **zero** selected drop, and each mask
inside the union is counted exactly once. -/
theorem acceptedEventWeightedPotentialDrop_univ_eq_sum_pivots {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n)
    (w g : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) :
    law.acceptedEventWeightedPotentialDrop Finset.univ w g x =
      ∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (acceptedLeftmostZeroEvent w x i) w g x := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g
          (selectedAfterMask (linearFitness w) x mask))
  have hpoint (mask : MutationMask n) :
      F mask = ∑ i ∈ zeroPositions x,
        if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0 := by
    have hindicator :=
      sum_zeroPositions_acceptedLeftmostZeroEvent_indicator
        w x mask (F mask)
    rw [hindicator]
    by_cases hcase : Accepts (linearFitness w) x (mutateWithMask x mask) ∧
        (zeroToOneFlips x mask).Nonempty
    · simp [hcase]
    · have hdrop : linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask) = 0 := by
        by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
        · have hno : ¬ (zeroToOneFlips x mask).Nonempty := by
            intro hn
            exact hcase ⟨hacc, hn⟩
          have hempty : zeroToOneFlips x mask = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro j hj
            exact hno ⟨j, hj⟩
          exact linearErrorPotential_selected_drop_eq_zero_of_noZeroToOneFlips
            w g hw x mask hempty
        · exact linearErrorPotential_selected_drop_of_rejects w g x mask hacc
      have hFzero : F mask = 0 := by
        dsimp [F]
        rw [hdrop, mul_zero]
      rw [hFzero]
      simp
  have hfilter (i : Fin n) :
      (∑ mask : MutationMask n,
        if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0) =
        ∑ mask ∈ acceptedLeftmostZeroEvent w x i, F mask := by
    calc
      (∑ mask : MutationMask n,
        if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0) =
          ∑ mask ∈ (Finset.univ.filter (fun mask : MutationMask n =>
            mask ∈ acceptedLeftmostZeroEvent w x i)), F mask := by
          rw [Finset.sum_filter]
      _ = ∑ mask ∈ acceptedLeftmostZeroEvent w x i, F mask := by
        congr 1
        ext mask
        simp
  unfold acceptedEventWeightedPotentialDrop
  change (∑ mask : MutationMask n, F mask) =
    ∑ i ∈ zeroPositions x,
      ∑ mask ∈ acceptedLeftmostZeroEvent w x i, F mask
  calc
    (∑ mask : MutationMask n, F mask) =
        ∑ mask : MutationMask n,
          ∑ i ∈ zeroPositions x,
            if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0 := by
      apply Finset.sum_congr rfl
      intro mask hm
      exact hpoint mask
    _ = ∑ i ∈ zeroPositions x,
        ∑ mask : MutationMask n,
          if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ zeroPositions x,
        ∑ mask ∈ acceptedLeftmostZeroEvent w x i, F mask := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hfilter i

end StaticUnaryUnbiasedMutation
end ECRuntime
