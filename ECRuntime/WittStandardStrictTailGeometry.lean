import ECRuntime.WittStandardCaseC2A
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 34: strict-tail geometry and the remaining acceptance bridge

Stage 33 fix 1 localizes the only unresolved part of Witt's sharp standard-rate
one-step proof to accepted non-singleton `A_i` mutations whose worsening objective
coefficients are all strictly smaller than the unique improving coefficient `w i`.

This module deliberately separates two issues that are easy to conflate:

* the finite geometric cancellation behind Witt's conditional Subcase 2.2.2 estimate;
* the selected/accepted-mask comparison required to apply that cancellation to the
  actual `(1+1)`-EA contribution.

The geometric identity is proved exactly.  On the selected side we expose the strict
accepted mass and its worsening Witt-potential mass, prove the exact identity

`strict contribution = g_i * accepted mass - bad mass`,

and show that the Stage-33 certificate is equivalent to one explicit bad-mass bound.
The latter is the only remaining acceptance bridge; this stage does not assume or hide
it inside the geometric algebra.
-/

/-! ## The finite conditional geometric cancellation -/

/-- Elementary survival-series cancellation.  It is stated for an arbitrary real
`p`; later we instantiate `p = standardMutationRate n`.

The multiplication form avoids division by the probability of seeing at least one
worsening flip and therefore remains valid also for `k = 0`. -/
theorem mutationRate_mul_survivalGeometricSum (p : ℝ) (k : ℕ) :
    p * (∑ j : Fin k, (1 - p) ^ j.val) = 1 - (1 - p) ^ k := by
  have hgeom := witt_fin_sum_pow_mul_sub_one (1 - p) k
  calc
    p * (∑ j : Fin k, (1 - p) ^ j.val) =
        -((∑ j : Fin k, (1 - p) ^ j.val) * ((1 - p) - 1)) := by
      ring
    _ = -((1 - p) ^ k - 1) := by rw [hgeom]
    _ = 1 - (1 - p) ^ k := by ring

/-- The geometric envelope occurring in the conditional strict-tail estimate for a
fixed improving coordinate.  Its successive terms are

`g_i, g_i (1-p), ..., g_i (1-p)^(k-1)`.

At the standard mutation rate these are the exact reciprocal-base envelope terms used
in Witt's refined potential argument. -/
noncomputable def wittStandardStrictTailConditionalEnvelope {n : ℕ}
    (w : Fin n → ℝ) (i : Fin n) (k : ℕ) : ℝ :=
  wittStandardPotentialWeight w i *
    (∑ j : Fin k, (1 - standardMutationRate n) ^ j.val)

/-- Exact cancellation of the conditional geometric envelope at the standard mutation
rate.  This is the division-free form of

`p / (1-(1-p)^k) * envelope = g_i`.
-/
theorem standardMutationRate_mul_wittStandardStrictTailConditionalEnvelope
    {n : ℕ} (w : Fin n → ℝ) (i : Fin n) (k : ℕ) :
    standardMutationRate n *
        wittStandardStrictTailConditionalEnvelope w i k =
      wittStandardPotentialWeight w i *
        (1 - (1 - standardMutationRate n) ^ k) := by
  unfold wittStandardStrictTailConditionalEnvelope
  calc
    standardMutationRate n *
        (wittStandardPotentialWeight w i *
          (∑ j : Fin k, (1 - standardMutationRate n) ^ j.val)) =
      wittStandardPotentialWeight w i *
        (standardMutationRate n *
          (∑ j : Fin k, (1 - standardMutationRate n) ^ j.val)) := by
      ring
    _ = wittStandardPotentialWeight w i *
        (1 - (1 - standardMutationRate n) ^ k) := by
      rw [mutationRate_mul_survivalGeometricSum]

/-! ## The state-dependent strict tail -/

/-- Currently-correct coordinates whose objective coefficient is strictly smaller than
that of the fixed improving coordinate `i`.  These are precisely the coordinates that
can occur as worsening flips in a Stage-33 strict-tail mask. -/
noncomputable def wittStandardStrictTailIndices {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => x j = true ∧ w j < w i)

@[simp] theorem mem_wittStandardStrictTailIndices {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i j : Fin n) :
    j ∈ wittStandardStrictTailIndices w x i ↔
      x j = true ∧ w j < w i := by
  classical
  simp [wittStandardStrictTailIndices]

/-- Every worsening flip of a strict accepted `A_i` mask belongs to the fixed
state-dependent strict tail. -/
theorem oneToZeroFlips_subset_wittStandardStrictTailIndices {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hmask : mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i) :
    oneToZeroFlips x mask ⊆ wittStandardStrictTailIndices w x i := by
  intro j hj
  have hstrict := (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hmask
  have hjData := (mem_oneToZeroFlips x mask j).mp hj
  exact (mem_wittStandardStrictTailIndices w x i j).2
    ⟨hjData.2, hstrict.2 j hj⟩

/-- A strict non-singleton accepted `A_i` mask certifies that the state-dependent
strict tail is nonempty. -/
theorem wittStandardStrictTailIndices_nonempty_of_strictMask {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hmask : mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i) :
    (wittStandardStrictTailIndices w x i).Nonempty := by
  have hstrict := (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hmask
  have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
    w x i mask).mp hstrict.1
  have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
  have hbad := oneToZeroFlips_nonempty_of_caseC2At_of_ne_singleton
    x mask i hAdata.1.1 hbase.2
  rcases hbad with ⟨j, hj⟩
  exact ⟨j, oneToZeroFlips_subset_wittStandardStrictTailIndices
    w x i mask hmask hj⟩

/-! ## Accepted strict-tail mass accounting -/

/-- Probability mass of the accepted strict-tail non-singleton `A_i` masks. -/
noncomputable def wittStandardCaseC2AStrictAcceptedMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i,
    mutationMaskWeight p mask

/-- Expected worsening Witt-potential mass inside the accepted strict-tail `A_i`
class. -/
noncomputable def wittStandardCaseC2AStrictBadMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  ∑ mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i,
    mutationMaskWeight p mask *
      (∑ j ∈ oneToZeroFlips x mask, wittStandardPotentialWeight w j)

/-- Accepted strict-tail mass is nonnegative for a genuine mutation probability. -/
theorem wittStandardCaseC2AStrictAcceptedMass_nonneg {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    0 ≤ wittStandardCaseC2AStrictAcceptedMass p w x i := by
  unfold wittStandardCaseC2AStrictAcceptedMass
  apply Finset.sum_nonneg
  intro mask hmask
  exact mutationMaskWeight_nonneg hp0 hp1 mask

/-- Pointwise accepted strict-tail drop: one improving Witt coefficient minus the
worsening Witt coefficients. -/
theorem wittStandardLinearPotential_selected_drop_eq_good_sub_bad_of_strictC2A
    {n : ℕ} (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ wittStandardCaseC2AStrictAcceptedMasks w x i) :
    wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) =
      wittStandardPotentialWeight w i -
        (∑ j ∈ oneToZeroFlips x mask, wittStandardPotentialWeight w j) := by
  have hstrict := (mem_wittStandardCaseC2AStrictAcceptedMasks w x i mask).mp hmask
  have hbase := (mem_wittStandardCaseC2ANonSingletonAcceptedMasks_iff
    w x i mask).mp hstrict.1
  have hAdata := (mem_classicalLinearCaseC2AAcceptedMasks w x i mask).mp hbase.1
  rw [wittStandardLinearPotential_selected_drop_of_accepts
    w x mask hAdata.2, flipContribution_sum_eq_flip_sums, hAdata.1.1]
  simp

/-- Exact aggregate identity for the strict-tail contribution. -/
theorem wittStandardCaseC2AStrictContribution_eq_goodMass_sub_badMass
    {n : ℕ} (p : ℝ) (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    wittStandardCaseC2AStrictContribution p w x i =
      wittStandardPotentialWeight w i *
          wittStandardCaseC2AStrictAcceptedMass p w x i -
        wittStandardCaseC2AStrictBadMass p w x i := by
  unfold wittStandardCaseC2AStrictContribution
    wittStandardCaseC2AStrictAcceptedMass
    wittStandardCaseC2AStrictBadMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro mask hmask
  rw [wittStandardLinearPotential_selected_drop_eq_good_sub_bad_of_strictC2A
    w x i mask hmask]
  ring

/-! ## The explicit remaining acceptance bridge -/

/-- Selected strict-tail bad-mass bound.  This is the exact acceptance/conditioning
statement still needed after the geometric cancellation has been separated out. -/
def HasWittStandardStrictC2ABadMassBound {n : ℕ}
    (w : Fin n → ℝ) : Prop :=
  ∀ (x : BitString n) (i : Fin n), x i = false →
    wittStandardCaseC2AStrictBadMass
        (standardMutationRate n) w x i ≤
      wittStandardPotentialWeight w i *
        wittStandardCaseC2AStrictAcceptedMass
          (standardMutationRate n) w x i

/-- The Stage-33 contribution certificate is exactly the selected bad-mass bound. -/
theorem hasWittStandardStrictC2AContributionNonnegativity_iff_badMassBound
    {n : ℕ} (w : Fin n → ℝ) :
    HasWittStandardStrictC2AContributionNonnegativity w ↔
      HasWittStandardStrictC2ABadMassBound w := by
  constructor
  · intro h x i hi
    have hnonneg := h x i hi
    rw [wittStandardCaseC2AStrictContribution_eq_goodMass_sub_badMass] at hnonneg
    exact sub_nonneg.mp hnonneg
  · intro h x i hi
    rw [wittStandardCaseC2AStrictContribution_eq_goodMass_sub_badMass]
    exact sub_nonneg.mpr (h x i hi)

/-- A proof of the explicit selected bad-mass bridge therefore closes the sharp
`1/(e n)` multiplicative-drift interface through the promoted Stage-33 reduction. -/
theorem wittStandard_hasMultiplicativeDriftLowerBound_of_strictC2ABadMassBound
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (hbad : HasWittStandardStrictC2ABadMassBound w) :
    HasMultiplicativeDriftLowerBound
      (onePlusOneTransition (standardMutationRate n) (linearFitness w))
      (wittStandardLinearPotential w)
      (wittStandardLinearDriftRate n) := by
  apply wittStandard_hasMultiplicativeDriftLowerBound_of_strictC2A
    hn w hw hmono
  exact (hasWittStandardStrictC2AContributionNonnegativity_iff_badMassBound w).2 hbad

end ECRuntime
