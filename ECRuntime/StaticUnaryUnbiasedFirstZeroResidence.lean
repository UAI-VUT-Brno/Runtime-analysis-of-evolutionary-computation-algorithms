import ECRuntime.StaticUnaryUnbiasedLowestPivotTailCharge
import ECRuntime.LevelExitTail
import ECRuntime.LeadingOnesResidence
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

section ResidenceDecidability
attribute [local instance] Classical.propDecidable

/-!
# Stage 101 statement candidate: frozen-prefix geometric residence on BinVal

Coordinate zero is the most important coordinate in this formalization.
The first zero is the smallest numerical index at which the current parent
is not optimal. On a superincreasing linear objective, elitist selection
cannot undo the preceding all-one prefix. More strongly, the first zero is
corrected if and only if the original mutation mask belongs to its unique
minimum-pivot class. Hence its *one-step exit mass* is independent of the
less-important bits, even when those bits evolve while the process waits.

The nine statements below were approved by the user and now have proof
bodies awaiting strict focused compiler verification. They remain outside the
promoted root. The exact geometric residence statement is about the finite-level survival recursion already
connected to the genuine trajectory measure by LevelExitTrajectory. It is
not a proof of the full Doerr--Janett--Lengler runtime bound.
-/

/-- All coordinates strictly more important than `i` are already correct. -/
def firstZeroPrefixOnes {n : Nat} (x : BitString n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j.val < i.val -> x j = true

/-- The first remaining zero occurs at `i`. -/
def firstZeroAt {n : Nat} (x : BitString n) (i : Fin n) : Prop :=
  firstZeroPrefixOnes x i /\ x i = false

/-- Level consisting of exactly those strings whose first zero is `i`. -/
def firstZeroLevel {n : Nat} (i : Fin n) : Set (BitString n) :=
  {x | firstZeroAt x i}

/-!
The two auxiliary lemmas deliberately reason about the ORIGINAL mutation
mask.  An accepted move cannot flip an earlier correct coordinate: otherwise
the minimum flipped coordinate would be one of those earlier coordinates,
and Stage 99's superincreasing acceptance equivalence would reject it.
-/
private theorem accepted_mask_avoids_firstZero_prefix {n : Nat}
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask))
    (j : Fin n) (hj : j.val < i.val) : j ∉ mask := by
  classical
  intro hjmask
  have hne : mask.Nonempty := ⟨j, hjmask⟩
  let m : Fin n := mask.min' hne
  have hm : mask ∈ lowestMaskEvent m := by
    apply (mem_lowestMaskEvent_iff m mask).2
    constructor
    · exact Finset.min'_mem mask hne
    · intro t ht
      change m ≤ t
      exact Finset.min'_le mask t ht
  have hmle : m ≤ j := Finset.min'_le mask j hjmask
  have hmlt : m.val < i.val := lt_of_le_of_lt hmle hj
  have hzero : x m = false :=
    (superincreasing_accepts_iff_lowest_pivot_zero
      w hw x m mask hm).1 hacc
  have hone : x m = true := hx.1 m hmlt
  rw [hone] at hzero
  cases hzero

private theorem accepted_mask_flips_firstZero_is_lowest {n : Nat}
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask : MutationMask n)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask))
    (hi : i ∈ mask) : mask ∈ lowestMaskEvent i := by
  apply (mem_lowestMaskEvent_iff i mask).2
  constructor
  · exact hi
  · intro j hj
    by_contra hnot
    have hjlt : j.val < i.val := by omega
    exact (accepted_mask_avoids_firstZero_prefix
      w hw x i hx mask hacc j hjlt) hj

/-- Elitist selection on a superincreasing objective never destroys the
already-correct prefix preceding the first zero. -/
theorem firstZeroAt_selected_preserves_prefix {n : Nat}
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask : MutationMask n) :
    firstZeroPrefixOnes
      (selectedAfterMask (linearFitness w) x mask) i := by
  intro j hj
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · have hjnot : j ∉ mask :=
      accepted_mask_avoids_firstZero_prefix w hw x i hx mask hacc j hj
    change (elitistSelect (linearFitness w) x
      (mutateWithMask x mask)) j = true
    rw [elitistSelect_of_accepts _ _ _ hacc]
    simp [mutateWithMask, hjnot, hx.1 j hj]
  · change (elitistSelect (linearFitness w) x
      (mutateWithMask x mask)) j = true
    rw [elitistSelect_of_rejects _ _ _ hacc]
    exact hx.1 j hj

/-- While the first zero remains incorrect, the selected state remains
in the same first-zero level. Exit is exactly the minimum-pivot event,
including the empty mask and zero-radius operators. -/
theorem firstZeroAt_selected_stays_iff {n : Nat}
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask : MutationMask n) :
    firstZeroAt (selectedAfterMask (linearFitness w) x mask) i <->
      mask ∉ lowestMaskEvent i := by
  have hprefix := firstZeroAt_selected_preserves_prefix w hw x i hx mask
  change (firstZeroPrefixOnes
      (selectedAfterMask (linearFitness w) x mask) i ∧
    selectedAfterMask (linearFitness w) x mask i = false) ↔
    mask ∉ lowestMaskEvent i
  constructor
  · intro hstay hm
    have hi : i ∈ mask := lowestMaskEvent_supports_pivot i mask hm
    have hacc : Accepts (linearFitness w) x (mutateWithMask x mask) :=
      (superincreasing_accepts_iff_lowest_pivot_zero
        w hw x i mask hm).2 hx.2
    have htrue : selectedAfterMask (linearFitness w) x mask i = true := by
      change (elitistSelect (linearFitness w) x
        (mutateWithMask x mask)) i = true
      rw [elitistSelect_of_accepts _ _ _ hacc]
      simp [mutateWithMask, hi, hx.2]
    have hfalse := hstay.2
    rw [htrue] at hfalse
    cases hfalse
  · intro hm
    refine ⟨hprefix, ?_⟩
    by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
    · have hinot : i ∉ mask := by
        intro hi
        exact hm (accepted_mask_flips_firstZero_is_lowest
          w hw x i hx mask hacc hi)
      change (elitistSelect (linearFitness w) x
        (mutateWithMask x mask)) i = false
      rw [elitistSelect_of_accepts _ _ _ hacc]
      simp [mutateWithMask, hinot, hx.2]
    · change (elitistSelect (linearFitness w) x
        (mutateWithMask x mask)) i = false
      rw [elitistSelect_of_rejects _ _ _ hacc]
      exact hx.2

/-- The exact, unconditioned event that exits the first-zero level. -/
theorem firstZeroAt_selected_exits_iff {n : Nat}
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (mask : MutationMask n) :
    (selectedAfterMask (linearFitness w) x mask) ∉ firstZeroLevel i <->
      mask ∈ lowestMaskEvent i := by
  change (¬ firstZeroAt
    (selectedAfterMask (linearFitness w) x mask) i) ↔
    mask ∈ lowestMaskEvent i
  constructor
  · intro hnot
    by_contra hm
    exact hnot ((firstZeroAt_selected_stays_iff w hw x i hx mask).2 hm)
  · intro hm hlevel
    exact ((firstZeroAt_selected_stays_iff w hw x i hx mask).1 hlevel) hm

/-- Under the original mask law, the first-zero exit probability equals
its minimum-pivot mass, not a conditionally size-biased radius law. -/
theorem firstZeroAt_mask_exit_mass_eq {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i) :
    finiteEventMass law.weight
        (fun mask : MutationMask n =>
          selectedAfterMask (linearFitness w) x mask ∉ firstZeroLevel i) =
      law.maskEventMass (lowestMaskEvent i) := by
  classical
  calc
    finiteEventMass law.weight
        (fun mask : MutationMask n =>
          selectedAfterMask (linearFitness w) x mask ∉ firstZeroLevel i) =
        ∑ mask ∈ lowestMaskEvent i, law.weight mask := by
          apply finiteEventMass_eq_sum_finset_of_iff
          intro mask
          exact firstZeroAt_selected_exits_iff w hw x i hx mask
    _ = law.maskEventMass (lowestMaskEvent i) := rfl

/-- The complementary one-step survival probability, including laws
with an atom at the empty mask. -/
theorem firstZeroAt_mask_stay_mass_eq {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i) :
    finiteEventMass law.weight
        (fun mask : MutationMask n =>
          selectedAfterMask (linearFitness w) x mask ∈ firstZeroLevel i) =
      1 - law.maskEventMass (lowestMaskEvent i) := by
  have hpart := finiteEventMass_add_compl law.weight
    (fun mask : MutationMask n =>
      selectedAfterMask (linearFitness w) x mask ∈ firstZeroLevel i)
  have hexit := firstZeroAt_mask_exit_mass_eq law w hw x i hx
  rw [hexit, law.weight_sum] at hpart
  linarith

/-- At least the singleton mutation of the first zero contributes to
its exit mass. This certificate needs no second moment and is uniform
in the less-important coordinates. -/
theorem lowestMaskEvent_mass_ge_oneBit_per_coordinate {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (i : Fin n) :
    law.oneBitMass / (n : Real) <=
      law.maskEventMass (lowestMaskEvent i) := by
  have hn : 0 < n := by
    have hni := i.isLt
    omega
  have hsingle : ({i} : MutationMask n) ∈ lowestMaskEvent i := by
    apply (mem_lowestMaskEvent_iff i ({i} : MutationMask n)).2
    constructor
    · simp
    · intro j hj
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      exact le_refl _
  calc
    law.oneBitMass / (n : Real) = law.weight ({i} : MutationMask n) :=
      (law.singletonWeight_eq_oneBitMass_div hn i).symm
    _ ≤ law.maskEventMass (lowestMaskEvent i) :=
      law.singletonWeight_le_maskEventMass (lowestMaskEvent i) i hsingle

/-- The event identity is transported from the finite mask space to the
actual stochastic transition on bitstrings. -/
theorem firstZeroAt_transition_exit_mass_eq {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i) :
    finiteEventMass ((law.transition (linearFitness w)) x)
        (fun y : BitString n => y ∉ firstZeroLevel i) =
      law.maskEventMass (lowestMaskEvent i) := by
  classical
  change finiteEventMass
    (pushforwardWeight law.weight (selectedAfterMask (linearFitness w) x))
    (fun y : BitString n => y ∉ firstZeroLevel i) =
      law.maskEventMass (lowestMaskEvent i)
  rw [finiteEventMass_pushforwardWeight]
  exact firstZeroAt_mask_exit_mass_eq law w hw x i hx

/-- Exact geometric residence: for every horizon, survival at the same
first-zero level is geometric, even though the lower-priority suffix can
change between iterations. This is a finite-trajectory statement, not a
claim of globally positive one-step potential drift. -/
theorem firstZeroAt_finiteLevelSurvival_eq_pow {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (k : Nat) :
    finiteLevelSurvival (law.transition (linearFitness w))
        (firstZeroLevel i) k x =
      (1 - law.maskEventMass (lowestMaskEvent i)) ^ k := by
  classical
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  have hexit : ∀ z : BitString n, z ∈ firstZeroLevel i →
      finiteEventMass ((law.transition (linearFitness w)) z)
        (fun y : BitString n => y ∉ firstZeroLevel i) =
        law.maskEventMass (lowestMaskEvent i) := by
    intro z hz
    exact firstZeroAt_transition_exit_mass_eq law w hw z i hz
  exact finiteLevelSurvival_eq_geometric_of_exact_exit_mass
    (law.transition (linearFitness w)) (firstZeroLevel i)
    hP (law.maskEventMass (lowestMaskEvent i)) hexit k x hx

/-- Geometric residence is uniformly dominated by singleton progress.
This bound is a legitimate level-exit ingredient, but summing it over
all first-zero levels gives only a coarse quadratic runtime bound; the
sharp n log n theorem needs additional suffix occupation/repair control. -/
theorem firstZeroAt_finiteLevelSurvival_le_singleton_bound {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (hx : firstZeroAt x i)
    (k : Nat) :
    finiteLevelSurvival (law.transition (linearFitness w))
        (firstZeroLevel i) k x <=
      (1 - law.oneBitMass / (n : Real)) ^ k := by
  rw [firstZeroAt_finiteLevelSurvival_eq_pow law w hw x i hx k]
  have hp : law.oneBitMass / (n : Real) ≤
      law.maskEventMass (lowestMaskEvent i) :=
    law.lowestMaskEvent_mass_ge_oneBit_per_coordinate i
  have hmass : law.maskEventMass (lowestMaskEvent i) ≤ 1 := by
    calc
      law.maskEventMass (lowestMaskEvent i) ≤
          ∑ mask : MutationMask n, law.weight mask := by
            unfold maskEventMass
            apply Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.subset_univ (lowestMaskEvent i))
            intro mask _ _
            exact law.weight_nonneg mask
      _ = 1 := law.weight_sum
  have hnonneg : 0 ≤ 1 - law.maskEventMass (lowestMaskEvent i) := by
    linarith
  exact pow_le_pow_left₀ hnonneg (by linarith) k

end ResidenceDecidability
end StaticUnaryUnbiasedMutation
end ECRuntime
