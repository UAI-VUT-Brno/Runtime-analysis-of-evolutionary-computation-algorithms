import ECRuntime.StaticUnaryUnbiasedAcceptedEventBridge
import ECRuntime.LinearPotential
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Accepted leftmost-error events for static unary-unbiased linear functions

The 2024 static unary-unbiased upper-bound proof partitions accepted mutations according
to the leftmost flipped error bit.  The repository uses the opposite objective
convention from that paper: positive linear functions are maximized toward `allOnes`,
and coordinate `0` is the most important coordinate.  Consequently the corresponding
pivot event here is indexed by a currently-zero coordinate `i` that is flipped to one,
with no more-important currently-zero coordinate flipped in the same mutation.

This module deliberately formalizes only the event layer needed to instantiate the
promoted Stage-73 Bayes bridge.  It proves:

* every mask in the pivot event flips its pivot coordinate;
* a singleton zero-to-one flip belongs to its own pivot event;
* pivot events for distinct coordinates are disjoint; and
* the corrected conditional second-coordinate bound for the concrete pivot event is
  `E[K(K-1)] / (p₁ (n-1))`.

No mean-only replacement by `chi/(n-1)` is assumed.
-/

/--
Accepted mutation masks whose most-important flipped zero coordinate is `i`.

Since coordinate `0` is the most important coordinate in the repository convention,
`i.val <= j.val` says that no more-important zero-to-one flip than `i` occurs.
-/
noncomputable def acceptedLeftmostZeroEvent {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : Finset (MutationMask n) := by
  classical
  exact Finset.univ.filter (fun mask =>
    i ∈ zeroToOneFlips x mask ∧
      (∀ j ∈ zeroToOneFlips x mask, i.val ≤ j.val) ∧
        Accepts (linearFitness w) x (mutateWithMask x mask))

/-- Characterization of membership in the accepted leftmost-zero pivot event. -/
@[simp] theorem mem_acceptedLeftmostZeroEvent_iff {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mask ∈ acceptedLeftmostZeroEvent w x i ↔
      i ∈ zeroToOneFlips x mask ∧
        (∀ j ∈ zeroToOneFlips x mask, i.val ≤ j.val) ∧
          Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  simp [acceptedLeftmostZeroEvent]

/-- Membership in the accepted pivot event implies that the pivot coordinate flips. -/
theorem acceptedLeftmostZeroEvent_supports_pivot {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    i ∈ mask := by
  have hpred := (mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hmask
  have hflip : i ∈ zeroToOneFlips x mask := hpred.1
  exact ((mem_zeroToOneFlips x mask i).1 hflip).1

/-- Membership in the pivot event also records that the pivot is currently a zero bit. -/
theorem acceptedLeftmostZeroEvent_pivot_is_zero {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    x i = false := by
  have hpred := (mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hmask
  have hflip : i ∈ zeroToOneFlips x mask := hpred.1
  exact ((mem_zeroToOneFlips x mask i).1 hflip).2

/-- Every mask in the pivot event is accepted by elitist selection. -/
theorem acceptedLeftmostZeroEvent_accepts {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i) :
    Accepts (linearFitness w) x (mutateWithMask x mask) := by
  exact ((mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hmask).2.2

/-- The pivot is no less important than every other zero-to-one flip in the event. -/
theorem acceptedLeftmostZeroEvent_pivot_le {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n)
    (mask : MutationMask n)
    (hmask : mask ∈ acceptedLeftmostZeroEvent w x i)
    (j : Fin n) (hj : j ∈ zeroToOneFlips x mask) :
    i.val ≤ j.val := by
  exact ((mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hmask).2.1 j hj

/--
For positive linear weights, flipping exactly one currently-zero coordinate is accepted
and belongs to the pivot event indexed by that coordinate.
-/
theorem singleton_mem_acceptedLeftmostZeroEvent {n : ℕ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    ({i} : MutationMask n) ∈ acceptedLeftmostZeroEvent w x i := by
  have hflip : i ∈ zeroToOneFlips x ({i} : MutationMask n) :=
    (mem_zeroToOneFlips x ({i} : MutationMask n) i).2 ⟨by simp, hi⟩
  have hleft : ∀ j ∈ zeroToOneFlips x ({i} : MutationMask n), i.val ≤ j.val := by
    intro j hj
    have hjmask : j ∈ ({i} : MutationMask n) :=
      ((mem_zeroToOneFlips x ({i} : MutationMask n) j).1 hj).1
    have hji : j = i := by
      simpa using hjmask
    subst j
    exact le_rfl
  have hacc : Accepts (linearFitness w) x
      (mutateWithMask x ({i} : MutationMask n)) := by
    exact le_of_lt (linearFitness_single_zero_flip_improves w hw x i hi)
  exact (mem_acceptedLeftmostZeroEvent_iff w x i ({i} : MutationMask n)).2
    ⟨hflip, hleft, hacc⟩

/-- Distinct accepted pivot events are pairwise disjoint. -/
theorem acceptedLeftmostZeroEvent_disjoint {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n)
    (i j : Fin n) (hij : i ≠ j) :
    Disjoint (acceptedLeftmostZeroEvent w x i)
      (acceptedLeftmostZeroEvent w x j) := by
  rw [Finset.disjoint_left]
  intro mask hmi hmj
  have hpi := (mem_acceptedLeftmostZeroEvent_iff w x i mask).1 hmi
  have hpj := (mem_acceptedLeftmostZeroEvent_iff w x j mask).1 hmj
  have hleij : i.val ≤ j.val := hpi.2.1 j hpj.1
  have hleji : j.val ≤ i.val := hpj.2.1 i hpi.1
  apply hij
  exact Fin.ext (Nat.le_antisymm hleij hleji)

/--
Under `p₁ > 0`, every accepted pivot event for a currently-zero coordinate has positive
mass because it contains that coordinate's singleton mutation.
-/
theorem acceptedLeftmostZeroEvent_mass_pos {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (hp1 : 0 < law.oneBitMass)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i : Fin n) (hi : x i = false) :
    0 < law.maskEventMass (acceptedLeftmostZeroEvent w x i) := by
  have hsingleton : ({i} : MutationMask n) ∈ acceptedLeftmostZeroEvent w x i :=
    singleton_mem_acceptedLeftmostZeroEvent w hw x i hi
  have hweight : 0 < law.weight ({i} : MutationMask n) := by
    rw [law.singletonWeight_eq_oneBitMass_div hn i]
    exact div_pos hp1 (by exact_mod_cast hn)
  have hle : law.weight ({i} : MutationMask n) ≤
      law.maskEventMass (acceptedLeftmostZeroEvent w x i) :=
    law.singletonWeight_le_maskEventMass
      (acceptedLeftmostZeroEvent w x i) i hsingleton
  exact lt_of_lt_of_le hweight hle

/--
Concrete corrected conditional second-coordinate estimate for the accepted pivot event.

This is the direct Stage-73 instantiation corresponding to the Bayes step in the 2024
linear-function proof, but with the exact factorial-moment coefficient retained.
-/
theorem acceptedLeftmostZeroEvent_secondCoordinateSlice_bound {n : ℕ}
    (law : StaticUnaryUnbiasedMutation n) (hn : 2 ≤ n)
    (hp1 : 0 < law.oneBitMass)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) (i j : Fin n) (hi : x i = false) (hij : i ≠ j) :
    law.maskEventMass
        (secondCoordinateSlice (acceptedLeftmostZeroEvent w x i) j) /
        law.maskEventMass (acceptedLeftmostZeroEvent w x i) ≤
      law.secondFactorialRadiusMoment /
        (law.oneBitMass * ((n - 1 : ℕ) : ℝ)) := by
  exact law.secondCoordinateSlice_mass_div_eventMass_le_factorialCoefficient
    hn hp1 (acceptedLeftmostZeroEvent w x i) i j hij
    (fun mask hmask => acceptedLeftmostZeroEvent_supports_pivot w x i mask hmask)
    (singleton_mem_acceptedLeftmostZeroEvent w hw x i hi)

end StaticUnaryUnbiasedMutation
end ECRuntime
