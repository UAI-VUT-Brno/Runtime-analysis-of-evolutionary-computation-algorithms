import ECRuntime.StaticUnaryUnbiasedTailCoordinateMoment
import ECRuntime.StaticUnaryUnbiasedPivotPartition
import ECRuntime.StaticUnaryUnbiasedLinearDrift
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Stage 93: accepted short-radius pivot accounting

The Stage-92 tail-moment estimate is valid without a second moment, but its
positive-drift corollary assumes that *all* short-radius signed contributions
dominate the singleton gain.  This module replaces that opaque premise by a
finite, acceptance-aware decomposition into the singleton gain at each pivot
and a signed, non-singleton remainder.  A new unconditional lower envelope
charges only flipped-one loss in the actual accepted short-pivot remainders.

No accepted short-radius remainder is discarded or declared nonnegative. The
resulting finite-event budget can be refined in later stages; it is not a
proof of the full bounded-first-moment sharp runtime upper bound.
-/

/-- Intersect an arbitrary mask event with one accepted leftmost-zero pivot. -/
noncomputable def restrictedAcceptedPivotEvent {n : Nat}
    (event : Finset (MutationMask n)) (w : Fin n -> Real)
    (x : BitString n) (i : Fin n) : Finset (MutationMask n) := by
  classical
  exact event.filter (fun mask => mask ∈ acceptedLeftmostZeroEvent w x i)

/-- The accepted pivot event with radius strictly below the cutoff. -/
noncomputable def shortAcceptedPivotEvent {n : Nat}
    (w : Fin n -> Real) (x : BitString n) (b : Nat) (i : Fin n) :
    Finset (MutationMask n) :=
  restrictedAcceptedPivotEvent (shortRadiusMaskEvent (n := n) b) w x i

/-- The accepted short-pivot masks except for the improving singleton. -/
noncomputable def shortPivotRemainderEvent {n : Nat}
    (w : Fin n -> Real) (x : BitString n) (b : Nat) (i : Fin n) :
    Finset (MutationMask n) :=
  (shortAcceptedPivotEvent w x b i).erase ({i} : MutationMask n)

/-- Membership in a restricted accepted pivot automatically implies acceptance. -/
theorem restrictedAcceptedPivotEvent_accepts {n : Nat}
    (event : Finset (MutationMask n)) (w : Fin n -> Real)
    (x : BitString n) (i : Fin n) (mask : MutationMask n)
    (hm : mask ∈ restrictedAcceptedPivotEvent event w x i) :
    Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  change mask ∈ event.filter
    (fun m => m ∈ acceptedLeftmostZeroEvent w x i) at hm
  have hmem : mask ∈ acceptedLeftmostZeroEvent w x i := by
    exact (Finset.mem_filter.mp hm).2
  exact acceptedLeftmostZeroEvent_accepts w x i mask hmem

/-- The Stage-82 pivot partition is valid on *any* restricted event, not only
on the whole mask space.  The summands remain signed and unnormalized. -/
theorem acceptedEventWeightedPotentialDrop_event_eq_sum_pivot_slices
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n)) (w g : Fin n -> Real)
    (hw : PositiveLinearWeights w) (x : BitString n) :
    law.acceptedEventWeightedPotentialDrop event w g x =
      ∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (restrictedAcceptedPivotEvent event w x i) w g x := by
  classical
  let F : MutationMask n -> Real := fun mask =>
    law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask))
  have hpoint (mask : MutationMask n) :
      F mask = ∑ i ∈ zeroPositions x,
        if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0 := by
    have hindicator :=
      sum_zeroPositions_acceptedLeftmostZeroEvent_indicator w x mask (F mask)
    rw [hindicator]
    by_cases hcase : Accepts (linearFitness w) x (mutateWithMask x mask) ∧
        (zeroToOneFlips x mask).Nonempty
    case pos => simp [hcase]
    case neg =>
      have hdrop : linearErrorPotential g x -
          linearErrorPotential g
            (selectedAfterMask (linearFitness w) x mask) = 0 := by
        by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
        case pos =>
          have hno : Not (zeroToOneFlips x mask).Nonempty := by
            intro hn
            exact hcase ⟨hacc, hn⟩
          have hempty : zeroToOneFlips x mask = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro j hj
            exact hno ⟨j, hj⟩
          exact linearErrorPotential_selected_drop_eq_zero_of_noZeroToOneFlips
            w g hw x mask hempty
        case neg =>
          exact linearErrorPotential_selected_drop_of_rejects w g x mask hacc
      have hfzero : F mask = 0 := by
        dsimp [F]
        rw [hdrop, mul_zero]
      rw [hfzero]
      simp
  unfold acceptedEventWeightedPotentialDrop
  change (∑ mask ∈ event, F mask) =
    ∑ i ∈ zeroPositions x,
      ∑ mask ∈ restrictedAcceptedPivotEvent event w x i, F mask
  calc
    (∑ mask ∈ event, F mask) =
        ∑ mask ∈ event,
          ∑ i ∈ zeroPositions x,
            if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0 := by
      apply Finset.sum_congr rfl
      intro mask hm
      exact hpoint mask
    _ = ∑ i ∈ zeroPositions x,
          ∑ mask ∈ event,
            if mask ∈ acceptedLeftmostZeroEvent w x i then F mask else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ zeroPositions x,
          ∑ mask ∈ restrictedAcceptedPivotEvent event w x i, F mask := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold restrictedAcceptedPivotEvent
      rw [Finset.sum_filter]

/-- The signed short-radius drift is exactly the sum of its accepted pivot
slices.  Positive weights ensure that selected changes with no improving
zero-to-one bit contribute zero. -/
theorem acceptedEventWeightedPotentialDrop_short_eq_sum_pivots {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w g : Fin n -> Real)
    (hw : PositiveLinearWeights w) (x : BitString n) (b : Nat) :
    law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x =
      ∑ i ∈ zeroPositions x,
        law.acceptedEventWeightedPotentialDrop
          (shortAcceptedPivotEvent w x b i) w g x := by
  exact law.acceptedEventWeightedPotentialDrop_event_eq_sum_pivot_slices
    (shortRadiusMaskEvent (n := n) b) w g hw x

/-- For `b >= 2`, a one-bit improvement is present in its short pivot event. -/
theorem singleton_mem_shortAcceptedPivotEvent {n : Nat}
    (w : Fin n -> Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : Nat) (hb : 2 ≤ b)
    (i : Fin n) (hi : x i = false) :
    ({i} : MutationMask n) ∈ shortAcceptedPivotEvent w x b i := by
  classical
  have hcard : ({i} : MutationMask n).card < b := by
    simp
    omega
  have hshort : ({i} : MutationMask n) ∈
      shortRadiusMaskEvent (n := n) b := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩
  unfold shortAcceptedPivotEvent restrictedAcceptedPivotEvent
  exact Finset.mem_filter.mpr
    ⟨hshort, singleton_mem_acceptedLeftmostZeroEvent w hw x i hi⟩

/-- The accepted short-radius pivot contribution consists of its exactly
known singleton gain and an *unrestricted signed* non-singleton remainder. -/
theorem shortAcceptedPivotEvent_drop_eq_singleton_add_remainder {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n -> Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : Nat) (hb : 2 ≤ b)
    (i : Fin n) (hi : x i = false) :
    law.acceptedEventWeightedPotentialDrop
        (shortAcceptedPivotEvent w x b i) w g x =
      (law.oneBitMass / (n : Real)) * g i +
        law.acceptedEventWeightedPotentialDrop
          (shortPivotRemainderEvent w x b i) w g x := by
  classical
  let event := shortAcceptedPivotEvent w x b i
  let single : MutationMask n := {i}
  let F : MutationMask n -> Real := fun mask =>
    law.weight mask *
      (linearErrorPotential g x -
        linearErrorPotential g (selectedAfterMask (linearFitness w) x mask))
  have hsing : single ∈ event :=
    singleton_mem_shortAcceptedPivotEvent w hw x b hb i hi
  have hsum := Finset.sum_erase_add event F hsing
  have hscalar : F single = (law.oneBitMass / (n : Real)) * g i := by
    dsimp [F, single]
    rw [law.singletonWeight_eq_oneBitMass_div hn i,
      selected_single_zero_flip_linearError_drop w g hw x i hi]
  unfold acceptedEventWeightedPotentialDrop shortPivotRemainderEvent
  change (∑ mask ∈ event, F mask) =
    (law.oneBitMass / (n : Real)) * g i +
      (∑ mask ∈ event.erase single, F mask)
  calc
    (∑ mask ∈ event, F mask) =
        (∑ mask ∈ event.erase single, F mask) + F single := hsum.symm
    _ = (law.oneBitMass / (n : Real)) * g i +
          (∑ mask ∈ event.erase single, F mask) := by
      rw [hscalar]
      ring

/-- Exact singleton contribution plus a signed sum of accepted short-pivot
non-singleton remainders.  This proves an identity, not a positivity claim. -/
theorem acceptedEventWeightedPotentialDrop_short_eq_singleton_add_remainders
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n -> Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : Nat) (hb : 2 ≤ b) :
    law.acceptedEventWeightedPotentialDrop
        (shortRadiusMaskEvent (n := n) b) w g x =
      (law.oneBitMass / (n : Real)) * (∑ i ∈ zeroPositions x, g i) +
        ∑ i ∈ zeroPositions x,
          law.acceptedEventWeightedPotentialDrop
            (shortPivotRemainderEvent w x b i) w g x := by
  rw [law.acceptedEventWeightedPotentialDrop_short_eq_sum_pivots w g hw x b]
  calc
    (∑ i ∈ zeroPositions x,
      law.acceptedEventWeightedPotentialDrop
        (shortAcceptedPivotEvent w x b i) w g x) =
        ∑ i ∈ zeroPositions x,
          ((law.oneBitMass / (n : Real)) * g i +
            law.acceptedEventWeightedPotentialDrop
              (shortPivotRemainderEvent w x b i) w g x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact law.shortAcceptedPivotEvent_drop_eq_singleton_add_remainder
        hn w g hw x b hb i ((mem_zeroPositions x i).mp hi)
    _ = (law.oneBitMass / (n : Real)) * (∑ i ∈ zeroPositions x, g i) +
          ∑ i ∈ zeroPositions x,
            law.acceptedEventWeightedPotentialDrop
              (shortPivotRemainderEvent w x b i) w g x := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A signed selected-potential change on an accepted event is bounded below
by the negative loss of its actually flipped one-bits. -/
theorem acceptedEventWeightedPotentialDrop_ge_neg_flippedOneLoss_of_accepts
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (event : Finset (MutationMask n))
    (w g : Fin n -> Real) (x : BitString n)
    (hg : forall j, 0 ≤ g j)
    (hacc : ∀ mask ∈ event,
      Accepts (linearFitness w) x (mutateWithMask x mask)) :
    -law.acceptedEventFlippedOneLoss event g x ≤
      law.acceptedEventWeightedPotentialDrop event w g x := by
  classical
  unfold acceptedEventFlippedOneLoss acceptedEventWeightedPotentialDrop
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro mask hm
  have hpoint := linearErrorPotential_selected_drop_ge_neg_oneToZeroLoss_of_accepts
    w g x mask hg (hacc mask hm)
  have hmul := mul_le_mul_of_nonneg_left hpoint (law.weight_nonneg mask)
  nlinarith

/-- The pivot remainder events contain only accepted mutations. -/
theorem shortPivotRemainderEvent_accepts {n : Nat}
    (w : Fin n -> Real) (x : BitString n) (b : Nat)
    (i : Fin n) (mask : MutationMask n)
    (hm : mask ∈ shortPivotRemainderEvent w x b i) :
    Accepts (linearFitness w) x (mutateWithMask x mask) := by
  classical
  have hpivot : mask ∈ shortAcceptedPivotEvent w x b i := by
    exact (Finset.mem_erase.mp hm).2
  exact restrictedAcceptedPivotEvent_accepts
    (shortRadiusMaskEvent (n := n) b) w x i mask hpivot

/-- An unconditional short-radius drift bound.  The debit is the *actual*
accepted one-to-zero loss inside the disjoint non-singleton pivot slices,
not a postulated nonnegative remainder or an all-mask upper envelope. -/
theorem acceptedEventWeightedPotentialDrop_short_ge_singleton_sub_pivotLoss
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n -> Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : Nat) (hb : 2 ≤ b)
    (hg : forall j, 0 ≤ g j) :
    (law.oneBitMass / (n : Real)) * (∑ i ∈ zeroPositions x, g i) -
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) g x) ≤
    law.acceptedEventWeightedPotentialDrop
      (shortRadiusMaskEvent (n := n) b) w g x := by
  have hsplit := law.acceptedEventWeightedPotentialDrop_short_eq_singleton_add_remainders
    hn w g hw x b hb
  have hbudget :
      -(∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) g x) ≤
        ∑ i ∈ zeroPositions x,
          law.acceptedEventWeightedPotentialDrop
            (shortPivotRemainderEvent w x b i) w g x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i hi
    exact law.acceptedEventWeightedPotentialDrop_ge_neg_flippedOneLoss_of_accepts
      (shortPivotRemainderEvent w x b i) w g x hg
      (fun mask hm => shortPivotRemainderEvent_accepts w x b i mask hm)
  linarith

/-- Full drift: singleton gain minus the explicit accepted short-pivot loss
and Stage-92's radius-tail first-moment penalty.  This needs only nonnegative
potential weights, positive objective weights, and the actual law. -/
theorem linearErrorPotential_drift_ge_singleton_sub_pivotLoss_sub_tailMeanRadius
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n -> Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : Nat) (hb : 2 ≤ b)
    (hg : forall j, 0 ≤ g j) :
    (law.oneBitMass / (n : Real)) * (∑ i ∈ zeroPositions x, g i) -
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) g x) -
      (law.tailMeanRadius b / (n : Real)) *
        (∑ j ∈ onePositions x, g j) ≤
    driftAt (law.transition (linearFitness w))
      (linearErrorPotential g) x := by
  have hshort := law.acceptedEventWeightedPotentialDrop_short_ge_singleton_sub_pivotLoss
    hn w g hw x b hb hg
  have htail := law.linearErrorPotential_drift_ge_short_sub_tailMeanRadius
    hn w g x b hg
  linarith

/-- A user-supplied bound on each acceptance-conditioned short-pivot loss
immediately gives a quantitative global drift criterion.  Such budgets are
additional proof obligations; no bound from mean radius alone is asserted. -/
theorem linearErrorPotential_drift_ge_singleton_sub_pivotBudgets_sub_tailMeanRadius
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (w g : Fin n -> Real) (hw : PositiveLinearWeights w)
    (x : BitString n) (b : Nat) (hb : 2 ≤ b)
    (hg : forall j, 0 ≤ g j)
    (budget : Fin n -> Real)
    (hbudget : ∀ i ∈ zeroPositions x,
      law.acceptedEventFlippedOneLoss
        (shortPivotRemainderEvent w x b i) g x ≤ budget i) :
    (law.oneBitMass / (n : Real)) * (∑ i ∈ zeroPositions x, g i) -
      (∑ i ∈ zeroPositions x, budget i) -
      (law.tailMeanRadius b / (n : Real)) *
        (∑ j ∈ onePositions x, g j) ≤
    driftAt (law.transition (linearFitness w))
      (linearErrorPotential g) x := by
  have hbase := law.linearErrorPotential_drift_ge_singleton_sub_pivotLoss_sub_tailMeanRadius
    hn w g hw x b hb hg
  have hsum :
      (∑ i ∈ zeroPositions x,
        law.acceptedEventFlippedOneLoss
          (shortPivotRemainderEvent w x b i) g x) ≤
      ∑ i ∈ zeroPositions x, budget i := by
    apply Finset.sum_le_sum
    intro i hi
    exact hbudget i hi
  linarith

end StaticUnaryUnbiasedMutation
end ECRuntime
