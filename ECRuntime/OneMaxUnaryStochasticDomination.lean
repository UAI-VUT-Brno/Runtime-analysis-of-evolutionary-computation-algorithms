import ECRuntime.OneMax
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.DirectGeometricStochasticDominationClosed
import ECRuntime.LeadingOnesResidence
import ECRuntime.MultiplicativeDriftTail
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
Stage 108 (A3 strengthening) promotion-preparation source: geometric-sum domination for OneMax.
The statement gate and standalone pinned elaboration passed; full verification is pending.
Source: Doerr (2019), Analyzing Randomized Search Heuristics via Stochastic
Domination. The sum has all n levels, not just initially present levels.
-/

/-- A lower bound on the probability of leaving level i+1. -/
noncomputable def oneMaxGeometricRates {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) : Fin n → Real :=
  fun i => ((i.val + 1 : Nat) : Real) * law.oneBitMass / (n : Real)

/-- Every geometric comparison rate is positive when the singleton mass is. -/
theorem oneMaxGeometricRates_pos {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (hp : 0 < law.oneBitMass) :
    ∀ i : Fin n, 0 < oneMaxGeometricRates law i := by
  intro i
  unfold oneMaxGeometricRates
  have hi : (0 : Real) < (i.val + 1 : Nat) := by exact_mod_cast (Nat.succ_pos i.val)
  have hnreal : (0 : Real) < n := by exact_mod_cast hn
  exact div_pos (mul_pos hi hp) hnreal

/-- Every geometric comparison rate is a valid probability. -/
theorem oneMaxGeometricRates_le_one {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) :
    ∀ i : Fin n, oneMaxGeometricRates law i ≤ 1 := by
  have hmem : 1 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hp : law.oneBitMass ≤ 1 := by
    unfold oneBitMass
    calc
      law.radiusMass 1 ≤ ∑ k ∈ Finset.range (n + 1), law.radiusMass k := by
        exact Finset.single_le_sum (fun k _ => law.radiusMass_nonneg k) hmem
      _ = 1 := law.sum_radiusMass_eq_one
  intro i
  have hindex : ((i.val + 1 : Nat) : Real) ≤ (n : Real) := by
    exact_mod_cast (Nat.succ_le_iff.mpr i.isLt)
  have hnreal : 0 < (n : Real) := by exact_mod_cast hn
  have hprod : ((i.val + 1 : Nat) : Real) * law.oneBitMass ≤ (n : Real) := by
    calc
      ((i.val + 1 : Nat) : Real) * law.oneBitMass ≤
          (n : Real) * law.oneBitMass :=
        mul_le_mul_of_nonneg_right hindex law.oneBitMass_nonneg
      _ ≤ (n : Real) * 1 :=
        mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n)
      _ = (n : Real) := by ring
  exact (div_le_iff₀ hnreal).2 (by simpa [oneMaxGeometricRates] using hprod)

/-- Exact-level exit mass is at least the singleton improvement mass. -/
theorem oneMaxUnary_exactLevelExit
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n) :
    HasUniformExactLevelExitBounds (law.transition oneMaxReal)
      oneMaxPotential (oneMaxGeometricRates law) := by
  intro i z hz
  have hlevel : oneMaxPotential z = i.val + 1 :=
    (mem_exactPositivePotentialLevel oneMaxPotential i z).mp hz
  have hlevelZ : zeroCount z = i.val + 1 := by
    simpa [oneMaxPotential] using hlevel
  have hmask :
      (∑ mask ∈ singleZeroMasks z, law.weight mask) =
        law.singleZeroFlipWeight z := by
    unfold singleZeroMasks singleZeroFlipWeight
    rw [Finset.sum_image]
    intro j _ j' _ hjj'
    exact Finset.singleton_injective hjj'
  have hrate :
      oneMaxGeometricRates law i =
        (∑ mask ∈ singleZeroMasks z, law.weight mask) := by
    rw [hmask, law.singleZeroFlipWeight_eq hn z]
    simp only [oneMaxGeometricRates, hlevelZ]
    ring
  have hsub : ∀ mask ∈ singleZeroMasks z,
      selectedAfterMask oneMaxReal z mask ∉
        exactPositivePotentialLevel oneMaxPotential i := by
    intro mask hm hstay
    rcases Finset.mem_image.mp hm with ⟨j, hj, rfl⟩
    have hjzero : z j = false := (mem_zeroPositions z j).mp hj
    have hdrop := oneMaxPotential_selected_single_zero_flip_lt z j hjzero
    have hsame := (mem_exactPositivePotentialLevel oneMaxPotential i _).mp hstay
    omega
  have hmaskBound : oneMaxGeometricRates law i ≤
      finiteEventMass law.weight (fun mask : MutationMask n =>
        selectedAfterMask oneMaxReal z mask ∉
          exactPositivePotentialLevel oneMaxPotential i) := by
    calc
      oneMaxGeometricRates law i =
          ∑ mask ∈ singleZeroMasks z, law.weight mask := hrate
      _ ≤ finiteEventMass law.weight (fun mask : MutationMask n =>
          selectedAfterMask oneMaxReal z mask ∉
            exactPositivePotentialLevel oneMaxPotential i) := by
          exact sum_le_finiteEventMass_of_subset law.weight _
            (singleZeroMasks z) law.weight_nonneg hsub
  have hpush :
      finiteEventMass (law.transition oneMaxReal z) (fun y =>
        y ∉ exactPositivePotentialLevel oneMaxPotential i) =
      finiteEventMass law.weight (fun mask : MutationMask n =>
        selectedAfterMask oneMaxReal z mask ∉
          exactPositivePotentialLevel oneMaxPotential i) := by
    unfold StaticUnaryUnbiasedMutation.transition finiteRandomTransition
    exact finiteEventMass_pushforwardWeight law.weight
      (selectedAfterMask oneMaxReal z)
      (fun y => y ∉ exactPositivePotentialLevel oneMaxPotential i)
  calc
    oneMaxGeometricRates law i ≤
        finiteEventMass law.weight (fun mask : MutationMask n =>
          selectedAfterMask oneMaxReal z mask ∉
            exactPositivePotentialLevel oneMaxPotential i) := hmaskBound
    _ = finiteEventMass (law.transition oneMaxReal z) (fun y =>
          y ∉ exactPositivePotentialLevel oneMaxPotential i) := hpush.symm

/-- The OneMax zero count cannot increase on positive-probability transitions. -/
theorem oneMaxUnary_nonincreasing_support
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) :
    HasPotentialNonincreasingTransitionSupport
      (law.transition oneMaxReal) oneMaxPotential := by
  intro x y hxy
  by_contra hnle
  have hmask (mask : MutationMask n) :
      selectedAfterMask oneMaxReal x mask ≠ y := by
    intro h
    apply hnle
    rw [← h]
    exact oneMaxPotential_selectedAfterMask_le x mask
  have hzero : law.transition oneMaxReal x y = 0 := by
    unfold StaticUnaryUnbiasedMutation.transition finiteRandomTransition pushforwardWeight
    apply Finset.sum_eq_zero
    intro mask _
    simp [hmask mask]
  rw [hzero] at hxy
  exact (lt_irrefl (0 : Real)) hxy

/-- Unrestricted first-hitting time is dominated by a sum of n independent
one-based geometric waiting times of rates (i+1) p_1 / n. -/
theorem oneMaxUnary_hittingTime_stochasticDomination
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (hp : 0 < law.oneBitMass)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)] (x : BitString n) :
    StochasticallyDominated
      (transitionTrajectoryMeasure
        (law.transition oneMaxReal) (law.transition_stochastic oneMaxReal) x)
      (transitionTrajectoryFirstHittingTime (oneMaxTarget n) x)
      (geometricWaitingSumMeasure
        (geometricLevelProbabilityVector
          (oneMaxGeometricRates law)
          (oneMaxGeometricRates_pos law hn hp)
          (oneMaxGeometricRates_le_one law hn))) id := by
  have hbound : ∀ z : BitString n, oneMaxPotential z ≤ n := by
    intro z
    exact zeroCount_le z
  have h :=
    stochasticallyDominated_transitionTrajectoryPotentialHittingTime_geometricWaitingSum
      (law.transition oneMaxReal) (law.transition_stochastic oneMaxReal)
      oneMaxPotential hbound (oneMaxGeometricRates law)
      (oneMaxGeometricRates_pos law hn hp)
      (oneMaxGeometricRates_le_one law hn)
      (law.oneMaxUnary_exactLevelExit hn)
      (law.oneMaxUnary_nonincreasing_support) x
  -- `oneMaxTarget` uses an explicit eta-expanded potential and a distinct
  -- decidability instance.  First-hitting times are target-extensional.
  have htarget : oneMaxTarget n =
      potentialTarget (oneMaxPotential (n := n)) := by rfl
  have htime :
      transitionTrajectoryFirstHittingTime (oneMaxTarget n) x =
        transitionTrajectoryFirstHittingTime
          (potentialTarget (oneMaxPotential (n := n))) x :=
    transitionTrajectoryFirstHittingTime_congr_set
      (oneMaxTarget n) (potentialTarget (oneMaxPotential (n := n)))
      htarget x
  rw [htime]
  exact h

end StaticUnaryUnbiasedMutation
end ECRuntime
