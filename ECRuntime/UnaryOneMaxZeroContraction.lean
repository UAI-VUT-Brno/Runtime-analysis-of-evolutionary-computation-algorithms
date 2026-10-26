import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.OneMax
import ECRuntime.FitnessLevel
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-! Candidate-only shared proof of the exact singleton-mass contraction.
It is used by approved Stages 125 and 115, without importing any numeric
candidate module into the promoted library. -/

/-- The expected zero count contracts by the guaranteed singleton-mutation mass;
all additional accepted mutations can only decrease the zero count. -/
theorem candidate_unaryOneMax_expectedZeroCount_contracts
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (x : BitString n) :
    expectedValueAfter (law.transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real)) x ≤
      (1 - law.oneBitMass / (n : Real)) * (zeroCount x : Real) := by
  classical
  let event : MutationMask n → Prop := fun mask =>
    oneMaxPotential (selectedAfterMask oneMaxReal x mask) < oneMaxPotential x
  have hAll : ∀ mask : MutationMask n,
      oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask) ≤
        oneMaxPotentialReal x := by
    intro mask
    unfold oneMaxPotentialReal
    exact_mod_cast oneMaxPotential_selectedAfterMask_le x mask
  have hEvent : ∀ mask : MutationMask n, event mask →
      oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask) + 1 ≤
        oneMaxPotentialReal x := by
    intro mask hmask
    unfold event at hmask
    unfold oneMaxPotentialReal
    have hnat : oneMaxPotential (selectedAfterMask oneMaxReal x mask) + 1 ≤
        oneMaxPotential x := by omega
    exact_mod_cast hnat
  have hweighted := weightedExpectation_add_eventMass_mul_le
    law.weight event
    (fun mask : MutationMask n =>
      oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask))
    (oneMaxPotentialReal x) 1
    law.weight_nonneg law.weight_sum hAll hEvent
  have hmass :
      (∑ mask ∈ singleZeroMasks x, law.weight mask) =
        law.singleZeroFlipWeight x := by
    unfold singleZeroMasks StaticUnaryUnbiasedMutation.singleZeroFlipWeight
    rw [Finset.sum_image]
    intro i _ j _ hij
    exact Finset.singleton_injective hij
  have hprogress :
      (oneMaxPotential x : Real) * (law.oneBitMass / (n : Real)) ≤
        finiteEventMass law.weight event := by
    calc
      (oneMaxPotential x : Real) * (law.oneBitMass / (n : Real)) =
          law.singleZeroFlipWeight x := by
        simpa [oneMaxPotential] using
          (law.singleZeroFlipWeight_eq hn x).symm
      _ = ∑ mask ∈ singleZeroMasks x, law.weight mask := hmass.symm
      _ ≤ finiteEventMass law.weight event := by
        apply sum_le_finiteEventMass_of_subset
        · exact law.weight_nonneg
        · intro mask hm
          rcases Finset.mem_image.mp hm with ⟨i, hi, himask⟩
          subst mask
          exact oneMaxPotential_selected_single_zero_flip_lt x i
            ((mem_zeroPositions x i).mp hi)
  have hEV :
      expectedValueAfter (law.transition oneMaxReal) oneMaxPotentialReal x =
        ∑ mask : MutationMask n, law.weight mask *
          oneMaxPotentialReal (selectedAfterMask oneMaxReal x mask) := by
    unfold expectedValueAfter StaticUnaryUnbiasedMutation.transition
      finiteRandomTransition
    exact pushforwardWeight_expectation
      (w := law.weight) (f := selectedAfterMask oneMaxReal x)
      oneMaxPotentialReal
  have hdrift :
      (oneMaxPotential x : Real) * (law.oneBitMass / (n : Real)) ≤
        oneMaxPotentialReal x -
          expectedValueAfter (law.transition oneMaxReal) oneMaxPotentialReal x := by
    rw [hEV]
    dsimp [event] at hweighted hprogress
    simp only [one_mul] at hweighted
    unfold oneMaxPotentialReal at hweighted ⊢
    linarith
  change expectedValueAfter (law.transition oneMaxReal) oneMaxPotentialReal x ≤
    (1 - law.oneBitMass / (n : Real)) * oneMaxPotentialReal x
  dsimp [oneMaxPotentialReal, oneMaxPotential] at hdrift ⊢
  nlinarith [hdrift]

/-- The approved Stage-125 one-step contraction, independent of any
higher moments of the mutation-radius distribution. -/
theorem proposed_unaryOneMax_expectedZeroCount_contracts
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (x : BitString n) :
    expectedValueAfter (law.transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real)) x ≤
      (1 - law.oneBitMass / (n : Real)) * (zeroCount x : Real) := by
  exact candidate_unaryOneMax_expectedZeroCount_contracts law hn x


end ECRuntime
