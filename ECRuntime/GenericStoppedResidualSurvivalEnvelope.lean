import ECRuntime.GenericDriftLowerFiniteHorizonResearch
import ECRuntime.BellmanGeometricExactRuntime
import Mathlib

namespace ECRuntime

/-! P07: the stopped residual in the finite lower-drift inequality
is a Bellman residual with an absorbing target. Because the potential
vanishes on the target, the existing survival-envelope theorem applies
verbatim, with no unwarranted finite-horizon residual deletion. -/

/-- A finite-state stopped potential, bounded by `B`, has residual
expectation bounded by `B` times the genuine non-target survival mass. -/
theorem proposed_genericDriftLower_stoppedPotential_le_survival
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun y : α => y ∈ target)]
    (hP : IsStochastic P) (potential : α → Real)
    (hzero : ∀ y ∈ target, potential y = 0)
    (B : Real) (hbound : ∀ y, potential y ≤ B)
    (t : Nat) (x : α) :
    finiteStoppedPotential P target potential t x ≤
      B * finiteLevelSurvival P targetᶜ t x := by
  classical
  have heq : ∀ t : Nat, ∀ y : α,
      finiteStoppedPotential P target potential t y =
        stage127_bellmanResidual P target potential t y := by
    intro k
    induction k with
    | zero =>
        intro y
        rfl
    | succ k ih =>
        intro y
        by_cases hy : y ∈ target
        · simp [finiteStoppedPotential, stage127_bellmanResidual, hy,
            hzero y hy]
        · simp only [finiteStoppedPotential, stage127_bellmanResidual,
            if_neg hy]
          unfold expectedValueAfter
          apply Finset.sum_congr rfl
          intro z _
          rw [ih z]
  rw [heq t x]
  exact stage127_bellmanResidual_le_survival
    P target hP potential hzero B hbound t x

end ECRuntime
