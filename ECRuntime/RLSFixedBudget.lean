import ECRuntime.RLSOneBitSupport
import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.UnaryOneMaxZeroContraction
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LinearPotential
import ECRuntime.OneMax
import ECRuntime.FiniteTrajectory
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
Provisional public Stage 115 (A7): fixed-budget first moments of the zero count.
Source context: Doerr--Jansen--Witt--Zarges (2013) and Lengler--Spooner
(2015). The claims are about expected remaining zeros, not concentration.
-/

/-- The last state along a length-t finite trajectory, or the starting
state when the trajectory has length zero. -/
def finiteBudgetTerminal {alpha : Type*} :
    (t : Nat) → alpha → FiniteTrajectory alpha t → alpha
  | 0, x, _ => x
  | t + 1, _, path => path (Fin.last t)

/-- A length-(t+1) path has the same terminal point as its tail
of length t, started from the first successor. -/
private theorem candidate_finiteBudgetTerminal_cons
    {α : Type*} (t : Nat) (x y : α)
    (tail : FiniteTrajectory α t) :
    finiteBudgetTerminal (t + 1) x (Fin.cons y tail) =
      finiteBudgetTerminal t y tail := by
  cases t <;> simp [finiteBudgetTerminal]

/-- Generic recursion for a terminal-state observable over finite paths.
This is shared by both fixed-budget approved theorem statements. -/
private theorem candidate_finiteBudgetExpectation_step
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (f : α → Real)
    (t : Nat) (x : α) :
    (∑ path : FiniteTrajectory α (t + 1),
      finiteTrajectoryWeight P (t + 1) x path *
        f (finiteBudgetTerminal (t + 1) x path)) =
    expectedValueAfter P (fun y : α =>
      ∑ tail : FiniteTrajectory α t,
        finiteTrajectoryWeight P t y tail *
          f (finiteBudgetTerminal t y tail)) x := by
  classical
  rw [sum_finiteTrajectory_succ]
  simp_rw [finiteTrajectoryWeight_cons,
    candidate_finiteBudgetTerminal_cons]
  unfold expectedValueAfter
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  ring

/-- A finite-state Markov observable that is an eigenfunction of the
one-step expectation operator has exact geometric finite-budget mean.
This is independent of elitism, objective choice and mutation semantics. -/
private theorem candidate_finiteBudgetExpectation_eigen
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (f : α → Real) (c : Real)
    (heigen : ∀ x, expectedValueAfter P f x = c * f x) :
    ∀ (t : Nat) (x : α),
      (∑ path : FiniteTrajectory α t,
        finiteTrajectoryWeight P t x path *
          f (finiteBudgetTerminal t x path)) = c ^ t * f x := by
  classical
  intro t
  induction t with
  | zero =>
      intro x
      simp [finiteBudgetTerminal, finiteTrajectoryWeight]
  | succ t ih =>
      intro x
      rw [candidate_finiteBudgetExpectation_step]
      calc
        expectedValueAfter P (fun y : α =>
            ∑ tail : FiniteTrajectory α t,
              finiteTrajectoryWeight P t y tail *
                f (finiteBudgetTerminal t y tail)) x =
            expectedValueAfter P (fun y => c ^ t * f y) x := by
              unfold expectedValueAfter
              apply Finset.sum_congr rfl
              intro y _
              exact congrArg (fun v : Real => P x y * v) (ih y)
        _ = c ^ t * expectedValueAfter P f x := by
              unfold expectedValueAfter
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ = c ^ t * (c * f x) := by rw [heigen x]
        _ = c ^ (t + 1) * f x := by rw [pow_succ]; ring

/-- If an observable contracts in conditional expectation by a
nonnegative factor, every finite-budget expectation contracts at that
factor, without an independence assumption between iterations. -/
private theorem candidate_finiteBudgetExpectation_contracts
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (f : α → Real) (c : Real) (hc : 0 ≤ c)
    (hcontract : ∀ x, expectedValueAfter P f x ≤ c * f x) :
    ∀ (t : Nat) (x : α),
      (∑ path : FiniteTrajectory α t,
        finiteTrajectoryWeight P t x path *
          f (finiteBudgetTerminal t x path)) ≤ c ^ t * f x := by
  classical
  intro t
  induction t with
  | zero =>
      intro x
      simp [finiteBudgetTerminal, finiteTrajectoryWeight]
  | succ t ih =>
      intro x
      rw [candidate_finiteBudgetExpectation_step]
      have hmono := expectedValueAfter_mono P hP
        (fun y : α =>
          ∑ tail : FiniteTrajectory α t,
            finiteTrajectoryWeight P t y tail *
              f (finiteBudgetTerminal t y tail))
        (fun y : α => c ^ t * f y)
        (fun y => ih y) x
      calc
        expectedValueAfter P (fun y : α =>
            ∑ tail : FiniteTrajectory α t,
              finiteTrajectoryWeight P t y tail *
                f (finiteBudgetTerminal t y tail)) x ≤
            expectedValueAfter P (fun y => c ^ t * f y) x := hmono
        _ = c ^ t * expectedValueAfter P f x := by
              unfold expectedValueAfter
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro y _
              ring
        _ ≤ c ^ t * (c * f x) :=
              mul_le_mul_of_nonneg_left (hcontract x) (pow_nonneg hc t)
        _ = c ^ (t + 1) * f x := by rw [pow_succ]; ring

/-- Exact reduction of any fixed-budget zero-count expectation for RLS
on positive linear functions to RLS on OneMax. -/
private theorem candidate_rlsFixedBudget_reduce_to_oneMax
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (x : BitString n) (t : Nat) :
    (∑ path : FiniteTrajectory (BitString n) t,
      finiteTrajectoryWeight
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w)) t x path *
        (zeroCount (finiteBudgetTerminal t x path) : Real)) =
    (∑ path : FiniteTrajectory (BitString n) t,
      finiteTrajectoryWeight
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          oneMaxReal) t x path *
        (zeroCount (finiteBudgetTerminal t x path) : Real)) := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw]

/-- Exact fixed-budget expected zero count for RLS on positive linear
objectives: each original zero remains unflipped with probability (1-1/n)^t. -/
theorem rlsLinear_fixedBudget_expectedZeros_eq
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w)
    (x : BitString n) (t : Nat) :
    (Finset.univ.sum (fun path : FiniteTrajectory (BitString n) t =>
      finiteTrajectoryWeight
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w)) t x path *
      (zeroCount (finiteBudgetTerminal t x path) : Real))) =
      (zeroCount x : Real) * (1 - 1 / (n : Real)) ^ t := by
  rw [candidate_rlsFixedBudget_reduce_to_oneMax hn w hw x t]
  have heigen (y : BitString n) :=
    candidate_rlsOneMax_expectedZeroCount_exact hn y
  simpa only [mul_comm] using
    (candidate_finiteBudgetExpectation_eigen
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real))
      (1 - 1 / (n : Real)) heigen t x)

/-- A singleton-mass-only fixed-budget first-moment bound for OneMax under
any static unary-unbiased mutation law, with no radius-moment assumption. -/
theorem oneMaxUnary_fixedBudget_expectedZeros_le
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (hn : 0 < n) (hp : 0 < law.oneBitMass)
    (x : BitString n) (t : Nat) :
    (Finset.univ.sum (fun path : FiniteTrajectory (BitString n) t =>
      finiteTrajectoryWeight (law.transition oneMaxReal) t x path *
        (zeroCount (finiteBudgetTerminal t x path) : Real))) ≤
      (zeroCount x : Real) *
        (1 - law.oneBitMass / (n : Real)) ^ t := by
  have hp1le : law.oneBitMass ≤ 1 := by
    have hmem : 1 ∈ Finset.range (n + 1) :=
      Finset.mem_range.mpr (by omega)
    unfold StaticUnaryUnbiasedMutation.oneBitMass
    calc
      law.radiusMass 1 ≤
          ∑ k ∈ Finset.range (n + 1), law.radiusMass k := by
            exact Finset.single_le_sum
              (fun k _ => law.radiusMass_nonneg k) hmem
      _ = 1 := law.sum_radiusMass_eq_one
  have hnreal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  have hn1 : (1 : Real) ≤ (n : Real) := by exact_mod_cast hn
  have hpnonneg : 0 ≤ law.oneBitMass := le_of_lt hp
  have hc : 0 ≤ 1 - law.oneBitMass / (n : Real) := by
    have hdiv : law.oneBitMass / (n : Real) ≤ 1 :=
      (div_le_iff₀ hnreal).mpr (by linarith [hpnonneg])
    linarith
  have hcontract (y : BitString n) :=
    candidate_unaryOneMax_expectedZeroCount_contracts law hn y
  simpa only [mul_comm] using
    (candidate_finiteBudgetExpectation_contracts
      (law.transition oneMaxReal) (law.transition_stochastic oneMaxReal)
      (fun y : BitString n => (zeroCount y : Real))
      (1 - law.oneBitMass / (n : Real)) hc hcontract t x)

end ECRuntime
