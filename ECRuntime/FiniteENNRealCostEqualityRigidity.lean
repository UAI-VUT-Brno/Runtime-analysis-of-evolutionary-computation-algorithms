import ECRuntime.FiniteCostSumEqualityRigidity
import Mathlib

open scoped ENNReal
namespace ECRuntime

/-! P01: the finite, non-top ENNReal equality case omitted from the
real-valued Stage 438 interface.  Finiteness is necessary: adding infinity
would destroy strictness, and the hypothesis cannot be dropped. -/

/-- Equality of finite extended-nonnegative cost sums with pointwise domination
forces equality of every summand. -/
theorem proposed_finiteENNRealCosts_eq_of_sum_eq
    {alpha : Type*} (s : Finset alpha) (a b : alpha -> ENNReal)
    (hfinite : forall i, i ∈ s -> b i ≠ ⊤)
    (hle : forall i, i ∈ s -> a i <= b i)
    (hsum : Finset.sum s a = Finset.sum s b) :
    forall i, i ∈ s -> a i = b i := by
  classical
  have hafinite : forall i, i ∈ s -> a i ≠ ⊤ := by
    intro i hi htop
    have htop_le : (⊤ : ENNReal) <= b i := by
      simpa only [htop] using hle i hi
    exact hfinite i hi (top_unique htop_le)
  have hrealLe : forall i, i ∈ s -> (a i).toReal <= (b i).toReal := by
    intro i hi
    exact ENNReal.toReal_mono (hfinite i hi) (hle i hi)
  have hrealSum : Finset.sum s (fun i => (a i).toReal) =
      Finset.sum s (fun i => (b i).toReal) := by
    simpa only [ENNReal.toReal_sum hafinite, ENNReal.toReal_sum hfinite]
      using congrArg ENNReal.toReal hsum
  have hpoint := proposed_finiteRealCosts_eq_of_sum_eq
    s (fun i => (a i).toReal) (fun i => (b i).toReal) hrealLe hrealSum
  intro i hi
  calc
    a i = ENNReal.ofReal (a i).toReal :=
      ((ENNReal.ofReal_toReal_eq_iff).2 (hafinite i hi)).symm
    _ = ENNReal.ofReal (b i).toReal := congrArg ENNReal.ofReal (hpoint i hi)
    _ = b i := (ENNReal.ofReal_toReal_eq_iff).2 (hfinite i hi)

end ECRuntime
