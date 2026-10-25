import Mathlib

namespace ECRuntime

/-! P01: a finite, real-valued equality-case lemma needed to deduce local
optimality from an equality of global runtime contributions. In Stage 426
these real identities must still be reconciled with ENNReal reciprocals. -/

/-- A sum of coordinatewise smaller real costs equals its comparison sum
only when every individual cost is equal. -/
theorem proposed_finiteRealCosts_eq_of_sum_eq
    {alpha : Type*} (s : Finset alpha) (a b : alpha -> Real)
    (hle : forall i, i ∈ s -> a i <= b i)
    (hsum : (Finset.sum s a) = Finset.sum s b) :
    forall i, i ∈ s -> a i = b i := by
  classical
  intro i hi
  by_contra hne
  have hlt : a i < b i := lt_of_le_of_ne (hle i hi) hne
  have hstrict : Finset.sum s a < Finset.sum s b := by
    apply Finset.sum_lt_sum (fun j hj => hle j hj)
    exact ⟨i, hi, hlt⟩
  exact (not_lt_of_ge hsum.ge) hstrict

end ECRuntime
