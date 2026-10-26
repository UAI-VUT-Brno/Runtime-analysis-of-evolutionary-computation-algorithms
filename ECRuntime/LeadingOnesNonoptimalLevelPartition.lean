import ECRuntime.LeadingOnesAdaptiveAbsorbingPath
import Mathlib

namespace ECRuntime

/-! P01: the finite exact-level partition behind the nonoptimal occupation
series. No probability or finite-horizon approximation is used here. -/

/-- Every suboptimal LeadingOnes state has a unique exact score index below `n`. -/
theorem proposed_leadingOnes_nonoptimal_iff_exists_exactLevel
    {n : Nat} (x : BitString n) :
    leadingOnes x < n ↔ ∃ i : Fin n, leadingOnes x = i.val := by
  constructor
  · intro h
    exact ⟨⟨leadingOnes x, h⟩, rfl⟩
  · rintro ⟨i, hi⟩
    rw [hi]
    exact i.isLt

/-- The nonoptimal target complement is exhausted by the finitely many
exact score levels, including the zero-dimensional edge case. -/
theorem proposed_leadingOnes_notTarget_iff_exists_exactLevel
    {n : Nat} (x : BitString n) :
    x ∉ leadingOnesTarget n ↔ ∃ i : Fin n, leadingOnes x = i.val := by
  exact (proposed_leadingOnes_lt_dim_iff_not_target x).symm.trans
    (proposed_leadingOnes_nonoptimal_iff_exists_exactLevel x)

end ECRuntime
