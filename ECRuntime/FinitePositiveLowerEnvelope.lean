import Mathlib

namespace ECRuntime

/-!
Stage 228 (NEW, pending approval): generic finite-state positive minimum.
It supplies a uniform progress constant once strict positivity has been proved
at every state. The theorem does not assume or conclude almost-sure hitting.
-/

/-- A strictly positive function on a finite type admits a single strictly
positive lower bound valid at every state. -/
theorem proposed_finite_positive_uniform_lower
    {alpha : Type*} [Fintype alpha]
    (f : alpha -> Real) (hpos : ∀ x, 0 < f x) :
    ∃ delta : Real, 0 < delta ∧ ∀ x, delta <= f x := by
  classical
  have aux : ∀ s : Finset alpha,
      (∀ x, x ∈ s -> 0 < f x) ->
      ∃ delta : Real, 0 < delta ∧ ∀ x, x ∈ s -> delta <= f x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        refine ⟨1, by norm_num, ?_⟩
        intro x hx
        simp at hx
    | @insert a s ha ih =>
        intro hposS
        have hposA : 0 < f a := hposS a (Finset.mem_insert_self a s)
        have hrest : ∀ x, x ∈ s -> 0 < f x := by
          intro x hx
          exact hposS x (Finset.mem_insert_of_mem hx)
        obtain ⟨delta, hdelta, hle⟩ := ih hrest
        refine ⟨min delta (f a), lt_min hdelta hposA, ?_⟩
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxs
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hle x hxs)
  obtain ⟨delta, hdelta, hle⟩ := aux Finset.univ (by
    intro x _; exact hpos x)
  exact ⟨delta, hdelta, fun x => hle x (Finset.mem_univ x)⟩

end ECRuntime
