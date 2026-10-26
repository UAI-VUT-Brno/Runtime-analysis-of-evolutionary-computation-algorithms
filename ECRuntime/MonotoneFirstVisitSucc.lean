import Mathlib

namespace ECRuntime

/-! P01. A deterministic bridge between the first-visit predicate at a
positive time and the adjacent below-to-exact entry predicate. This theorem
requires path monotonicity; it is *not* a statement about arbitrary paths. -/

/-- On a nondecreasing integer-valued trajectory, the first visit to level
`i` at time `t+1` is exactly a transition from below `i` to `i`. -/
theorem proposed_monotoneScore_firstVisitSucc_iff
    (f : Nat → Nat) (hmono : Monotone f) (i t : Nat) :
    (f (t + 1) = i ∧ ∀ s : Nat, s < t + 1 → f s ≠ i) ↔
      (f t < i ∧ f (t + 1) = i) := by
  constructor
  · rintro ⟨hit, hfirst⟩
    constructor
    · have hle : f t ≤ i := by
        simpa [hit] using hmono (Nat.le_succ t)
      have hne : f t ≠ i := hfirst t (Nat.lt_succ_self t)
      omega
    · exact hit
  · rintro ⟨hbelow, hit⟩
    constructor
    · exact hit
    · intro s hs heq
      have hle : f s ≤ f t := hmono (Nat.le_of_lt_succ hs)
      omega

end ECRuntime
