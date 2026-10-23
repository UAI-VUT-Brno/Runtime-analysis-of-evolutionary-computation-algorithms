import ECRuntime.LeadingOnesStationaryAntitone
import Mathlib

namespace ECRuntime

/-!
Stage 155 — USER-APPROVED PROVISIONAL PUBLIC THEOREM.
Böttcher--Doerr--Neumann (2010), fixed-rate LeadingOnes.
The stationary equation has opposite signs at rates 1 and 2. Existence
via the intermediate value theorem is the next independent step toward
Stage 111's unique global minimizer. This module is provisionally public for the Round 36 full promotion gate.
-/

/-- A stationary mutation-rate constant exists strictly between 1 and 2.
The interior root is obtained by applying the intermediate-value theorem
to the continuous stationary equation; no numerical approximation is used. -/
theorem proposed_leadingOnes_stationaryRoot_exists :
    ∃ c : Real, 1 < c ∧ c < 2 ∧ (2 - c) * Real.exp c = 2 := by
  let f : Real → Real := fun c => (2 - c) * Real.exp c - 2
  have hcont : Continuous f := by
    dsimp [f]
    fun_prop
  have hleft : 0 < f 1 := by
    dsimp [f]
    have he := Real.exp_one_gt_two
    norm_num at *
    linarith
  have hright : f 2 < 0 := by
    dsimp [f]
    norm_num
  -- Find c in [1,2] where f(c)=0 by the intermediate value theorem.
  -- Endpoint inequalities then imply 1<c<2.
  have hroot : ∃ c ∈ Set.Icc (1 : Real) 2, f c = 0 := by
    -- Work with -f so that its endpoint values are increasing. The
    -- intermediate-value theorem returns a point of the CLOSED interval;
    -- strictness of the endpoint signs will subsequently rule out both ends.
    let g : Real → Real := fun x => -f x
    have hgcont : Continuous g := hcont.neg
    have hmem : (0 : Real) ∈ Set.Icc (g 1) (g 2) := by
      change -f 1 ≤ (0 : Real) ∧ 0 ≤ -f 2
      constructor <;> linarith
    have himage : Set.Icc (g 1) (g 2) ⊆
        g '' Set.Icc (1 : Real) 2 := by
      exact intermediate_value_Icc (by norm_num : (1 : Real) ≤ 2)
        hgcont.continuousOn
    obtain ⟨c, hc, hzero⟩ := himage hmem
    refine ⟨c, hc, ?_⟩
    change -f c = 0 at hzero
    linarith
  rcases hroot with ⟨c, hc, hz⟩
  rcases Set.mem_Icc.mp hc with ⟨hc1, hc2⟩
  have hc1' : 1 < c := by
    rcases lt_or_eq_of_le hc1 with hlt | heq
    · exact hlt
    · subst c
      have hz' : f 1 = 0 := hz
      linarith
  have hc2' : c < 2 := by
    rcases lt_or_eq_of_le hc2 with hlt | heq
    · exact hlt
    · subst c
      have hz' : f 2 = 0 := hz
      linarith
  refine ⟨c, hc1', hc2', ?_⟩
  dsimp [f] at hz
  linarith

end ECRuntime
