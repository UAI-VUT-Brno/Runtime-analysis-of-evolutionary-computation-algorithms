import ECRuntime.AdaptiveLeadingOnesBoundaryProgressPositive
import ECRuntime.FinitePositiveLowerEnvelope
import ECRuntime.LeadingOnesBoundaryEventualCrossing
import Mathlib

namespace ECRuntime

/-! Stage 235 (pending approval). A reusable state-uniform, positive
one-step boundary-progress envelope for an interior adaptive schedule.
This is a *local* probabilistic result, not by itself an a.s.-hitting proof. -/

/-- Before a fixed LeadingOnes boundary, a strictly interior score-dependent
mutation schedule admits one common strictly positive lower bound for the
one-step strict boundary-potential decrease probability. -/
theorem proposed_leadingOnesAdaptive_uniformBoundaryProgress
    {n : Nat} (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (i : Fin n) :
    ∃ delta : Real, 0 < delta ∧ ∀ x : BitString n,
      0 < leadingOnesBoundaryPotential i x →
        delta ≤ finiteEventMass
          (fun mask : MutationMask n =>
            mutationMaskWeight (rate (leadingOnes x)) mask)
          (fun mask =>
            leadingOnesBoundaryPotential i
              (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
              leadingOnesBoundaryPotential i x) := by
  classical
  let f : BitString n → Real := fun x =>
    if hx : 0 < leadingOnesBoundaryPotential i x then
      finiteEventMass
        (fun mask : MutationMask n =>
          mutationMaskWeight (rate (leadingOnes x)) mask)
        (fun mask =>
          leadingOnesBoundaryPotential i
            (selectedAfterMask (leadingOnesReal (n := n)) x mask) <
            leadingOnesBoundaryPotential i x)
    else 1
  have hf : ∀ x : BitString n, 0 < f x := by
    intro x
    by_cases hx : 0 < leadingOnesBoundaryPotential i x
    · simp only [f, dif_pos hx]
      exact proposed_leadingOnesAdaptive_boundaryMaskProgress_pos
        rate hrate i x hx
    · simp [f, hx]
  obtain ⟨delta, hdelta, hfloor⟩ :=
    proposed_finite_positive_uniform_lower f hf
  refine ⟨delta, hdelta, ?_⟩
  intro x hx
  simpa only [f, dif_pos hx] using hfloor x

end ECRuntime
