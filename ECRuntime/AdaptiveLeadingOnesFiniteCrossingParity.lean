import ECRuntime.AdaptiveLeadingOnesUniformHistoryWeightFlip
import ECRuntime.LeadingOnesFirstCrossingMass
import Mathlib

namespace ECRuntime

/-!
Stage 219 (NEW, awaiting statement approval): the coordinate-flip
involution exchanges first crossing exactly at score i with strictly
skipping score i, and the adaptive history weight is invariant. Reindex
finite sums over the whole finite-history type using the already certified
equivalence. No stochasticity hypothesis is needed for this algebraic
weight identity; probabilistic interpretation requires admissible rates.
-/

/-- Adaptive uniform-start mass of first crossings landing exactly at i
at finite crossing time t. -/
noncomputable def leadingOnesAdaptiveFirstCrossingExactMass
    {n t : Nat} (rate : Nat -> Real) (i : Fin n) : Real := by
  classical
  exact ∑ h : LeadingOnesFiniteHistory n t,
    if leadingOnesFirstCrossingExact i h then
      leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0

/-- Adaptive uniform-start mass of first crossings strictly skipping i
at finite crossing time t. -/
noncomputable def leadingOnesAdaptiveFirstCrossingSkipMass
    {n t : Nat} (rate : Nat -> Real) (i : Fin n) : Real := by
  classical
  exact ∑ h : LeadingOnesFiniteHistory n t,
    if leadingOnesFirstCrossingSkip i h then
      leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0

/-- At every finite crossing time, exact visits and strict skips have equal
uniform-start mass for arbitrary score-dependent mutation rates. -/
theorem proposed_leadingOnesAdaptive_firstCrossingExactMass_eq_skipMass
    {n t : Nat} (rate : Nat -> Real) (i : Fin n) :
    leadingOnesAdaptiveFirstCrossingExactMass (t := t) rate i =
      leadingOnesAdaptiveFirstCrossingSkipMass (t := t) rate i := by
  classical
  unfold leadingOnesAdaptiveFirstCrossingExactMass
    leadingOnesAdaptiveFirstCrossingSkipMass
  refine Fintype.sum_equiv (leadingOnesFiniteHistoryFlipEquiv (t := t) i)
    (fun h : LeadingOnesFiniteHistory n t =>
      if leadingOnesFirstCrossingExact i h then
        leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0)
    (fun h : LeadingOnesFiniteHistory n t =>
      if leadingOnesFirstCrossingSkip i h then
        leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0) ?_
  intro h
  change
    (if leadingOnesFirstCrossingExact i h then
      leadingOnesAdaptiveUniformFiniteHistoryWeight rate h else 0) =
      (if leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h) then
        leadingOnesAdaptiveUniformFiniteHistoryWeight rate
          (leadingOnesFiniteHistoryFlip i h) else 0)
  by_cases hexact : leadingOnesFirstCrossingExact i h
  · have hskipFlip :
        leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h) :=
      (leadingOnesFirstCrossingSkip_flip_iff_exact i h).2 hexact
    have hpre : leadingOnesHistoryPreCrossing i h := hexact.1
    rw [if_pos hexact, if_pos hskipFlip]
    exact (proposed_leadingOnesAdaptive_uniformHistoryWeight_flip
      rate i h hpre).symm
  · have hnotSkipFlip :
        Not (leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h)) := by
      intro hskipFlip
      exact hexact ((leadingOnesFirstCrossingSkip_flip_iff_exact i h).1 hskipFlip)
    rw [if_neg hexact, if_neg hnotSkipFlip]

end ECRuntime
