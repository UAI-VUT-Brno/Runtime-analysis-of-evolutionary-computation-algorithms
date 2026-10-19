import ECRuntime.GeometricFailureCouplingReduction
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 71: natural-threshold to full stochastic domination

The Stage-26 direct Bellman route produces tail inequalities at natural thresholds.
For the runtime observables used here this is already enough: the process hitting time
is either a natural number or `⊤`, and the comparison variable can be represented on
the discrete geometric failure-count product, where its waiting sum is a natural
number pointwise.

This file isolates the generic representation-theoretic bridge.  At every finite
`ENNReal` threshold `t`, an `ℕ ∪ {⊤}`-valued observable has the same strict upper-tail
event as at the natural threshold `floor (t.toReal)`.  Thus natural-threshold
domination of two such observables implies full first-order stochastic domination.
-/

/-- An `ENNReal`-valued observable takes only natural-number values or `⊤`. -/
def IsNatOrTopValued {Ω : Type*} (X : Ω -> ENNReal) : Prop :=
  forall ω, X ω = ⊤ ∨ ∃ k : Nat, X ω = (k : ENNReal)

/-- The natural floor used to quantize a finite `ENNReal` threshold. -/
noncomputable def runtimeNaturalFloor (t : ENNReal) : Nat :=
  ⌊t.toReal⌋₊

/-- For a natural-or-top-valued observable, every finite strict upper-tail event is
exactly its strict upper-tail event at the natural floor of the threshold. -/
theorem runtimeTailEvent_eq_natFloor_of_natOrTopValued
    {Ω : Type*} {X : Ω -> ENNReal}
    (hX : IsNatOrTopValued X) (t : ENNReal) (ht : t ≠ ⊤) :
    runtimeTailEvent X t =
      runtimeTailEvent X (runtimeNaturalFloor t : ENNReal) := by
  ext ω
  change (t < X ω) ↔ ((runtimeNaturalFloor t : ENNReal) < X ω)
  rcases hX ω with htop | ⟨n, hn⟩
  · rw [htop]
    constructor
    · intro _
      exact lt_top_iff_ne_top.2 (ENNReal.natCast_ne_top _)
    · intro _
      exact lt_top_iff_ne_top.2 ht
  · rw [hn]
    have ht_nonneg : 0 <= t.toReal := ENNReal.toReal_nonneg
    calc
      t < (n : ENNReal) ↔ t.toReal < (n : Real) := by
        simpa using
          (ENNReal.toReal_lt_toReal ht (ENNReal.natCast_ne_top n)).symm
      _ ↔ runtimeNaturalFloor t < n := by
        simpa [runtimeNaturalFloor] using (Nat.floor_lt ht_nonneg).symm
      _ ↔ (runtimeNaturalFloor t : ENNReal) < (n : ENNReal) := by
        norm_cast

/-- Natural-threshold domination upgrades to full stochastic domination when both
observables take only natural values or `⊤`. -/
theorem stochasticallyDominated_of_natTailDominated_of_natOrTopValued
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {μ : Measure Ω₁} {ν : Measure Ω₂}
    {X : Ω₁ -> ENNReal} {Y : Ω₂ -> ENNReal}
    (hX : IsNatOrTopValued X) (hY : IsNatOrTopValued Y)
    (hNat : NatTailDominated μ X ν Y) :
    StochasticallyDominated μ X ν Y := by
  intro t
  by_cases ht : t = ⊤
  · subst t
    simp [runtimeTailMass, runtimeTailEvent]
  · let k : Nat := runtimeNaturalFloor t
    calc
      runtimeTailMass μ X t =
          runtimeTailMass μ X (k : ENNReal) := by
        unfold runtimeTailMass
        simpa [k] using
          congrArg (fun s : Set Ω₁ => μ s)
            (runtimeTailEvent_eq_natFloor_of_natOrTopValued hX t ht)
      _ <= runtimeTailMass ν Y (k : ENNReal) := hNat k
      _ = runtimeTailMass ν Y t := by
        unfold runtimeTailMass
        symm
        simpa [k] using
          congrArg (fun s : Set Ω₂ => ν s)
            (runtimeTailEvent_eq_natFloor_of_natOrTopValued hY t ht)

/-- The conventional trajectory first-hitting time is pointwise natural-valued when
the target is reached and is `⊤` otherwise. -/
theorem isNatOrTopValued_transitionTrajectoryFirstHittingTime
    {alpha : Type*} (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)] (x : alpha) :
    IsNatOrTopValued (transitionTrajectoryFirstHittingTime target x) := by
  intro path
  classical
  by_cases h : ∃ k, transitionTrajectoryState x path k ∈ target
  · right
    refine ⟨Nat.find h, ?_⟩
    simp [transitionTrajectoryFirstHittingTime, h]
  · left
    simp [transitionTrajectoryFirstHittingTime, h]

/-- The waiting sum attached to a finite vector of geometric failure counts is
pointwise a natural number. -/
theorem isNatOrTopValued_geometricFailureVectorWaitingSum
    {m : Nat} :
    IsNatOrTopValued (geometricFailureVectorWaitingSum (m := m)) := by
  classical
  intro failures
  right
  refine ⟨∑ i : Fin m, (failures i + 1), ?_⟩
  unfold geometricFailureVectorWaitingSum geometricWaitingSum
  unfold geometricWaitingVectorOfFailureCounts geometricWaitingTime
  norm_cast

end ECRuntime
