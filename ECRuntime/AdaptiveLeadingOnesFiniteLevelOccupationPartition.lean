import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.LeadingOnesAdaptiveAbsorbingPath
import ECRuntime.LeadingOnesNonoptimalLevelPartition
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory
namespace ECRuntime

/-! Stage 304 (P01 research). A genuine trajectory-measure partition of the
probability of being nonoptimal into its disjoint exact LeadingOnes levels.
Unlike a finite surrogate, every summand refers to the actual Markov path law.
Mathlib's finite `measure_biUnion_finset`/disjoint-union machinery is the
natural proof route. -/

/-- Exact-time nonoptimal survival mass is the finite sum of exact-level
occupations, with no almost-sure termination assumption. -/
theorem proposed_leadingOnesAdaptive_nonoptimalMass_eq_sumExactLevels
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (x : BitString n) (t : Nat) :
    transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
        {path : Nat → BitString n |
          leadingOnes (transitionTrajectoryState x path t) < n} =
      ∑ i : Fin n,
        transitionTrajectoryMeasure
          (leadingOnesAdaptiveTransition rate)
          (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x
          {path : Nat → BitString n |
            leadingOnes (transitionTrajectoryState x path t) = i.val} := by
  classical
  let P : TransitionMatrix (BitString n) :=
    leadingOnesAdaptiveTransition (n := n) rate
  let hP : IsStochastic P :=
    proposed_leadingOnesAdaptive_transition_stochastic (n := n) rate hrate
  let μ : Measure (Nat → BitString n) := transitionTrajectoryMeasure P hP x
  let L : Fin n → Set (Nat → BitString n) :=
    fun j => {path | leadingOnes (transitionTrajectoryState x path t) = j.val}
  have hstate :
      Measurable (fun path : Nat → BitString n =>
        transitionTrajectoryState x path t) := by
    cases t with
    | zero => simpa only [transitionTrajectoryState_zero] using
        (measurable_const : Measurable (fun _ : Nat → BitString n => x))
    | succ k => simpa only [transitionTrajectoryState_succ] using
        (measurable_pi_apply (k + 1) :
          Measurable (fun path : Nat → BitString n => path (k + 1)))
  have hm : ∀ j : Fin n, MeasurableSet (L j) := by
    intro j
    have hlevel : MeasurableSet
        ({z : BitString n | leadingOnes z = j.val} : Set (BitString n)) :=
      (Set.to_countable _).measurableSet
    exact hlevel.preimage hstate
  have hd : ((↑(Finset.univ : Finset (Fin n))) : Set (Fin n)).PairwiseDisjoint L := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro path hi hj
    exact hij (Fin.ext (hi.symm.trans hj))
  have hcover :
      {path : Nat → BitString n |
        leadingOnes (transitionTrajectoryState x path t) < n} =
        ⋃ j ∈ (Finset.univ : Finset (Fin n)), L j := by
    ext path
    constructor
    · intro h
      obtain ⟨j, hj⟩ :=
        (proposed_leadingOnes_nonoptimal_iff_exists_exactLevel
          (transitionTrajectoryState x path t)).mp h
      exact Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_univ j, hj⟩⟩
    · intro h
      obtain ⟨j, h⟩ := Set.mem_iUnion.mp h
      obtain ⟨_, hj⟩ := Set.mem_iUnion.mp h
      exact (proposed_leadingOnes_nonoptimal_iff_exists_exactLevel
        (transitionTrajectoryState x path t)).mpr ⟨j, hj⟩
  change μ _ = ∑ j : Fin n, μ (L j)
  rw [hcover]
  simpa only [L] using
    (MeasureTheory.measure_biUnion_finset (μ := μ)
      (s := (Finset.univ : Finset (Fin n))) (f := L)
      hd (by intro j _; exact hm j))

end ECRuntime
