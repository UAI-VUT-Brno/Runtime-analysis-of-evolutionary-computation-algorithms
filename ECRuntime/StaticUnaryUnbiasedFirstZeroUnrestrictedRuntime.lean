import ECRuntime.StaticUnaryUnbiasedFirstZeroFiniteRuntime
import ECRuntime.UnrestrictedRuntime
import ECRuntime.TrajectoryFirstHittingTime
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
# Unrestricted expected runtime for superincreasing objectives

This module combines the proved finite-horizon first-zero bounds with the
generic supremum and sample-path hitting-time semantics. In particular, the
unrestricted expected hitting time is finite and bounded by the sum of exact
level-hazard reciprocals, provided the singleton mutation probability is
positive and the linear weights are superincreasing.

The full sharp upper and matching lower bounds for arbitrary positive linear
objectives in Doerr--Janett--Lengler (2024) are **not** claimed here.
-/
section Stage106Decidability
attribute [local instance] Classical.propDecidable

/-- The unrestricted runtime supremum agrees with the supremum of finite first-zero occupation costs. -/
theorem firstZeroRuntimeSup_eq_iSup_finiteRuntimeMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) :
    runtimeSup (law.transition (linearFitness w))
      (firstZeroOptimalSet (n := n)) x =
      ⨆ T : Nat, ENNReal.ofReal (firstZeroFiniteRuntimeMass law w x T) := by
  -- The unrestricted supremum was already defined using the generic
  -- finite-horizon Bellman expectations. Stage 105 identifies each of them
  -- with the corresponding sum of nonoptimal occupation probabilities.
  unfold runtimeSup
  apply iSup_congr
  intro T
  exact congrArg ENNReal.ofReal
    (firstZeroFiniteRuntimeMass_eq_hittingRuntime law w hw x T).symm

/-- Each finite first-zero occupation cost is bounded by unrestricted runtime. -/
theorem firstZeroFiniteRuntimeMass_ofReal_le_runtimeSup {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) :
    ENNReal.ofReal (firstZeroFiniteRuntimeMass law w x T) ≤
      runtimeSup (law.transition (linearFitness w))
        (firstZeroOptimalSet (n := n)) x := by
  rw [firstZeroFiniteRuntimeMass_eq_hittingRuntime law w hw x T]
  exact finiteHorizonRuntime_ofReal_le_runtimeSup
    (law.transition (linearFitness w))
    (firstZeroOptimalSet (n := n)) T x

/-- The unrestricted expected runtime obeys the sum-of-inverse-hazards bound. -/
theorem firstZeroRuntimeSup_le_hazardCap {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (hp1 : 0 < law.oneBitMass) :
    runtimeSup (law.transition (linearFitness w))
      (firstZeroOptimalSet (n := n)) x ≤
      ENNReal.ofReal
        (∑ i : Fin n, 1 / law.maskEventMass (lowestMaskEvent i)) := by
  rw [firstZeroRuntimeSup_eq_iSup_finiteRuntimeMass law w hw x]
  refine iSup_le ?_
  intro T
  exact ENNReal.ofReal_le_ofReal
    (firstZeroFiniteRuntimeMass_le_hazardCap law w hw x T hp1)

/-- The unrestricted expected runtime is finite when singleton mutation has positive mass. -/
theorem firstZeroRuntimeSup_ne_top {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (hp1 : 0 < law.oneBitMass) :
    runtimeSup (law.transition (linearFitness w))
      (firstZeroOptimalSet (n := n)) x ≠ ⊤ := by
  have hcap := firstZeroRuntimeSup_le_hazardCap law w hw x hp1
  exact ne_top_of_le_ne_top (by simp) hcap

/-- An already-optimal state has zero unrestricted expected runtime. -/
theorem firstZeroRuntimeSup_zero_of_allOnes {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (x : BitString n)
    (hx : firstZeroAllOnes x) :
    runtimeSup (law.transition (linearFitness w))
      (firstZeroOptimalSet (n := n)) x = 0 := by
  have hmem : x ∈ firstZeroOptimalSet (n := n) := hx
  unfold runtimeSup
  apply le_antisymm
  · refine iSup_le ?_
    intro T
    have hzero :
        finiteHorizonRuntime (law.transition (linearFitness w))
          (firstZeroOptimalSet (n := n)) T x = 0 := by
      cases T with
      | zero => rfl
      | succ t =>
          exact finiteHorizonRuntime_succ_of_mem
            (law.transition (linearFitness w))
            (firstZeroOptimalSet (n := n)) t x hmem
    simp [hzero]
  · exact bot_le

/-- The sample-path first-hitting-time integral equals the unrestricted runtime supremum. -/
theorem firstZeroFirstHittingTime_lintegral_eq_runtimeSup {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)] (x : BitString n) :
    (∫⁻ path : Nat → BitString n,
      transitionTrajectoryFirstHittingTime
        (firstZeroOptimalSet (n := n)) x path
      ∂transitionTrajectoryMeasure
        (law.transition (linearFitness w))
        (law.transition_stochastic (linearFitness w)) x) =
      runtimeSup (law.transition (linearFitness w))
        (firstZeroOptimalSet (n := n)) x := by
  exact transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
    (law.transition (linearFitness w))
    (firstZeroOptimalSet (n := n))
    (law.transition_stochastic (linearFitness w)) x

/-- The sample-path expected hitting time satisfies the hazard-cap bound. -/
theorem firstZeroFirstHittingTime_lintegral_le_hazardCap {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hp1 : 0 < law.oneBitMass) :
    (∫⁻ path : Nat → BitString n,
      transitionTrajectoryFirstHittingTime
        (firstZeroOptimalSet (n := n)) x path
      ∂transitionTrajectoryMeasure
        (law.transition (linearFitness w))
        (law.transition_stochastic (linearFitness w)) x) ≤
      ENNReal.ofReal
        (∑ i : Fin n, 1 / law.maskEventMass (lowestMaskEvent i)) := by
  rw [firstZeroFirstHittingTime_lintegral_eq_runtimeSup law w x]
  exact firstZeroRuntimeSup_le_hazardCap law w hw x hp1

/-- The sample-path expected hitting time is finite under positive singleton mass. -/
theorem firstZeroFirstHittingTime_lintegral_ne_top {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hp1 : 0 < law.oneBitMass) :
    (∫⁻ path : Nat → BitString n,
      transitionTrajectoryFirstHittingTime
        (firstZeroOptimalSet (n := n)) x path
      ∂transitionTrajectoryMeasure
        (law.transition (linearFitness w))
        (law.transition_stochastic (linearFitness w)) x) ≠ ⊤ := by
  rw [firstZeroFirstHittingTime_lintegral_eq_runtimeSup law w x]
  exact firstZeroRuntimeSup_ne_top law w hw x hp1

/-- The sample-path expected hitting time vanishes at an optimal initial state. -/
theorem firstZeroFirstHittingTime_lintegral_zero_of_allOnes {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : firstZeroAllOnes x) :
    (∫⁻ path : Nat → BitString n,
      transitionTrajectoryFirstHittingTime
        (firstZeroOptimalSet (n := n)) x path
      ∂transitionTrajectoryMeasure
        (law.transition (linearFitness w))
        (law.transition_stochastic (linearFitness w)) x) = 0 := by
  rw [firstZeroFirstHittingTime_lintegral_eq_runtimeSup law w x]
  exact firstZeroRuntimeSup_zero_of_allOnes law w x hx

end Stage106Decidability
end StaticUnaryUnbiasedMutation
end ECRuntime
