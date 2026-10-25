import ECRuntime.IndependentBitCoordinateFlipMarginalResearch
import ECRuntime.StaticUnaryUnbiasedFlipMarginals
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-! P07: an exact first-moment identity for genuinely independent-bit
mutation, derived from certified coordinate marginals and finite double
counting. Unlike the singleton mass, this is the full expected radius. -/

/-- The mean number of mutated bits is `n*p`, including dimension zero. -/
theorem proposed_independentBitLaw_meanRadius_eq_n_mul_p
    (n : Nat) (p : Real) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (StaticUnaryUnbiasedMutation.independentBitLaw (n := n) p hp0 hp1).meanRadius =
      (n : Real) * p := by
  let law : StaticUnaryUnbiasedMutation n :=
    StaticUnaryUnbiasedMutation.independentBitLaw p hp0 hp1
  change law.meanRadius = (n : Real) * p
  rw [← law.sum_coordinateFlipMass_eq_meanRadius]
  change (∑ i : Fin n,
    (StaticUnaryUnbiasedMutation.independentBitLaw (n := n) p hp0 hp1).coordinateFlipMass i) =
      (n : Real) * p
  simp_rw [proposed_independentBitLaw_coordinateFlipMass_eq_p p hp0 hp1]
  simp

end ECRuntime
