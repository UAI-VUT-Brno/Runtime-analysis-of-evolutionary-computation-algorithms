import ECRuntime.NonnegativeDiscreteGeometricConvolution
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: isolate the precise mathematical interface that converts a
*genuine* pointwise first-entry convolution into its total occupation
product. The remaining missing obligation is the probabilistic convolution,
not algebraic exchange of nonnegative sums. -/

/-- If the actual occupation sequence is the first-entry/geometric-stay
convolution, then its sum is the product of entry mass and residence mass. -/
theorem proposed_ennreal_trueOccupation_total_of_firstEntryConvolution
    (occupation entry : Nat → ENNReal) (stay : ENNReal)
    (hconvolution : ∀ t : Nat,
      occupation t =
        ∑ k ∈ Finset.range (t + 1), entry k * stay ^ (t - k)) :
    (∑' t : Nat, occupation t) =
      (∑' k : Nat, entry k) * (∑' j : Nat, stay ^ j) := by
  calc
    (∑' t : Nat, occupation t) =
        ∑' t : Nat,
          ∑ k ∈ Finset.range (t + 1), entry k * stay ^ (t - k) := by
      apply tsum_congr
      intro t
      exact hconvolution t
    _ = _ := proposed_ennreal_geometricEntryResidence_convolution_total
      entry stay

end ECRuntime
