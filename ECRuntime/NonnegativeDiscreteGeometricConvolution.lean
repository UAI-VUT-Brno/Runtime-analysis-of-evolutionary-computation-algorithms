import ECRuntime.AdaptiveOccupationConvolution
import Mathlib

open scoped BigOperators ENNReal
namespace ECRuntime

/-! P01: specialize the certified arbitrary nonnegative occupation convolution
to the geometric residence kernel. The remaining open P01 obligation is
probabilistic: proving that actual path-measure occupation has this convolution
shape, not the countable-sum algebra already certified in Stage 255. -/

/-- Summing all finite-horizon first-entry/geometric residence convolutions
is the product of the entry mass and residence series. -/
theorem proposed_ennreal_geometricEntryResidence_convolution_total
    (entry : Nat → ENNReal) (stay : ENNReal) :
    (∑' t : Nat,
      ∑ k ∈ Finset.range (t + 1), entry k * stay ^ (t - k)) =
    (∑' k : Nat, entry k) * (∑' j : Nat, stay ^ j) := by
  exact proposed_adaptive_occupation_tsum_entryStay_convolution
    entry (fun j => stay ^ j)

end ECRuntime
