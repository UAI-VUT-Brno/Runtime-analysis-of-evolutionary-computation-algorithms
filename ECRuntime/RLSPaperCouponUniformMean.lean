import ECRuntime.RLSCouponProcessKernelCorrespondence
import ECRuntime.RLSAllDimensionPaperSharpCentered
import Mathlib

open Filter
namespace ECRuntime

/-! P02: direct coupon-process counterpart to the 2013 preprint's
Theorem 1. A rigorous interface uses the already-defined Boolean
coupon process and proves its exact kernel equality with the RLS chain.
The coupon types initially present are independently uniform Boolean
coordinates, exactly the uniform initial distribution in the formula. -/

/-- The random-stake coupon collector has the paper's sharp expected
number of additional sampling rounds, centered at its half-harmonic. -/
theorem proposed_randomStakeCoupon_paperTheorem1_sharpCentered :
    Tendsto
      (fun n : Nat => if hn : 0 < n then
        ((Finset.univ.sum (fun x : BitString n =>
           (runtimeSup (randomStakeCouponTransition hn)
              ({allOnes n} : Set (BitString n)) x).toReal)) / (2 : Real) ^ n) -
          (n : Real) * ((harmonicReal (n / 2) +
            harmonicReal ((n + 1) / 2)) / 2)
       else 0)
      atTop (nhds (-(1 / 2 : Real))) := by
  let f : (n : Nat) → BitString n → Real := fun _ => oneMaxReal
  have hf : ∀ n, CandidateCoordinateStrictMonotonicity (f n) := by
    intro n x i hi
    change (oneMax x : Real) < (oneMax (mutateWithMask x {i}) : Real)
    exact_mod_cast (oneMax_single_zero_flip_improves x i hi)
  have h := proposed_strictMonotoneRLS_allDimensionPaperSharpCentered f hf
  convert h using 1
  funext n
  split_ifs <;> rfl

end ECRuntime
