import ECRuntime.RLSUniformInitialRuntimeSecondOrder

open Filter
namespace ECRuntimeTest
open ECRuntime

/-- Regress the exact runtime theorem, including its piecewise n=0 case. -/
private theorem stage141_runtime_secondOrder :
    Tendsto
      (fun n : Nat =>
        if hn : 0 < n then
          ((Finset.univ.sum (fun x : BitString n =>
            (runtimeSup
              ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
                (linearFitness (fun _ : Fin n => (1 : Real))))
              ({allOnes n} : Set (BitString n)) x).toReal) /
              (2 : Real) ^ n)) / (n : Real) - harmonicReal n
        else 0)
      atTop (nhds (- Real.log 2)) := by
  exact proposed_rlsLinear_uniformStart_runtime_secondOrder

end ECRuntimeTest
