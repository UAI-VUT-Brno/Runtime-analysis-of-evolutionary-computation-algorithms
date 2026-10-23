import ECRuntime.BellmanGeometricExactRuntime
import ECRuntime.FiniteRuntimeSurvivalSupport
import Mathlib

open Filter

namespace ECRuntime

/-!
Stage 127, approved theorem, provisional public integration.

The finite-horizon Bellman identity, nonnegative and bounded residuals,
and runtime lower approximation live in `BellmanFiniteResidualSupport`.
They were compiler-accepted in Round 13 and are now shared with Stage 131.
The general finite-mean vanishing-residual step is still open. The
approved Stage 131 instead proves the geometrically decaying special case,
which suffices for the exact coupon-collector specialization if its proof
candidate compiles. General finite-mean convergence should be developed
separately rather than silently strengthened to a uniform geometric claim.
-/

/-- The generic residual argument needs only survival convergence;
no geometric estimate is required for this conditional lemma. The missing
finite-mean-to-survival implication is isolated below, not assumed silently. -/
private theorem stage127_exact_of_vanishing_survival
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P)
    (R : alpha → Real)
    (hRnonneg : ∀ y, 0 ≤ R y)
    (hRzero : ∀ y, y ∈ target → R y = 0)
    (hRbellman : ∀ y, y ∉ target → R y = 1 + expectedValueAfter P R y)
    (hsurvival : ∀ y,
      Tendsto (fun t : Nat => finiteLevelSurvival P targetᶜ t y)
        atTop (nhds (0 : Real)))
    (x : alpha) :
    runtimeSup P target x = ENNReal.ofReal (R x) := by
  classical
  have hupper := stage127_bellman_gives_runtime_upperBound
    P target hP R hRnonneg hRzero hRbellman x
  letI : Nonempty alpha := ⟨x⟩
  let B : Real := Finset.univ.sup' (Finset.univ_nonempty :
      (Finset.univ : Finset alpha).Nonempty) R
  have hB : ∀ y : alpha, R y ≤ B := by
    intro y
    exact Finset.le_sup' R (Finset.mem_univ y)
  have hprod : Tendsto
      (fun t : Nat => B * finiteLevelSurvival P targetᶜ t x)
      atTop (nhds (0 : Real)) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul (hsurvival x))
  have hlimit : Tendsto
      (fun t : Nat => ENNReal.ofReal
        (R x - B * finiteLevelSurvival P targetᶜ t x))
      atTop (nhds (ENNReal.ofReal (R x))) := by
    have hreal : Tendsto
        (fun t : Nat => R x - B * finiteLevelSurvival P targetᶜ t x)
        atTop (nhds (R x)) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hprod)
    exact ENNReal.tendsto_ofReal hreal
  have hlower : ENNReal.ofReal (R x) ≤ runtimeSup P target x := by
    apply le_of_tendsto hlimit
    exact Filter.Eventually.of_forall (fun t =>
      stage127_runtimeSup_lowerApprox P target hP R hRzero hRbellman
        B hB t x)
  exact le_antisymm hupper hlower

/-- In a finite stochastic process with finite first-hitting expectation,
a nonnegative real Bellman solution that vanishes on the target equals
the unrestricted expected first-hitting runtime. -/
theorem proposed_exactRuntime_of_bellmanAndFiniteHitting
    {alpha : Type*} [Fintype alpha]
    (P : TransitionMatrix alpha) (target : Set alpha)
    [DecidablePred (fun x => x ∈ target)]
    (hP : IsStochastic P)
    (R : alpha → Real)
    (hRnonneg : ∀ x, 0 ≤ R x)
    (hRzero : ∀ x, x ∈ target → R x = 0)
    (hRbellman : ∀ x, x ∉ target → R x = 1 + expectedValueAfter P R x)
    (hFinite : ∀ x, runtimeSup P target x ≠ ⊤)
    (x : alpha) :
    runtimeSup P target x = ENNReal.ofReal (R x) := by
  exact stage127_exact_of_vanishing_survival P target hP R
    hRnonneg hRzero hRbellman
    (fun y => candidate_finiteSurvival_tendsto_zero_of_finite_runtime
      P target hP hFinite y) x

end ECRuntime
