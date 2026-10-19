import ECRuntime.GeometricSum
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace ECRuntime

/-- Finite sum of a family of extended nonnegative runtime coordinates. -/
noncomputable def finiteRuntimeSum
    {Ω : Type*} {m : ℕ} (W : Fin m → Ω → ENNReal) (ω : Ω) : ENNReal :=
  ∑ i : Fin m, W i ω

/-- Measurability of a finite runtime sum follows coordinatewise. -/
theorem measurable_finiteRuntimeSum
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    {W : Fin m → Ω → ENNReal}
    (hW : ∀ i, Measurable (W i)) :
    Measurable (finiteRuntimeSum W) := by
  unfold finiteRuntimeSum
  exact Finset.measurable_sum Finset.univ (by
    intro i _
    exact hW i)

/-- Pointwise coordinate domination is preserved by finite summation. -/
theorem finiteRuntimeSum_mono_of_pointwise_le
    {Ω : Type*} {m : ℕ}
    {W Z : Fin m → Ω → ENNReal}
    (hWZ : ∀ i ω, W i ω ≤ Z i ω) :
    ∀ ω, finiteRuntimeSum W ω ≤ finiteRuntimeSum Z ω := by
  intro ω
  unfold finiteRuntimeSum
  exact Finset.sum_le_sum (fun i _ => hWZ i ω)

/--
On a common probability space, coordinatewise pointwise domination implies
stochastic domination of the corresponding finite runtime sums.
-/
theorem stochasticallyDominated_finiteRuntimeSum_of_pointwise_le
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) {W Z : Fin m → Ω → ENNReal}
    (hWZ : ∀ i ω, W i ω ≤ Z i ω) :
    StochasticallyDominated
      μ (finiteRuntimeSum W)
      μ (finiteRuntimeSum Z) :=
  stochasticallyDominated_of_pointwise_le μ
    (finiteRuntimeSum_mono_of_pointwise_le hWZ)

/-- Natural-threshold version of finite-sum pointwise domination. -/
theorem natTailDominated_finiteRuntimeSum_of_pointwise_le
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) {W Z : Fin m → Ω → ENNReal}
    (hWZ : ∀ i ω, W i ω ≤ Z i ω) :
    NatTailDominated
      μ (finiteRuntimeSum W)
      μ (finiteRuntimeSum Z) :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_finiteRuntimeSum_of_pointwise_le μ hWZ)

/-- The verified geometric waiting-time total is the finite sum of its coordinates. -/
theorem finiteRuntimeSum_geometricWaitingCoordinate
    {m : ℕ} (ω : Fin m → ENNReal) :
    finiteRuntimeSum (fun i => geometricWaitingCoordinate i) ω =
      geometricWaitingSum ω := by
  rfl

/--
A coupled family of waiting times bounded coordinatewise by the canonical
geometric coordinates is stochastically dominated by their geometric sum.
This is the deterministic summation step used after a future coupling theorem.
-/
theorem stochasticallyDominated_by_geometricWaitingSum_of_pointwise_le
    {m : ℕ} (p : Fin m → unitInterval)
    (W : Fin m → (Fin m → ENNReal) → ENNReal)
    (hW : ∀ i ω, W i ω ≤ geometricWaitingCoordinate i ω) :
    StochasticallyDominated
      (geometricWaitingProductMeasure p)
      (finiteRuntimeSum W)
      (geometricWaitingProductMeasure p)
      geometricWaitingSum := by
  apply stochasticallyDominated_of_pointwise_le
  intro ω
  rw [← finiteRuntimeSum_geometricWaitingCoordinate ω]
  exact finiteRuntimeSum_mono_of_pointwise_le hW ω

/-- Natural-threshold form of the coupled geometric-sum domination theorem. -/
theorem natTailDominated_by_geometricWaitingSum_of_pointwise_le
    {m : ℕ} (p : Fin m → unitInterval)
    (W : Fin m → (Fin m → ENNReal) → ENNReal)
    (hW : ∀ i ω, W i ω ≤ geometricWaitingCoordinate i ω) :
    NatTailDominated
      (geometricWaitingProductMeasure p)
      (finiteRuntimeSum W)
      (geometricWaitingProductMeasure p)
      geometricWaitingSum :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_by_geometricWaitingSum_of_pointwise_le p W hW)

end ECRuntime
