import ECRuntime.FiniteSumDomination
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace ECRuntime

/-!
# Product-coupling bridge for stochastic domination

The actual adaptive coupling constructed in Stage 26 is supported on pairs
`(actual trajectory, comparison variables)` satisfying the desired runtime order.
There is no reason for that order to hold on arbitrary *off-support* pairs in the
ambient product type.  Consequently the reusable coupling interface should require
an almost-everywhere order under the coupling measure, not a global pointwise order
on the complete Cartesian product.

Stage 26 fix 24 adds the almost-everywhere versions as the primary interface and keeps
all earlier pointwise theorems as convenience wrappers.  This is mathematically the
right boundary for the upcoming sequential construction: support properties of the
finite split rows will yield the coordinate inequalities `κ`-almost everywhere,
while the two marginal equalities remain exact.
-/

/-- An almost-everywhere ordered coupling with the prescribed marginals proves
stochastic domination. -/
theorem stochasticallyDominated_of_product_coupling_ae
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂)
    (X : Ω₁ → ENNReal) (Y : Ω₂ → ENNReal)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : Measure (Ω₁ × Ω₂))
    (hfst : Measure.map (Prod.fst : Ω₁ × Ω₂ → Ω₁) κ = μ)
    (hsnd : Measure.map (Prod.snd : Ω₁ × Ω₂ → Ω₂) κ = ν)
    (hle : ∀ᵐ z ∂κ, X z.1 ≤ Y z.2) :
    StochasticallyDominated μ X ν Y := by
  intro t
  unfold runtimeTailMass runtimeTailEvent
  change μ (X ⁻¹' Set.Ioi t) ≤ ν (Y ⁻¹' Set.Ioi t)
  have hXt : MeasurableSet (X ⁻¹' Set.Ioi t) :=
    measurableSet_Ioi.preimage hX
  have hYt : MeasurableSet (Y ⁻¹' Set.Ioi t) :=
    measurableSet_Ioi.preimage hY
  rw [← hfst, ← hsnd]
  rw [Measure.map_apply measurable_fst hXt,
      Measure.map_apply measurable_snd hYt]
  refine measure_mono_ae (hle.mono ?_)
  intro z hz htail
  change t < X z.1 at htail
  change t < Y z.2
  exact lt_of_lt_of_le htail hz

/-- Pointwise ordered couplings are a special case of the almost-everywhere bridge. -/
theorem stochasticallyDominated_of_product_coupling
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂)
    (X : Ω₁ → ENNReal) (Y : Ω₂ → ENNReal)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : Measure (Ω₁ × Ω₂))
    (hfst : Measure.map (Prod.fst : Ω₁ × Ω₂ → Ω₁) κ = μ)
    (hsnd : Measure.map (Prod.snd : Ω₁ × Ω₂ → Ω₂) κ = ν)
    (hle : ∀ z : Ω₁ × Ω₂, X z.1 ≤ Y z.2) :
    StochasticallyDominated μ X ν Y := by
  apply stochasticallyDominated_of_product_coupling_ae
    (μ := μ) (ν := ν) (X := X) (Y := Y)
    (hX := hX) (hY := hY) (κ := κ)
    (hfst := hfst) (hsnd := hsnd)
  exact Filter.Eventually.of_forall hle

/-- Natural-threshold form of the almost-everywhere product-coupling theorem. -/
theorem natTailDominated_of_product_coupling_ae
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂)
    (X : Ω₁ → ENNReal) (Y : Ω₂ → ENNReal)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : Measure (Ω₁ × Ω₂))
    (hfst : Measure.map (Prod.fst : Ω₁ × Ω₂ → Ω₁) κ = μ)
    (hsnd : Measure.map (Prod.snd : Ω₁ × Ω₂ → Ω₂) κ = ν)
    (hle : ∀ᵐ z ∂κ, X z.1 ≤ Y z.2) :
    NatTailDominated μ X ν Y :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_of_product_coupling_ae
      (μ := μ) (ν := ν) (X := X) (Y := Y)
      (hX := hX) (hY := hY) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hle := hle))

/-- Natural-threshold pointwise compatibility wrapper. -/
theorem natTailDominated_of_product_coupling
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ : Measure Ω₁) (ν : Measure Ω₂)
    (X : Ω₁ → ENNReal) (Y : Ω₂ → ENNReal)
    (hX : Measurable X) (hY : Measurable Y)
    (κ : Measure (Ω₁ × Ω₂))
    (hfst : Measure.map (Prod.fst : Ω₁ × Ω₂ → Ω₁) κ = μ)
    (hsnd : Measure.map (Prod.snd : Ω₁ × Ω₂ → Ω₂) κ = ν)
    (hle : ∀ z : Ω₁ × Ω₂, X z.1 ≤ Y z.2) :
    NatTailDominated μ X ν Y :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_of_product_coupling
      (μ := μ) (ν := ν) (X := X) (Y := Y)
      (hX := hX) (hY := hY) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hle := hle))

/-- Almost-everywhere specialization of the coupling bridge to the canonical
independent geometric product law. -/
theorem stochasticallyDominated_by_geometricWaitingSum_of_coupling_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hle : ∀ᵐ z ∂κ, X z.1 ≤ geometricWaitingSum z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum := by
  exact stochasticallyDominated_of_product_coupling_ae
    (μ := μ) (ν := geometricWaitingProductMeasure p)
    (X := X) (Y := geometricWaitingSum)
    (hX := hX) (hY := measurable_geometricWaitingSum)
    (κ := κ) (hfst := hfst) (hsnd := hsnd) (hle := hle)

/-- Pointwise compatibility wrapper for the geometric-sum coupling theorem. -/
theorem stochasticallyDominated_by_geometricWaitingSum_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hle : ∀ z : Ω × (Fin m → ENNReal),
      X z.1 ≤ geometricWaitingSum z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum := by
  apply stochasticallyDominated_by_geometricWaitingSum_of_coupling_ae
    (μ := μ) (X := X) (hX := hX) (p := p) (κ := κ)
    (hfst := hfst) (hsnd := hsnd)
  exact Filter.Eventually.of_forall hle

/-- Natural-threshold almost-everywhere form of the geometric-sum coupling theorem. -/
theorem natTailDominated_by_geometricWaitingSum_of_coupling_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hle : ∀ᵐ z ∂κ, X z.1 ≤ geometricWaitingSum z.2) :
    NatTailDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_by_geometricWaitingSum_of_coupling_ae
      (μ := μ) (X := X) (hX := hX) (p := p) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hle := hle))

/-- Natural-threshold pointwise compatibility wrapper. -/
theorem natTailDominated_by_geometricWaitingSum_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hle : ∀ z : Ω × (Fin m → ENNReal),
      X z.1 ≤ geometricWaitingSum z.2) :
    NatTailDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_by_geometricWaitingSum_of_coupling
      (μ := μ) (X := X) (hX := hX) (p := p) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hle := hle))

/-- Almost-everywhere coordinatewise version of the geometric coupling bridge.
This is the primary interface for the adaptive fitness-level construction: the
coupling only needs to put full mass on pairs satisfying the coordinate bounds. -/
theorem stochasticallyDominated_by_geometricWaitingSum_of_coordinate_coupling_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (W : Fin m → Ω → ENNReal)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hXW : ∀ ω, X ω ≤ finiteRuntimeSum W ω)
    (hW : ∀ᵐ z ∂κ, ∀ i,
      W i z.1 ≤ geometricWaitingCoordinate i z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum := by
  apply stochasticallyDominated_by_geometricWaitingSum_of_coupling_ae
    (μ := μ) (X := X) (hX := hX) (p := p) (κ := κ)
    (hfst := hfst) (hsnd := hsnd)
  exact hW.mono (fun z hz => by
    calc
      X z.1 ≤ finiteRuntimeSum W z.1 := hXW z.1
      _ ≤ geometricWaitingSum z.2 := by
        unfold finiteRuntimeSum geometricWaitingSum
        exact Finset.sum_le_sum (fun i _ => hz i))

/-- Pointwise coordinatewise compatibility wrapper. -/
theorem stochasticallyDominated_by_geometricWaitingSum_of_coordinate_coupling
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (W : Fin m → Ω → ENNReal)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hXW : ∀ ω, X ω ≤ finiteRuntimeSum W ω)
    (hW : ∀ i (z : Ω × (Fin m → ENNReal)),
      W i z.1 ≤ geometricWaitingCoordinate i z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum := by
  apply stochasticallyDominated_by_geometricWaitingSum_of_coordinate_coupling_ae
    (μ := μ) (X := X) (hX := hX) (p := p) (W := W) (κ := κ)
    (hfst := hfst) (hsnd := hsnd) (hXW := hXW)
  exact Filter.Eventually.of_forall (fun z i => hW i z)

/-- Natural-threshold almost-everywhere coordinatewise bridge. -/
theorem natTailDominated_by_geometricWaitingSum_of_coordinate_coupling_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (W : Fin m → Ω → ENNReal)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hXW : ∀ ω, X ω ≤ finiteRuntimeSum W ω)
    (hW : ∀ᵐ z ∂κ, ∀ i,
      W i z.1 ≤ geometricWaitingCoordinate i z.2) :
    NatTailDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_by_geometricWaitingSum_of_coordinate_coupling_ae
      (μ := μ) (X := X) (hX := hX) (p := p) (W := W) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hXW := hXW) (hW := hW))

/-- Natural-threshold pointwise coordinatewise compatibility wrapper. -/
theorem natTailDominated_by_geometricWaitingSum_of_coordinate_coupling
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (W : Fin m → Ω → ENNReal)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hXW : ∀ ω, X ω ≤ finiteRuntimeSum W ω)
    (hW : ∀ i (z : Ω × (Fin m → ENNReal)),
      W i z.1 ≤ geometricWaitingCoordinate i z.2) :
    NatTailDominated
      μ X
      (geometricWaitingProductMeasure p) geometricWaitingSum :=
  natTailDominated_of_stochasticallyDominated
    (stochasticallyDominated_by_geometricWaitingSum_of_coordinate_coupling
      (μ := μ) (X := X) (hX := hX) (p := p) (W := W) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hXW := hXW) (hW := hW))

/-- Almost-everywhere public pushed-forward geometric-sum comparison. -/
theorem stochasticallyDominated_by_geometricWaitingSumMeasure_of_coupling_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hle : ∀ᵐ z ∂κ, X z.1 ≤ geometricWaitingSum z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingSumMeasure p) id := by
  have hdom :=
    stochasticallyDominated_by_geometricWaitingSum_of_coupling_ae
      (μ := μ) (X := X) (hX := hX) (p := p) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hle := hle)
  intro t
  calc
    runtimeTailMass μ X t ≤
        runtimeTailMass
          (geometricWaitingProductMeasure p) geometricWaitingSum t := hdom t
    _ = runtimeTailMass (geometricWaitingSumMeasure p) id t :=
      (geometricWaitingSumMeasure_runtimeTailMass p t).symm

/-- Pointwise compatibility wrapper for the public pushed-forward comparison. -/
theorem stochasticallyDominated_by_geometricWaitingSumMeasure_of_coupling
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hle : ∀ z : Ω × (Fin m → ENNReal),
      X z.1 ≤ geometricWaitingSum z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingSumMeasure p) id := by
  apply stochasticallyDominated_by_geometricWaitingSumMeasure_of_coupling_ae
    (μ := μ) (X := X) (hX := hX) (p := p) (κ := κ)
    (hfst := hfst) (hsnd := hsnd)
  exact Filter.Eventually.of_forall hle

/-- Almost-everywhere coordinatewise public form.  This is the final bridge expected
to be called by the sequential adaptive coupling construction. -/
theorem stochasticallyDominated_by_geometricWaitingSumMeasure_of_coordinate_coupling_ae
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (W : Fin m → Ω → ENNReal)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hXW : ∀ ω, X ω ≤ finiteRuntimeSum W ω)
    (hW : ∀ᵐ z ∂κ, ∀ i,
      W i z.1 ≤ geometricWaitingCoordinate i z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingSumMeasure p) id := by
  have hdom :=
    stochasticallyDominated_by_geometricWaitingSum_of_coordinate_coupling_ae
      (μ := μ) (X := X) (hX := hX) (p := p) (W := W) (κ := κ)
      (hfst := hfst) (hsnd := hsnd) (hXW := hXW) (hW := hW)
  intro t
  calc
    runtimeTailMass μ X t ≤
        runtimeTailMass
          (geometricWaitingProductMeasure p) geometricWaitingSum t := hdom t
    _ = runtimeTailMass (geometricWaitingSumMeasure p) id t :=
      (geometricWaitingSumMeasure_runtimeTailMass p t).symm

/-- Pointwise coordinatewise public compatibility wrapper. -/
theorem stochasticallyDominated_by_geometricWaitingSumMeasure_of_coordinate_coupling
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure Ω) (X : Ω → ENNReal) (hX : Measurable X)
    (p : Fin m → unitInterval)
    (W : Fin m → Ω → ENNReal)
    (κ : Measure (Ω × (Fin m → ENNReal)))
    (hfst : Measure.map
      (Prod.fst : Ω × (Fin m → ENNReal) → Ω) κ = μ)
    (hsnd : Measure.map
      (Prod.snd : Ω × (Fin m → ENNReal) → (Fin m → ENNReal)) κ =
        geometricWaitingProductMeasure p)
    (hXW : ∀ ω, X ω ≤ finiteRuntimeSum W ω)
    (hW : ∀ i (z : Ω × (Fin m → ENNReal)),
      W i z.1 ≤ geometricWaitingCoordinate i z.2) :
    StochasticallyDominated
      μ X
      (geometricWaitingSumMeasure p) id := by
  apply stochasticallyDominated_by_geometricWaitingSumMeasure_of_coordinate_coupling_ae
    (μ := μ) (X := X) (hX := hX) (p := p) (W := W) (κ := κ)
    (hfst := hfst) (hsnd := hsnd) (hXW := hXW)
  exact Filter.Eventually.of_forall (fun z i => hW i z)

end ECRuntime
