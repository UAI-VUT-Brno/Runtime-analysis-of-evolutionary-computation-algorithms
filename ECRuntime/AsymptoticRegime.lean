import Mathlib

open Filter
open Asymptotics

namespace ECRuntime

/-!
# Stage 29: asymptotic conventions for dimension-indexed EC quantities

The runtime-development stages before this file are finite-dimensional.  The tight
linear-function program that follows uses the standard Mathlib asymptotic relations on
sequences indexed by the problem dimension.  This module fixes one small repository-wide
convention: unless stated otherwise, asymptotics in `n : ℕ` are taken along
`Filter.atTop` and are real-valued.

The aliases below deliberately do not introduce a second asymptotic theory.  They expose
Mathlib's `IsBigO`, `IsLittleO`, `IsTheta`, and `IsEquivalent` with the filter parameter
fixed once, so later EC theorems can state their asymptotic content without repeating the
same filter plumbing.
-/

/-- Big-O for real sequences as the dimension tends to infinity. -/
abbrev NatIsBigO (f g : ℕ → ℝ) : Prop :=
  Asymptotics.IsBigO Filter.atTop f g

/-- Little-o for real sequences as the dimension tends to infinity. -/
abbrev NatIsLittleO (f g : ℕ → ℝ) : Prop :=
  Asymptotics.IsLittleO Filter.atTop f g

/-- Theta-equivalence for real sequences as the dimension tends to infinity. -/
abbrev NatIsTheta (f g : ℕ → ℝ) : Prop :=
  Asymptotics.IsTheta Filter.atTop f g

/-- Ratio-one asymptotic equivalence for real sequences as the dimension tends to infinity. -/
abbrev NatIsEquivalent (f g : ℕ → ℝ) : Prop :=
  Asymptotics.IsEquivalent Filter.atTop f g

/-- Canonical real linear growth sequence `n`. -/
noncomputable def natLinearGrowth (n : ℕ) : ℝ :=
  (n : ℝ)

/-- Canonical real quadratic growth sequence `n^2`. -/
noncomputable def natQuadraticGrowth (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2

/-- Canonical real `n log n` growth sequence used by tight linear-function runtime theorems. -/
noncomputable def natLinearLogGrowth (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ)

/-- Mathlib asymptotic equivalence implies the coarser Theta relation. -/
theorem natIsEquivalent_toTheta
    {f g : ℕ → ℝ} (h : NatIsEquivalent f g) :
    NatIsTheta f g := by
  exact Asymptotics.IsEquivalent.isTheta h

/-- Little-o implies Big-O under the Stage-29 dimension convention. -/
theorem natIsLittleO_toBigO
    {f g : ℕ → ℝ} (h : NatIsLittleO f g) :
    NatIsBigO f g := by
  exact Asymptotics.IsLittleO.isBigO h

/-- The Stage-29 Theta relation is symmetric. -/
theorem natIsTheta_symm
    {f g : ℕ → ℝ} (h : NatIsTheta f g) :
    NatIsTheta g f := by
  exact Asymptotics.IsTheta.symm h

/-- Big-O remains transitive after fixing the dimension filter. -/
theorem natIsBigO_trans
    {f g h : ℕ → ℝ} (hfg : NatIsBigO f g) (hgh : NatIsBigO g h) :
    NatIsBigO f h := by
  exact Asymptotics.IsBigO.trans hfg hgh

end ECRuntime
