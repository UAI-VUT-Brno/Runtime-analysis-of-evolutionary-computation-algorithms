import ECRuntime.LeadingOnesBoundaryEventualCrossing
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesBoundaryProgressPositive
import ECRuntime.FinitePositiveLowerEnvelope
import ECRuntime.FitnessLevel
import ECRuntime.UnrestrictedRuntime
import Mathlib

namespace ECRuntime

/-!
Stage 229 (NEW, pending approval and open proof): the substantial
adaptive finite expected-runtime statement. The intended proof combines
Stage 227 positive mask-progress, Stage 228 finite uniformization,
and the generic harmonic fitness-level/Bellman supersolution results.
The statement is NOT treated as a proved premise for Stage 225.
-/

/-- A strictly interior adaptive schedule gives a finite unrestricted
expected time to any fixed nonterminal LeadingOnes boundary. -/
theorem proposed_leadingOnesAdaptive_boundaryRuntime_ne_top
    {n : Nat} (rate : Nat -> Real)
    (hrate : ∀ j : Nat, j <= n -> 0 < rate j ∧ rate j < 1)
    (i : Fin n) (x : BitString n) :
    runtimeSup (leadingOnesAdaptiveTransition rate)
      (potentialTarget (leadingOnesBoundaryPotential i)) x ≠ ⊤ := by
  classical
  let V : BitString n → Nat := leadingOnesBoundaryPotential i
  let step : BitString n → MutationMask n → BitString n :=
    selectedAfterMask (leadingOnesReal (n := n))
  let w : BitString n → MutationMask n → Real :=
    fun y mask => mutationMaskWeight (rate (leadingOnes y)) mask
  let mass : BitString n → Real := fun y =>
    finiteEventMass (w y) (fun mask => V (step y mask) < V y)
  let positiveMass : BitString n → Real := fun y =>
    if 0 < V y then mass y else 1
  have hpos : ∀ y : BitString n, 0 < positiveMass y := by
    intro y
    by_cases hy : 0 < V y
    · simp only [positiveMass, if_pos hy]
      exact proposed_leadingOnesAdaptive_boundaryMaskProgress_pos
        rate hrate i y (by simpa only [V] using hy)
    · simp [positiveMass, hy]
  obtain ⟨delta, hdelta, hfloor⟩ :=
    proposed_finite_positive_uniform_lower positiveMass hpos
  let c : Real := delta / ((i.val + 1 : Nat) : Real)
  have hden : 0 < ((i.val + 1 : Nat) : Real) := by positivity
  have hc : 0 < c := div_pos hdelta hden
  have hw : ∀ y mask, 0 ≤ w y mask := by
    intro y mask
    have hr := hrate (leadingOnes y) (leadingOnes_le y)
    exact mutationMaskWeight_nonneg hr.1.le hr.2.le mask
  have hsum : ∀ y, ∑ mask : MutationMask n, w y mask = 1 := by
    intro y
    exact mutationMaskWeight_sum n (rate (leadingOnes y))
  have hmono : ∀ y mask, V (step y mask) ≤ V y := by
    intro y mask
    exact leadingOnesBoundaryPotential_selectedAfterMask_le i y mask
  have hprogress : ∀ y, 0 < V y →
      (V y : Real) * c ≤
        finiteEventMass (w y) (fun mask => V (step y mask) < V y) := by
    intro y hy
    have hbound : delta ≤ mass y := by
      have hle := hfloor y
      simpa only [positiveMass, if_pos hy] using hle
    have hV : V y ≤ i.val + 1 := by
      dsimp [V, leadingOnesBoundaryPotential]
      omega
    have hVcast : (V y : Real) ≤ ((i.val + 1 : Nat) : Real) := by
      exact_mod_cast hV
    have hfrac : (V y : Real) / ((i.val + 1 : Nat) : Real) ≤ 1 :=
      (div_le_one hden).2 hVcast
    have hscaled : (V y : Real) * c ≤ delta := by
      calc
        (V y : Real) * c =
            delta * ((V y : Real) / ((i.val + 1 : Nat) : Real)) := by
          dsimp [c]
          ring
        _ ≤ delta * 1 := mul_le_mul_of_nonneg_left hfrac hdelta.le
        _ = delta := by ring
    exact hscaled.trans hbound
  have hgeneric := harmonicFitnessLevel_finiteHorizonBound
    (w := w) (step := step) (V := V) (rate := c)
    hc hw hsum hmono hprogress
  have htransition :
      finiteRandomTransition w step = leadingOnesAdaptiveTransition rate := by
    funext y z
    rfl
  have hB : HasUniformFiniteHorizonRuntimeBound
      (leadingOnesAdaptiveTransition rate)
      (potentialTarget V) (harmonicLevelRuntime c V) := by
    rw [← htransition]
    exact hgeneric
  have hbound := runtimeSup_le_of_uniform_bound
    (leadingOnesAdaptiveTransition rate) (potentialTarget V)
    (harmonicLevelRuntime c V) hB x
  exact ne_top_of_le_ne_top (by simp) hbound

end ECRuntime
