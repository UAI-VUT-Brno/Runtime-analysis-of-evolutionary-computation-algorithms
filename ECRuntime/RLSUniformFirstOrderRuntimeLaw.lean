import ECRuntime.RLSUniformInitialFirstOrderFiniteSandwich
import Mathlib

open Filter

namespace ECRuntime

/-!
Stage 156 — USER-APPROVED, PROVISIONAL PUBLIC MODULE.
Source direction: Doerr--Doerr (2013), random-initial-stake coupon collecting.
The Stage 151 finite sandwich implies the first-order expected runtime
for ANY dimension-dependent family of strictly positive linear weights.
No constant-weight/OneMax restriction and no second-order log-two input
are needed. Dimensions 0 and 1 are assigned the harmless value 1 to
avoid division by log(1) and the zero-dimensional one-bit law.
-/

/-- Dimension-uniform first-order normalized expected RLS runtime,
with a conventional value at the exceptional dimensions n < 2. -/
noncomputable def stage156_normalizedRuntime
    (w : (n : Nat) → Fin n → Real) (n : Nat) : Real :=
  if hn : 2 ≤ n then
    ((Finset.univ.sum (fun x : BitString n =>
      (runtimeSup
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw
          (by omega : 0 < n)).transition (linearFitness (w n)))
        ({allOnes n} : Set (BitString n)) x).toReal)) /
      (2 : Real) ^ n) /
      ((n : Real) * Real.log (n : Real))
  else 1

/-- Uniform first-order n log n runtime law for positive linear fitness,
including weight vectors that vary with the problem dimension. -/
theorem proposed_rlsLinear_uniformInitial_firstOrder_runtime
    (w : (n : Nat) → Fin n → Real)
    (hw : ∀ n : Nat, PositiveLinearWeights (w n)) :
    Tendsto (fun n : Nat => stage156_normalizedRuntime w n)
      atTop (nhds (1 : Real)) := by
  have hlog : Tendsto (fun n : Nat => Real.log (n : Real))
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => (1 : Real) / Real.log (n : Real))
      atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog)
  let upper : Nat → Real := fun n =>
    if 2 ≤ n then (1 : Real) / Real.log (n : Real) else 0
  have hu : Tendsto upper atTop (nhds (0 : Real)) := by
    apply hinv.congr'
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with n hn
    simp [upper, hn]
  have hpoint (n : Nat) :
      -(upper n) ≤ stage156_normalizedRuntime w n - 1 ∧
        stage156_normalizedRuntime w n - 1 ≤ upper n := by
    by_cases hn : 2 ≤ n
    · have h := proposed_rlsLinear_uniformInitial_firstOrderFiniteSandwich
        hn (w n) (hw n)
      dsimp [stage156_normalizedRuntime, upper]
      simp only [dif_pos hn, if_pos hn]
      constructor <;> linarith [h.1, h.2]
    · simp [stage156_normalizedRuntime, upper, hn]
  -- Specify both envelope functions BEFORE applying squeeze_zero.
  -- A bare `linarith` cannot instantiate the implicit lower-bound
  -- metavariable introduced by that tactic (Round 35 diagnostics).
  have hlower (n : Nat) :
      0 ≤ stage156_normalizedRuntime w n - 1 + upper n := by
    linarith [(hpoint n).1]
  have hupper (n : Nat) :
      stage156_normalizedRuntime w n - 1 + upper n ≤
        (2 : Real) * upper n := by
    linarith [(hpoint n).2]
  have hdouble : Tendsto (fun n : Nat => (2 : Real) * upper n)
      atTop (nhds (0 : Real)) := by
    simpa using (tendsto_const_nhds.mul hu :
      Tendsto (fun n : Nat => (2 : Real) * upper n) atTop
        (nhds ((2 : Real) * 0)))
  have hshift : Tendsto
      (fun n : Nat => stage156_normalizedRuntime w n - 1 + upper n)
      atTop (nhds (0 : Real)) := by
    apply squeeze_zero
    · intro n
      exact hlower n
    · intro n
      exact hupper n
    · exact hdouble
  have hdiff : Tendsto
      (fun n : Nat => stage156_normalizedRuntime w n - 1)
      atTop (nhds (0 : Real)) := by
    have hh := hshift.sub hu
    convert hh using 1
    · funext n
      ring
    · ring_nf
  have heq :
      (fun n : Nat => (1 : Real) + (stage156_normalizedRuntime w n - 1)) =
      (fun n : Nat => stage156_normalizedRuntime w n) := by
    funext n
    ring
  rw [← heq]
  simpa only [add_zero] using tendsto_const_nhds.add hdiff

end ECRuntime
