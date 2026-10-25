import ECRuntime.LeadingOnesExpectedRuntimeAssembly
import ECRuntime.AdaptiveLeadingOnesTrajectoryRuntimeAssembly
import ECRuntime.LeadingOnesAdaptiveKernelCandidate
import ECRuntime.AdaptiveLeadingOnesUniformVisitProbability
import ECRuntime.AdaptiveLeadingOnesConditionalResidenceMean
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-! Stage 245 (historically frozen, reopened for user-requested consolidation).
The certified fixed-rate proof identifies the real sample-path
first-hitting-time expectation with the sum of expected occupation
charges. This candidate generalizes that *measure-level bridge* to a
fitness-dependent Markov kernel. The previously certified level-entry
law and conditional residence mean are inputs, not replacements, for
the missing occupation-time decomposition. The final theorem now uses the independent Stage 460 trajectory theorem.
This file remains nonpublic until all verification gates succeed. -/

/-- The genuine uniform-initialization mean hitting time of the adaptive
(1+1)-EA, defined from its infinite trajectory measure. -/
noncomputable def leadingOnesAdaptiveUniformFirstHittingTimeExpectation
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1) : ENNReal :=
  ((Fintype.card (BitString n) : ENNReal)⁻¹) *
    ∑ x : BitString n,
      ∫⁻ path : Nat → BitString n,
        transitionTrajectoryFirstHittingTime (leadingOnesTarget n) x path
      ∂transitionTrajectoryMeasure
        (leadingOnesAdaptiveTransition rate)
        (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x

/-- The trajectory integral defining the genuine adaptive expected hitting
 time agrees with the Bellman `runtimeSup` solution for the identical adaptive
 transition kernel. This isolates the remaining *occupation decomposition*
 (not measure identification) as the obstacle in the approved theorem below. -/
theorem leadingOnesAdaptiveUniformFirstHittingTimeExpectation_eq_runtimeSup_average
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1) :
    leadingOnesAdaptiveUniformFirstHittingTimeExpectation n rate hrate =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        ∑ x : BitString n,
          runtimeSup (leadingOnesAdaptiveTransition rate)
            (leadingOnesTarget n) x := by
  classical
  unfold leadingOnesAdaptiveUniformFirstHittingTimeExpectation
  apply congrArg
    (fun z : ENNReal => ((Fintype.card (BitString n) : ENNReal)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro x _hx
  exact transitionTrajectoryFirstHittingTime_lintegral_eq_runtimeSup
    (leadingOnesAdaptiveTransition rate) (leadingOnesTarget n)
    (proposed_leadingOnesAdaptive_transition_stochastic rate hrate) x

/-! **P01 occupation bridge frontier (proof-34).**
The adaptive entry law and local geometric residence mean yield a finite
nonnegative residence **surrogate** without using a stopping-time independence
assumption. The only remaining step is to identify this surrogate with the
actual pathwise expectation. This explicitly avoids conflating a completed
finite sum with the still-open occupation renewal identity. -/

/-- First-crossing mass times mean geometric residence, summed over the
nonterminal levels. The term is not *defined* as actual optimization time. -/
noncomputable def leadingOnesAdaptiveUniformResidenceContributionTotal
    (n : Nat) (rate : Nat → Real) : ENNReal :=
  ∑ i : Fin n,
    leadingOnesAdaptiveEventualFirstCrossingExactMass rate i *
      ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹)

/-- Fully algebraic assembly of the already certified adaptive exact-entry
probabilities. Its conclusion is about a residence *contribution*, not yet
the true sample-path hitting time. -/
theorem leadingOnesAdaptiveUniformResidenceContributionTotal_eq_halfSum
    (n : Nat) (rate : Nat → Real)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1) :
    leadingOnesAdaptiveUniformResidenceContributionTotal n rate =
      ENNReal.ofReal ((1 / 2 : Real) *
        ∑ i : Fin n, (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  unfold leadingOnesAdaptiveUniformResidenceContributionTotal
  calc
    (∑ i : Fin n,
        leadingOnesAdaptiveEventualFirstCrossingExactMass rate i *
          ENNReal.ofReal ((rate i.val * (1 - rate i.val) ^ i.val)⁻¹)) =
      ∑ i : Fin n,
        ENNReal.ofReal ((1 / 2 : Real) *
          (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [proposed_leadingOnesAdaptive_eventualExactEntry_half rate hinterior i]
      -- The certified adaptive visit lemma uses ENNReal's `1 / 2`,
      -- whereas `ENNReal_ofReal_half` is written with `2⁻¹`.
      -- Normalize the coefficient explicitly before applying ofReal_mul.
      have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : Real) := by
        simpa only [one_div] using ENNReal_ofReal_half.symm
      rw [hhalf]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 1 / 2)]
    _ = ENNReal.ofReal
          (∑ i : Fin n, (1 / 2 : Real) *
            (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i _hi
      have hpi := hinterior i.val (Nat.le_of_lt i.isLt)
      have hbase : 0 ≤ rate i.val * (1 - rate i.val) ^ i.val :=
        mul_nonneg hpi.1.le (pow_nonneg (by linarith [hpi.2]) _)
      exact mul_nonneg (by norm_num) (inv_nonneg.mpr hbase)
    _ = ENNReal.ofReal ((1 / 2 : Real) *
          ∑ i : Fin n, (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
      rw [Finset.mul_sum]

/-- The exact remaining obligation for P01: a genuine pathwise occupation
bridge. Supplying this bridge makes the approved runtime formula immediate.
Unlike the Stage-245 main theorem, this implication contains no admission. -/
theorem leadingOnesAdaptiveUniformRuntime_eq_halfSum_of_occupationBridge
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (hoccupation :
      leadingOnesAdaptiveUniformFirstHittingTimeExpectation n rate hrate =
        leadingOnesAdaptiveUniformResidenceContributionTotal n rate) :
    leadingOnesAdaptiveUniformFirstHittingTimeExpectation n rate hrate =
      ENNReal.ofReal ((1 / 2 : Real) *
        ∑ i : Fin n, (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  exact hoccupation.trans
    (leadingOnesAdaptiveUniformResidenceContributionTotal_eq_halfSum
      n rate hinterior)

/-- Exact adaptive total runtime formula. This is the crucial missing
bridge from first-crossing and conditional residence to actual global
expected optimization time. The frozen approved mathematical statement is unchanged. -/
theorem proposed_leadingOnesAdaptive_uniformRuntime_eq_levelSum
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (rate : Nat → Real)
    (hrate : ∀ j : Nat, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1) :
    leadingOnesAdaptiveUniformFirstHittingTimeExpectation n rate hrate =
      ENNReal.ofReal ((1 / 2 : Real) *
        ∑ i : Fin n, (rate i.val * (1 - rate i.val) ^ i.val)⁻¹) := by
  classical
  -- Stage 460 separately certifies the genuine trajectory/Bellman bridge.
  -- This is the same statement, with its historical named expectation unfolded.
  simpa only [leadingOnesAdaptiveUniformFirstHittingTimeExpectation] using
    (proposed_leadingOnesAdaptive_uniformTrajectoryRuntime_eq_halfSum
      n rate hrate hinterior)

end ECRuntime
