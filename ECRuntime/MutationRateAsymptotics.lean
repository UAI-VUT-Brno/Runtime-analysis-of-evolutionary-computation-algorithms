import ECRuntime.AsymptoticRegime
import ECRuntime.MutationRateRegime
import Mathlib

open Filter
open Asymptotics

namespace ECRuntime

/-!
# Stage 29: asymptotics of the `p = c/n` mutation-rate regime

Stage 28 introduced `scaledMutationRate c n` and its finite-dimensional admissibility
facts.  The tight linear-function stages need the corresponding dimension-asymptotic
interface.  This module records only the reusable rate facts:

* the zero-safe scaled rate is globally `c` times the canonical standard rate;
* every fixed `c/n` rate tends to zero;
* `c/n = o(1)`;
* `c/n = O(1/n)` for every fixed `c`;
* for nonzero `c`, `c/n = Θ(1/n)`.

No runtime estimate is introduced here.  The purpose is to make the mutation-rate
normalization used by the Stage 30--32 Witt formalization explicit and stable.
-/

/-- The positive-dimension identity from Stage 28 extends through the common zero convention. -/
theorem scaledMutationRate_eq_mul_standardMutationRate_all
    (c : ℝ) (n : ℕ) :
    scaledMutationRate c n = c * standardMutationRate n := by
  by_cases hn : n = 0
  · subst n
    simp [scaledMutationRate, standardMutationRate]
  · exact scaledMutationRate_eq_mul_standardMutationRate (Nat.pos_of_ne_zero hn)

/-- Every fixed scaled mutation rate tends to zero as the dimension tends to infinity. -/
theorem scaledMutationRate_tendsto_zero (c : ℝ) :
    Filter.Tendsto (fun n : ℕ => scaledMutationRate c n)
      Filter.atTop (nhds 0) := by
  have hdiv :
      Filter.Tendsto (fun n : ℕ => c / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  apply hdiv.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  exact (scaledMutationRate_eq_div_of_pos hn).symm

/-- In particular the repository-wide standard rate tends to zero. -/
theorem standardMutationRate_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => standardMutationRate n)
      Filter.atTop (nhds 0) := by
  have h := scaledMutationRate_tendsto_zero (1 : ℝ)
  apply h.congr'
  exact Filter.Eventually.of_forall scaledMutationRate_one_eq_standardMutationRate

/-- Every fixed `c/n` rate is little-o of the constant sequence one. -/
theorem scaledMutationRate_isLittleO_one (c : ℝ) :
    NatIsLittleO
      (fun n : ℕ => scaledMutationRate c n)
      (fun _ : ℕ => (1 : ℝ)) := by
  have hzero :
      ∀ n : ℕ, (1 : ℝ) = 0 → scaledMutationRate c n = 0 := by
    intro n h
    norm_num at h
  exact (Asymptotics.isLittleO_iff_tendsto hzero).2 (by
    simpa using scaledMutationRate_tendsto_zero c)

/-- A fixed scaled rate is always Big-O of the canonical `1/n` standard rate. -/
theorem scaledMutationRate_isBigO_standardMutationRate (c : ℝ) :
    NatIsBigO
      (fun n : ℕ => scaledMutationRate c n)
      (fun n : ℕ => standardMutationRate n) := by
  have hbase :=
    Asymptotics.isBigO_const_mul_self c
      (fun n : ℕ => standardMutationRate n) Filter.atTop
  have hfun :
      (fun n : ℕ => scaledMutationRate c n) =
        (fun n : ℕ => c * standardMutationRate n) := by
    funext n
    exact scaledMutationRate_eq_mul_standardMutationRate_all c n
  rw [hfun]
  exact hbase

/-- For nonzero fixed scale, `c/n` and `1/n` have exactly the same Theta order. -/
theorem scaledMutationRate_isTheta_standardMutationRate
    {c : ℝ} (hc : c ≠ 0) :
    NatIsTheta
      (fun n : ℕ => scaledMutationRate c n)
      (fun n : ℕ => standardMutationRate n) := by
  constructor
  · exact scaledMutationRate_isBigO_standardMutationRate c
  · have hbase :=
      Asymptotics.isBigO_self_const_mul hc
        (fun n : ℕ => standardMutationRate n) Filter.atTop
    have hfun :
        (fun n : ℕ => scaledMutationRate c n) =
          (fun n : ℕ => c * standardMutationRate n) := by
      funext n
      exact scaledMutationRate_eq_mul_standardMutationRate_all c n
    rw [← hfun] at hbase
    exact hbase

end ECRuntime
