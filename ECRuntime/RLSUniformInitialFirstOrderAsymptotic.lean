import ECRuntime.BinomialHarmonicAverageClosedForm
import ECRuntime.RLSRandomStart
import ECRuntime.HarmonicLogLower
import ECRuntime.RLSUniformInitialCorrectionEnvelope
import Mathlib

open Filter

namespace ECRuntime

/-!
Stage 137 — USER-APPROVED statement; proof development.
Doerr--Doerr (2013), collecting coupons with random initial stake.
This names the first-order asymptotic of the certified finite binomial
harmonic average, without claiming the paper's sharper second-order term.
The exact finite binomial-harmonic identity is promoted as Stage 138.
The harmonic/log limit and headline theorem compiled without diagnostics in
the user-run Round 32 standalone candidate check. Full public gate pending.
The denominator is zero for small n, which is harmless in an atTop limit.
-/

/-- Every term in the binomial-harmonic average is nonnegative. -/
private theorem stage137_binomial_harmonic_sum_nonneg (n : Nat) :
    0 ≤ (Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) * harmonicReal k) := by
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (Nat.cast_nonneg _) (harmonicReal_nonneg k)

/-- The finite weighted harmonic average is bounded by its largest
harmonic number; the monotonicity proof uses only k ≤ n. -/
private theorem stage137_binomial_harmonic_sum_le (n : Nat) :
    (Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) * harmonicReal k) ≤
    (Finset.range (n + 1)).sum (fun k =>
      (Nat.choose n k : Real) * harmonicReal n) := by
  apply Finset.sum_le_sum
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  exact mul_le_mul_of_nonneg_left (harmonicReal_mono hkn)
    (Nat.cast_nonneg _)

/-- Total binomial weight of the finite uniform-initialization law.
This is an exact normalization identity, before any asymptotics. -/
private theorem stage137_binomial_mass (n : Nat) :
    (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Real)) =
      (2 : Real) ^ n := by
  have h : ((1 : Real) + 1) ^ n =
      (Finset.range (n + 1)).sum (fun k => (Nat.choose n k : Real)) := by
    simp [add_pow]
  simpa only [one_add_one_eq_two] using h.symm

/-- A finite-n envelope: random-start harmonic cost is between zero
and the deterministic worst-case harmonic cost. This is not enough
alone for first-order asymptotics; Stage 138 supplies the sharp gap. -/
private theorem stage137_average_between_zero_and_max (n : Nat) :
    0 ≤ ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n ∧
    ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n ≤
      harmonicReal n := by
  have hp : (0 : Real) < (2 : Real) ^ n := by positivity
  constructor
  · exact div_nonneg (stage137_binomial_harmonic_sum_nonneg n) (le_of_lt hp)
  · apply (div_le_iff₀ hp).2
    calc
      (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k) ≤
        (Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal n) :=
            stage137_binomial_harmonic_sum_le n
      _ = (2 : Real) ^ n * harmonicReal n := by
        rw [← Finset.sum_mul, stage137_binomial_mass]
      _ = harmonicReal n * (2 : Real) ^ n := by ring

/-- The finite binomial correction becomes a difference of two normalized
terms. The identity holds even at the exceptional dimensions where the
logarithmic denominator is zero (real division is total in Lean). -/
private theorem stage137_log_normalized_identity
    (n : Nat)
    (hclosed :
      ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n =
      harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) :
    ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) /
          ((2 : Real) ^ n * Real.log (n : Real)) =
      harmonicReal n / Real.log (n : Real) -
        ((Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
          Real.log (n : Real) := by
  have hp : (2 : Real) ^ n ≠ 0 := by positivity
  calc
    ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) /
          ((2 : Real) ^ n * Real.log (n : Real)) =
        (((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k)) /
            (2 : Real) ^ n) / Real.log (n : Real) := by
              simp only [div_eq_mul_inv, mul_inv_rev]
              ring
    _ = (harmonicReal n -
        (Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
          Real.log (n : Real) := by rw [hclosed]
    _ = harmonicReal n / Real.log (n : Real) -
        ((Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
          Real.log (n : Real) := by ring

/-- An exact finite binomial identity implies the uniform, dimension-free
one-unit approximation `H_n - 1 ≤ E[H_K] ≤ H_n`. This is the concrete
estimate needed before invoking the harmonic/logarithm asymptotic. -/
private theorem stage137_harmonic_average_within_one
    (n : Nat)
    (hclosed :
      ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n =
        harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j))) :
    harmonicReal n - 1 ≤
      ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n ∧
    ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n ≤
      harmonicReal n := by
  have hbound :=
    proposed_rlsUniformInitial_harmonicCorrection_geometricEnvelope n
  have hpow : 0 ≤ (1 : Real) / (2 : Real) ^ n := by positivity
  rw [hclosed]
  constructor <;> linarith [hbound.1, hbound.2]

/-- Explicitly dominate the bounded harmonic correction after division
by log n (for n ≥ 2), avoiding any appeal to an infinite series. Its
limit is zero as soon as log n tends to infinity. -/
private theorem stage137_normalized_correction_le_inv_log
    (n : Nat) (hn : 2 ≤ n) :
    0 ≤ ((Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
      Real.log (n : Real) ∧
    ((Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
      Real.log (n : Real) ≤ (1 : Real) / Real.log (n : Real) := by
  have hn1 : (1 : Real) < (n : Real) := by
    exact_mod_cast (show 1 < n by omega)
  have hlog : 0 < Real.log (n : Real) := Real.log_pos hn1
  have hb := proposed_rlsUniformInitial_harmonicCorrection_geometricEnvelope n
  have hpow : 0 ≤ (1 : Real) / (2 : Real) ^ n := by positivity
  have hle : (Finset.Icc 1 n).sum (fun j =>
      (1 : Real) / ((j : Real) * (2 : Real) ^ j)) ≤ 1 := by
    linarith [hb.2]
  constructor
  · exact div_nonneg hb.1 (le_of_lt hlog)
  · apply (div_le_iff₀ hlog).2
    have hcancel : (1 : Real) / Real.log (n : Real) *
        Real.log (n : Real) = 1 := by
      field_simp [ne_of_gt hlog]
    rw [hcancel]
    exact hle

/-- The correction is at most one, so its quotient by log n vanishes.
The finite exceptional indices 0 and 1 are harmless because real division
by zero is total in Lean. Unlike the harmonic/log limit, this needs no
asymptotic expansion of the harmonic numbers. -/
private theorem stage137_correction_over_log_tendsto_zero :
    Tendsto
      (fun n : Nat =>
        ((Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
          Real.log (n : Real)) atTop (nhds (0 : Real)) := by
  have hlog : Tendsto
      (fun n : Nat => Real.log (n : Real)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto
      (fun n : Nat => (1 : Real) / Real.log (n : Real))
      atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using (tendsto_inv_atTop_zero.comp hlog)
  have hpoint (n : Nat) :
      0 ≤ ((Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
        Real.log (n : Real) ∧
      ((Finset.Icc 1 n).sum (fun j =>
        (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
        Real.log (n : Real) ≤
        (1 : Real) / Real.log (n : Real) := by
    by_cases hn : 2 ≤ n
    · exact stage137_normalized_correction_le_inv_log n hn
    · have hsmall : n = 0 ∨ n = 1 := by omega
      rcases hsmall with rfl | rfl
      · simp
      · simp
  apply squeeze_zero
  · intro n
    exact (hpoint n).1
  · intro n
    exact (hpoint n).2
  · exact hupper

/-- A finite correction identity, the standard harmonic/log limit, and
vanishing normalized correction together imply the headline asymptotic.
This implication is proved separately so the remaining two analytic inputs
can be supplied by reusable public lemmas rather than by hidden assumptions. -/
private theorem stage137_firstOrder_of_inputs
    (hclosed : ∀ n : Nat,
      ((Finset.range (n + 1)).sum (fun k =>
        (Nat.choose n k : Real) * harmonicReal k)) / (2 : Real) ^ n =
        harmonicReal n -
          (Finset.Icc 1 n).sum (fun j =>
            (1 : Real) / ((j : Real) * (2 : Real) ^ j)))
    (hharmonic : Tendsto
      (fun n : Nat => harmonicReal n / Real.log (n : Real))
      atTop (nhds (1 : Real)))
    (hcorrection : Tendsto
      (fun n : Nat =>
        ((Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
          Real.log (n : Real)) atTop (nhds (0 : Real))) :
    Tendsto
      (fun n : Nat =>
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k) /
            ((2 : Real) ^ n * Real.log (n : Real))))
      atTop (nhds (1 : Real)) := by
  have heq :
      (fun n : Nat =>
        ((Finset.range (n + 1)).sum (fun k =>
          (Nat.choose n k : Real) * harmonicReal k) /
            ((2 : Real) ^ n * Real.log (n : Real)))) =
      (fun n : Nat => harmonicReal n / Real.log (n : Real) -
        ((Finset.Icc 1 n).sum (fun j =>
          (1 : Real) / ((j : Real) * (2 : Real) ^ j))) /
          Real.log (n : Real)) := by
    funext n
    exact stage137_log_normalized_identity n (hclosed n)
  rw [heq]
  simpa only [sub_zero] using hharmonic.sub hcorrection

/-- The elementary harmonic lower and upper envelopes force
`Hₙ / log n → 1`. The finitely many zero-log indices do not affect an
`atTop` limit. This removes the final admitted analytic input of Stage 137. -/
private theorem stage137_harmonic_over_log_tendsto_one :
    Tendsto (fun n : Nat => harmonicReal n / Real.log (n : Real))
      atTop (nhds (1 : Real)) := by
  have hlog : Tendsto (fun n : Nat => Real.log (n : Real))
      atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : Nat => (1 : Real) / Real.log (n : Real))
      atTop (nhds (0 : Real)) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog)
  -- Use an explicit ordered subtraction instead of `linarith` on real
  -- division, whose nonlinear normalizer failed in Round 31. For n=0,1
  -- the denominator vanishes;
  -- we clip only the auxiliary deviation, not the approved headline theorem.
  have hbounds (n : Nat) (hn : 2 ≤ n) :
      (1 : Real) ≤ harmonicReal n / Real.log (n : Real) ∧
        harmonicReal n / Real.log (n : Real) ≤
          1 + (1 : Real) / Real.log (n : Real) := by
    have hnreal : (1 : Real) < (n : Real) := by
      exact_mod_cast (show 1 < n by omega)
    have hlogpos : 0 < Real.log (n : Real) := Real.log_pos hnreal
    have hmon : Real.log (n : Real) ≤ Real.log ((n : Real) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hlo : Real.log (n : Real) ≤ harmonicReal n :=
      hmon.trans (proposed_harmonicReal_log_succ_le n)
    have hhi : harmonicReal n ≤ 1 + Real.log (n : Real) :=
      harmonic_le_one_add_log n
    constructor
    · exact (le_div_iff₀ hlogpos).2 (by simpa only [one_mul] using hlo)
    · apply (div_le_iff₀ hlogpos).2
      have hnormalize :
          (1 + (1 : Real) / Real.log (n : Real)) * Real.log (n : Real) =
            1 + Real.log (n : Real) := by
        field_simp [ne_of_gt hlogpos]
        ring
      rw [hnormalize]
      exact hhi
  have hshifted : Tendsto
      (fun n : Nat => if 2 ≤ n then
        harmonicReal n / Real.log (n : Real) - 1 else (0 : Real))
      atTop (nhds (0 : Real)) := by
    apply squeeze_zero
    · intro n
      by_cases hn : 2 ≤ n
      · simp only [if_pos hn]
        exact sub_nonneg.mpr (hbounds n hn).1
      · simp [hn]
    · intro n
      by_cases hn : 2 ≤ n
      · simp only [if_pos hn]
        calc
          harmonicReal n / Real.log (n : Real) - 1 ≤
              (1 + (1 : Real) / Real.log (n : Real)) - 1 :=
            sub_le_sub_right (hbounds n hn).2 1
          _ = (1 : Real) / Real.log (n : Real) := by ring
      · have hsmall : n = 0 ∨ n = 1 := by omega
        rcases hsmall with rfl | rfl <;> simp [hn]
    · exact hinv
  have hevent :
      (fun n : Nat => if 2 ≤ n then
        harmonicReal n / Real.log (n : Real) - 1 else (0 : Real)) =ᶠ[atTop]
      (fun n : Nat => harmonicReal n / Real.log (n : Real) - 1) := by
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with n hn
    simp [hn]
  have hdiff : Tendsto
      (fun n : Nat => harmonicReal n / Real.log (n : Real) - 1)
      atTop (nhds (0 : Real)) := hshifted.congr' hevent
  have heq :
      (fun n : Nat => (1 : Real) +
        (harmonicReal n / Real.log (n : Real) - 1)) =
      (fun n : Nat => harmonicReal n / Real.log (n : Real)) := by
    funext n
    ring
  rw [← heq]
  simpa only [add_zero] using (tendsto_const_nhds.add hdiff)

/-- The binomially averaged harmonic coupon-collector runtime has first-order
coefficient 1 after normalization by log n. -/
theorem proposed_rlsUniformInitial_harmonic_firstOrder
    : Tendsto
        (fun n : Nat =>
          ((Finset.range (n + 1)).sum (fun k =>
            (Nat.choose n k : Real) * harmonicReal k) /
              ((2 : Real) ^ n * Real.log (n : Real))))
        atTop (nhds (1 : Real)) := by
  -- Stage 138 provides the exact finite identity; the bounded correction
  -- has a complete independent vanishing proof attempt above. The harmonic/log limit is now independently compiled; the public
  -- promotion gate still needs to verify this integration.
  have hharmonic : Tendsto
      (fun n : Nat => harmonicReal n / Real.log (n : Real))
      atTop (nhds (1 : Real)) :=
    stage137_harmonic_over_log_tendsto_one
  exact stage137_firstOrder_of_inputs
    proposed_binomialHarmonicAverage_closedForm hharmonic
    stage137_correction_over_log_tendsto_zero

end ECRuntime
