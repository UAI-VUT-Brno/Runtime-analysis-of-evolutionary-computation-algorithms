import ECRuntime.WittMutationDrift
import ECRuntime.WittStandardCaseC3
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 44: C3 branch for the mutation-rate parameterized Witt potential

Stage 43 reduced the general-rate one-step argument to nonnegativity of the
non-singleton remainder for

`V_p(x) = wittMutationLinearPotential p w x`.

This module closes the multi-improvement (classical C3) part under one explicit
finite-dimensional numerical condition.  The same accepted-mask erase map used in the
compiler-promoted standard-rate proof gives

`badMass <= p * (sum_i g_i(p)) * acceptedMass`.

The parameterized coefficients have base `(1-p)^(-1)`, hence their sorted sum is bounded
by the geometric envelope `sum_{r=0}^{n-1} base^r`.  For positive dimension this envelope
has the exact scaled form

`p * envelope = base^(n-1) - (1-p)`.

Therefore C3 is nonnegative whenever this quantity is at most `2`.  The condition is
kept explicit because it is the genuine finite-`n` boundary of this particular C3
envelope argument.  As a robust first specialization, the module proves that the
condition always holds for `p = c/n`, `0 <= c <= 1`, and `n >= 4`, by monotone comparison
with the already compiler-promoted standard-rate envelope.

No C2A strict-tail claim is generalized here.  The final section rewrites the Stage-43
remainder as `C2 remainder + C3 contribution`, so after this module is promoted the
remaining general-rate branch is again exactly C2.
-/

/-! ## Geometric envelope for the parameterized coefficients -/

/-- The reciprocal-survival base is monotone in the mutation probability on `(-∞,1)`. -/
theorem wittMutationBase_mono {p q : ℝ}
    (hp1 : p < 1) (hq1 : q < 1) (hpq : p ≤ q) :
    wittMutationBase p ≤ wittMutationBase q := by
  have hsurv : 1 - q ≤ 1 - p := by linarith
  have hqbase0 : 0 ≤ wittMutationBase q :=
    (wittMutationBase_pos hq1).le
  have hscaled :
      wittMutationBase q * (1 - q) ≤
        wittMutationBase q * (1 - p) :=
    mul_le_mul_of_nonneg_left hsurv hqbase0
  have hcomp :
      wittMutationBase p * (1 - p) ≤
        wittMutationBase q * (1 - p) := by
    rw [wittMutationBase_mul_survival hp1]
    calc
      (1 : ℝ) = wittMutationBase q * (1 - q) :=
        (wittMutationBase_mul_survival hq1).symm
      _ ≤ wittMutationBase q * (1 - p) := hscaled
  nlinarith [hcomp, wittMutation_survival_pos hp1]

/-- The Stage-32 reverse-rank exponent bound gives the matching geometric envelope for
arbitrary `0 <= p < 1`. -/
theorem wittMutationPotentialWeight_le_reverseGeometric {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    wittMutationPotentialWeight p w i ≤
      wittMutationBase p ^ (n - 1 - i.val) := by
  unfold wittMutationPotentialWeight
  exact (pow_right_mono₀ (one_le_wittMutationBase hp0 hp1))
    (wittStandardExponent_le_reverseRank w hmono i)

/-- The complete parameterized coefficient sum is bounded by the full finite geometric
envelope. -/
theorem sum_wittMutationPotentialWeight_le_geometricEnvelope {n : ℕ}
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) :
    (∑ i : Fin n, wittMutationPotentialWeight p w i) ≤
      ∑ i : Fin n, wittMutationBase p ^ i.val := by
  calc
    (∑ i : Fin n, wittMutationPotentialWeight p w i) ≤
        ∑ i : Fin n, wittMutationBase p ^ (n - 1 - i.val) := by
      apply Finset.sum_le_sum
      intro i hi
      exact wittMutationPotentialWeight_le_reverseGeometric hp0 hp1 w hmono i
    _ = ∑ i : Fin n, wittMutationBase p ^ i.val :=
      witt_reverse_geometric_sum_eq (wittMutationBase p) n

/-- Exact finite-`n` scaled geometric envelope for the reciprocal-survival base. -/
theorem mutationRate_mul_wittMutationGeometricEnvelope_eq
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp1 : p < 1) :
    p * (∑ i : Fin n, wittMutationBase p ^ i.val) =
      wittMutationBase p ^ (n - 1) - (1 - p) := by
  let b : ℝ := wittMutationBase p
  change p * (∑ i : Fin n, b ^ i.val) = b ^ (n - 1) - (1 - p)
  have hbq : b * (1 - p) = 1 := by
    simpa [b] using wittMutationBase_mul_survival hp1
  have hqb : (1 - p) * b = 1 := by
    rw [mul_comm]
    exact hbq
  have hpfactor : p = (1 - p) * (b - 1) := by
    calc
      p = 1 - (1 - p) := by ring
      _ = (1 - p) * b - (1 - p) := by rw [hqb]
      _ = (1 - p) * (b - 1) := by ring
  have hgeom := witt_fin_sum_pow_mul_sub_one b n
  have hnexp : n = (n - 1) + 1 := by omega
  have hpow : b ^ n = b ^ (n - 1) * b := by
    calc
      b ^ n = b ^ ((n - 1) + 1) :=
        congrArg (fun k : ℕ => b ^ k) hnexp
      _ = b ^ (n - 1) * b := by rw [pow_succ]
  have hpowSurvival : (1 - p) * b ^ n = b ^ (n - 1) := by
    rw [hpow]
    calc
      (1 - p) * (b ^ (n - 1) * b) =
          b ^ (n - 1) * (b * (1 - p)) := by ring
      _ = b ^ (n - 1) := by rw [hbq]; ring
  calc
    p * (∑ i : Fin n, b ^ i.val) =
        ((1 - p) * (b - 1)) * (∑ i : Fin n, b ^ i.val) := by
      exact congrArg (fun a : ℝ => a * (∑ i : Fin n, b ^ i.val)) hpfactor
    _ = (1 - p) * ((∑ i : Fin n, b ^ i.val) * (b - 1)) := by ring
    _ = (1 - p) * (b ^ n - 1) := by rw [hgeom]
    _ = (1 - p) * b ^ n - (1 - p) := by ring
    _ = b ^ (n - 1) - (1 - p) := by rw [hpowSurvival]

/-- Exact finite-dimensional numerical condition needed by the Stage-44 C3 envelope. -/
def WittMutationC3EnvelopeCondition (p : ℝ) (n : ℕ) : Prop :=
  p * (∑ i : Fin n, wittMutationBase p ^ i.val) ≤ 2

/-- Closed form of the finite-dimensional C3 envelope condition. -/
theorem wittMutationC3EnvelopeCondition_iff_closedForm
    {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp1 : p < 1) :
    WittMutationC3EnvelopeCondition p n ↔
      wittMutationBase p ^ (n - 1) - (1 - p) ≤ 2 := by
  unfold WittMutationC3EnvelopeCondition
  rw [mutationRate_mul_wittMutationGeometricEnvelope_eq hn hp1]

/-- For `n >= 4`, every scaled rate `c/n` with `0 <= c <= 1` is no larger than the
standard rate. -/
theorem scaledMutationRate_le_standardMutationRate_of_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    scaledMutationRate c n ≤ standardMutationRate n := by
  have hn2 : 2 ≤ n := by omega
  have hstd0 : 0 ≤ standardMutationRate n :=
    (standardMutationRate_mem_unitInterval_linear hn2).1
  rw [scaledMutationRate_eq_mul_standardMutationRate (by omega : 0 < n)]
  have hmul := mul_le_mul_of_nonneg_right hc1 hstd0
  simpa using hmul

/-- The parameterized geometric base at `c/n`, for `c <= 1`, is bounded by the
standard-rate base. -/
theorem wittMutationBase_scaled_le_standard
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    wittMutationBase (scaledMutationRate c n) ≤ wittStandardBase n := by
  have hn2 : 2 ≤ n := by omega
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0 hc1
  have hstdlt : standardMutationRate n < 1 := standardMutationRate_lt_one hn2
  have hplt : scaledMutationRate c n < 1 := lt_of_le_of_lt hp_le hstdlt
  have hbase := wittMutationBase_mono hplt hstdlt hp_le
  rw [wittMutationBase_standardMutationRate_eq_wittStandardBase hn2] at hbase
  exact hbase

/-- Consequently the complete scaled geometric envelope is dominated by the promoted
standard-rate envelope whenever `0 <= c <= 1`. -/
theorem scaledMutationRate_mul_wittMutationGeometricEnvelope_le_standard
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    scaledMutationRate c n *
        (∑ i : Fin n, wittMutationBase (scaledMutationRate c n) ^ i.val) ≤
      standardMutationRate n *
        (∑ i : Fin n, wittStandardBase n ^ i.val) := by
  have hn2 : 2 ≤ n := by omega
  have hp0 : 0 ≤ scaledMutationRate c n := scaledMutationRate_nonneg hc0
  have hstd0 : 0 ≤ standardMutationRate n :=
    (standardMutationRate_mem_unitInterval_linear hn2).1
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0 hc1
  have hstdlt : standardMutationRate n < 1 := standardMutationRate_lt_one hn2
  have hplt : scaledMutationRate c n < 1 := lt_of_le_of_lt hp_le hstdlt
  have hbase := wittMutationBase_scaled_le_standard hn hc0 hc1
  have hsum0 :
      0 ≤ ∑ i : Fin n, wittMutationBase (scaledMutationRate c n) ^ i.val := by
    apply Finset.sum_nonneg
    intro i hi
    exact pow_nonneg (wittMutationBase_pos hplt).le _
  have hsumle :
      (∑ i : Fin n, wittMutationBase (scaledMutationRate c n) ^ i.val) ≤
        ∑ i : Fin n, wittStandardBase n ^ i.val := by
    apply Finset.sum_le_sum
    intro i hi
    exact pow_le_pow_left₀ (wittMutationBase_pos hplt).le hbase i.val
  calc
    scaledMutationRate c n *
        (∑ i : Fin n, wittMutationBase (scaledMutationRate c n) ^ i.val) ≤
      standardMutationRate n *
        (∑ i : Fin n, wittMutationBase (scaledMutationRate c n) ^ i.val) :=
      mul_le_mul_of_nonneg_right hp_le hsum0
    _ ≤ standardMutationRate n *
        (∑ i : Fin n, wittStandardBase n ^ i.val) :=
      mul_le_mul_of_nonneg_left hsumle hstd0

/-- In particular, `0 <= c <= 1` satisfies the exact finite-`n` C3 envelope condition
for every `n >= 4`. -/
theorem wittMutationC3EnvelopeCondition_scaled_of_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    WittMutationC3EnvelopeCondition (scaledMutationRate c n) n := by
  unfold WittMutationC3EnvelopeCondition
  exact (scaledMutationRate_mul_wittMutationGeometricEnvelope_le_standard
      hn hc0 hc1).trans
    (standardMutationRate_mul_wittGeometricEnvelope_le_two hn)

/-! ## Parameterized C3 bad mass and contribution -/

/-- Expected worsening parameterized-Witt mass carried by accepted C3 masks. -/
noncomputable def wittMutationCaseC3BadMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x,
    mutationMaskWeight p mask *
      (∑ i ∈ oneToZeroFlips x mask, wittMutationPotentialWeight p w i)

/-- The parameterized C3 worsening mass written coordinatewise using the promoted C3
flip-at masses. -/
theorem wittMutationCaseC3BadMass_eq_sum_coordinate_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittMutationCaseC3BadMass p w x =
      ∑ i : Fin n,
        if x i = true then
          wittMutationPotentialWeight p w i *
            rankLinearCaseC3FlipAtMass p w x i
        else 0 := by
  classical
  unfold wittMutationCaseC3BadMass
  simp_rw [oneToZeroFlips, Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hxi : x i = true
  · rw [if_pos hxi]
    unfold rankLinearCaseC3FlipAtMass classicalLinearCaseC3AcceptedWithFlipAt
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro mask hmask
    by_cases him : i ∈ mask <;> simp [hxi, him, mul_comm]
  · rw [if_neg hxi]
    apply Finset.sum_eq_zero
    intro mask hmask
    simp [hxi]

/-- Before imposing the finite C3 envelope condition, accepted worsening mass is bounded
by `p * (sum_i g_i(p))` times accepted C3 mass. -/
theorem wittMutationCaseC3BadMass_le_rate_mul_weightSum_mul_mass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    wittMutationCaseC3BadMass p w x ≤
      p * (∑ i : Fin n, wittMutationPotentialWeight p w i) *
        rankLinearCaseC3AcceptedMass p w x := by
  rw [wittMutationCaseC3BadMass_eq_sum_coordinate_flipMass]
  have hmass0 : 0 ≤ rankLinearCaseC3AcceptedMass p w x :=
    rankLinearCaseC3AcceptedMass_nonneg hp0 hp1.le w x
  have hpmass0 : 0 ≤ p * rankLinearCaseC3AcceptedMass p w x :=
    mul_nonneg hp0 hmass0
  calc
    (∑ i : Fin n,
      if x i = true then
        wittMutationPotentialWeight p w i * rankLinearCaseC3FlipAtMass p w x i
      else 0) ≤
        ∑ i : Fin n,
          wittMutationPotentialWeight p w i *
            (p * rankLinearCaseC3AcceptedMass p w x) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hxi : x i = true
      · rw [if_pos hxi]
        have hflip := rankLinearCaseC3FlipAtMass_le_p_mul_acceptedMass
          hp0 hp1.le w hw x i hxi
        exact mul_le_mul_of_nonneg_left hflip
          (wittMutationPotentialWeight_pos hp0 hp1 w i).le
      · rw [if_neg hxi]
        exact mul_nonneg (wittMutationPotentialWeight_pos hp0 hp1 w i).le hpmass0
    _ = (∑ i : Fin n, wittMutationPotentialWeight p w i) *
          (p * rankLinearCaseC3AcceptedMass p w x) := by
      rw [Finset.sum_mul]
    _ = p * (∑ i : Fin n, wittMutationPotentialWeight p w i) *
          rankLinearCaseC3AcceptedMass p w x := by ring

/-- The exact finite envelope condition bounds accepted C3 worsening mass by twice its
accepted probability mass. -/
theorem wittMutationCaseC3BadMass_le_two_mul_acceptedMass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n)
    (henv : WittMutationC3EnvelopeCondition p n) :
    wittMutationCaseC3BadMass p w x ≤
      2 * rankLinearCaseC3AcceptedMass p w x := by
  have hbad := wittMutationCaseC3BadMass_le_rate_mul_weightSum_mul_mass
    hp0 hp1 w hw x
  have hsum := sum_wittMutationPotentialWeight_le_geometricEnvelope
    hp0 hp1 w hmono
  have hscale :
      p * (∑ i : Fin n, wittMutationPotentialWeight p w i) ≤ 2 := by
    calc
      p * (∑ i : Fin n, wittMutationPotentialWeight p w i) ≤
          p * (∑ i : Fin n, wittMutationBase p ^ i.val) :=
        mul_le_mul_of_nonneg_left hsum hp0
      _ ≤ 2 := henv
  have hmass0 : 0 ≤ rankLinearCaseC3AcceptedMass p w x :=
    rankLinearCaseC3AcceptedMass_nonneg hp0 hp1.le w x
  calc
    wittMutationCaseC3BadMass p w x ≤
        p * (∑ i : Fin n, wittMutationPotentialWeight p w i) *
          rankLinearCaseC3AcceptedMass p w x := hbad
    _ ≤ 2 * rankLinearCaseC3AcceptedMass p w x :=
      mul_le_mul_of_nonneg_right hscale hmass0

/-- In C3 the improving side contains at least two parameterized Witt coefficients, each
of which is at least one. -/
theorem two_le_wittMutationPotentialWeight_sum_zeroToOne_of_caseC3
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hC3 : IsClassicalLinearCaseC3 x mask) :
    (2 : ℝ) ≤
      ∑ i ∈ zeroToOneFlips x mask, wittMutationPotentialWeight p w i := by
  have hcard : 2 ≤ (zeroToOneFlips x mask).card := by
    simpa [IsClassicalLinearCaseC3, zeroToOneFlipCount] using hC3
  calc
    (2 : ℝ) ≤ ((zeroToOneFlips x mask).card : ℝ) := by exact_mod_cast hcard
    _ = ∑ _i ∈ zeroToOneFlips x mask, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ zeroToOneFlips x mask, wittMutationPotentialWeight p w i := by
      apply Finset.sum_le_sum
      intro i hi
      exact one_le_wittMutationPotentialWeight hp0 hp1 w i

/-- Every accepted C3 mask has parameterized-Witt drop at least two minus its worsening
parameterized-Witt mass. -/
theorem wittMutationLinearPotential_selected_drop_ge_two_sub_bad_of_caseC3
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hC3 : IsClassicalLinearCaseC3 x mask)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    (2 : ℝ) -
        (∑ i ∈ oneToZeroFlips x mask, wittMutationPotentialWeight p w i) ≤
      wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask) := by
  rw [wittMutationLinearPotential_selected_drop_of_accepts p w x mask hacc,
    flipContribution_sum_eq_flip_sums]
  have hpos := two_le_wittMutationPotentialWeight_sum_zeroToOne_of_caseC3
    hp0 hp1 w x mask hC3
  linarith

/-- Parameterized-Witt drift contribution of accepted C3 masks. -/
noncomputable def wittMutationCaseC3AcceptedContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

/-- Parameterized-Witt drift contribution of all C3 masks. -/
noncomputable def wittMutationCaseC3Contribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3Masks x,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

/-- Rejected C3 masks vanish, so the complete parameterized C3 contribution is the
accepted contribution. -/
theorem wittMutationCaseC3Contribution_eq_accepted {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittMutationCaseC3Contribution p w x =
      wittMutationCaseC3AcceptedContribution p w x := by
  classical
  unfold wittMutationCaseC3Contribution wittMutationCaseC3AcceptedContribution
    classicalLinearCaseC3AcceptedMasks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp [hacc]
  · rw [wittMutationLinearPotential_selected_drop_of_rejects p w x mask hacc]
    simp [hacc]

/-- Deterministic C3 reduction: contribution is at least `2 * mass - badMass`. -/
theorem two_mul_wittMutationCaseC3AcceptedMass_sub_badMass_le_contribution
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (x : BitString n) :
    2 * rankLinearCaseC3AcceptedMass p w x - wittMutationCaseC3BadMass p w x ≤
      wittMutationCaseC3AcceptedContribution p w x := by
  unfold rankLinearCaseC3AcceptedMass wittMutationCaseC3BadMass
    wittMutationCaseC3AcceptedContribution
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro mask hmask
  have hmem := (mem_classicalLinearCaseC3AcceptedMasks w x mask).mp hmask
  have hdrop := wittMutationLinearPotential_selected_drop_ge_two_sub_bad_of_caseC3
    hp0 hp1 w x mask hmem.1 hmem.2
  have hwt : 0 ≤ mutationMaskWeight p mask := mutationMaskWeight_nonneg hp0 hp1.le mask
  have hmul := mul_le_mul_of_nonneg_left hdrop hwt
  nlinarith

/-- Under the exact finite envelope condition, the complete C3 contribution is
nonnegative. -/
theorem wittMutationCaseC3Contribution_nonneg_of_envelope
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n)
    (henv : WittMutationC3EnvelopeCondition p n) :
    0 ≤ wittMutationCaseC3Contribution p w x := by
  rw [wittMutationCaseC3Contribution_eq_accepted]
  have hlower := two_mul_wittMutationCaseC3AcceptedMass_sub_badMass_le_contribution
    hp0 hp1 w x
  have hbad := wittMutationCaseC3BadMass_le_two_mul_acceptedMass
    hp0 hp1 w hw hmono x henv
  linarith

/-- Concrete Stage-44 C3 closure for every `p=c/n` with `0 <= c <= 1` and `n >= 4`. -/
theorem wittMutationCaseC3Contribution_nonneg_scaled_of_le_one
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    0 ≤ wittMutationCaseC3Contribution (scaledMutationRate c n) w x := by
  have hp_le := scaledMutationRate_le_standardMutationRate_of_le_one hn hc0 hc1
  have hplt : scaledMutationRate c n < 1 :=
    lt_of_le_of_lt hp_le (standardMutationRate_lt_one (by omega : 2 ≤ n))
  exact wittMutationCaseC3Contribution_nonneg_of_envelope
    (scaledMutationRate_nonneg hc0) hplt w hw hmono x
    (wittMutationC3EnvelopeCondition_scaled_of_le_one hn hc0 hc1)

/-! ## Reduction of the Stage-43 remainder after closing C3 -/

/-- Complete parameterized-Witt contribution of the numerical C2 mask class. -/
noncomputable def wittMutationCaseC2Contribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2Masks x,
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))

/-- The complete parameterized-Witt mask sum splits into C1, C2, and C3 pieces. -/
theorem wittMutation_mask_sum_eq_case_sums {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    (∑ mask : MutationMask n,
      mutationMaskWeight p mask *
        (wittMutationLinearPotential p w x -
          wittMutationLinearPotential p w
            (selectedAfterMask (linearFitness w) x mask))) =
      (∑ mask ∈ classicalLinearCaseC1Masks x,
        mutationMaskWeight p mask *
          (wittMutationLinearPotential p w x -
            wittMutationLinearPotential p w
              (selectedAfterMask (linearFitness w) x mask))) +
      wittMutationCaseC2Contribution p w x +
      wittMutationCaseC3Contribution p w x := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittMutationLinearPotential p w x -
        wittMutationLinearPotential p w
          (selectedAfterMask (linearFitness w) x mask))
  change (∑ mask : MutationMask n, F mask) =
    (∑ mask ∈ classicalLinearCaseC1Masks x, F mask) +
      (∑ mask ∈ classicalLinearCaseC2Masks x, F mask) +
        (∑ mask ∈ classicalLinearCaseC3Masks x, F mask)
  have h12 := classicalLinearCaseC1Masks_disjoint_C2Masks x
  have h123 := classicalLinearCaseC1_union_C2_disjoint_C3Masks x
  calc
    (∑ mask : MutationMask n, F mask) =
        ∑ mask ∈
          ((classicalLinearCaseC1Masks x ∪ classicalLinearCaseC2Masks x) ∪
            classicalLinearCaseC3Masks x), F mask := by
          rw [classicalLinearCaseMasks_union_eq_univ x]
    _ = (∑ mask ∈ classicalLinearCaseC1Masks x ∪ classicalLinearCaseC2Masks x,
          F mask) +
        (∑ mask ∈ classicalLinearCaseC3Masks x, F mask) :=
          Finset.sum_union h123
    _ = ((∑ mask ∈ classicalLinearCaseC1Masks x, F mask) +
          (∑ mask ∈ classicalLinearCaseC2Masks x, F mask)) +
        (∑ mask ∈ classicalLinearCaseC3Masks x, F mask) := by
          rw [Finset.sum_union h12]

/-- For positive weights, C1 vanishes, so total parameterized-Witt drift is C2 plus C3. -/
theorem wittMutationLinear_drift_eq_caseC2_add_caseC3 {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (wittMutationLinearPotential p w) x =
      wittMutationCaseC2Contribution p w x +
        wittMutationCaseC3Contribution p w x := by
  rw [wittMutationLinear_drift_eq_mask_sum]
  rw [wittMutation_mask_sum_eq_case_sums]
  rw [wittMutation_caseC1_contribution_eq_zero (p := p) w hw x]
  simp

/-- What remains inside C2 after removing the already extracted zero-singleton term. -/
noncomputable def wittMutationCaseC2RemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  wittMutationCaseC2Contribution p w x -
    linearSingletonRate n p * wittMutationLinearPotential p w x

/-- The Stage-43 remainder is exactly the C2 remainder plus the C3 contribution. -/
theorem wittMutationRemainderContribution_eq_caseC2Remainder_add_caseC3
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    wittMutationRemainderContribution p w x =
      wittMutationCaseC2RemainderContribution p w x +
        wittMutationCaseC3Contribution p w x := by
  have hsingle := wittMutationLinear_drift_eq_singleton_add_remainder
    (p := p) w hw x
  have hcases := wittMutationLinear_drift_eq_caseC2_add_caseC3 p w hw x
  unfold wittMutationCaseC2RemainderContribution
  linarith

/-- The sole aggregate certificate remaining after Stage 44 for a fixed mutation rate. -/
def HasWittMutationCaseC2RemainderNonnegativity {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ x : BitString n, 0 ≤ wittMutationCaseC2RemainderContribution p w x

/-- Once C3 satisfies its exact finite envelope condition, nonnegative C2 remainder closes
the complete Stage-43 remainder. -/
theorem hasWittMutationRemainderNonnegativity_of_caseC2_of_envelope
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (henv : WittMutationC3EnvelopeCondition p n)
    (hC2 : HasWittMutationCaseC2RemainderNonnegativity p w) :
    HasWittMutationRemainderNonnegativity p w := by
  intro x
  rw [wittMutationRemainderContribution_eq_caseC2Remainder_add_caseC3 w hw x]
  exact add_nonneg (hC2 x)
    (wittMutationCaseC3Contribution_nonneg_of_envelope
      hp0 hp1 w hw hmono x henv)

/-- Concrete scaled-rate reduction: for `0 <= c <= 1` and `n >= 4`, only C2 remains. -/
theorem hasWittMutationRemainderNonnegativity_scaled_of_caseC2
    {n : ℕ} (hn : 4 ≤ n) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (hC2 : HasWittMutationCaseC2RemainderNonnegativity
      (scaledMutationRate c n) w) :
    HasWittMutationRemainderNonnegativity (scaledMutationRate c n) w := by
  intro x
  rw [wittMutationRemainderContribution_eq_caseC2Remainder_add_caseC3 w hw x]
  exact add_nonneg (hC2 x)
    (wittMutationCaseC3Contribution_nonneg_scaled_of_le_one
      hn hc0 hc1 w hw hmono x)

end ECRuntime
