import ECRuntime.WittStandardDrift
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 32: geometric envelope and the C3 branch of Witt's standard-rate drift proof

Stage 31 reduced the sharp standard-rate drift theorem to nonnegativity of a finite
non-singleton remainder.  The first genuinely aggregate branch in Witt's proof is the
case in which at least two currently-zero coordinates flip to one (the repository's
classical case C3).

This module closes that branch.  There are two ingredients.

First, monotonicity of the objective coefficients gives a sharper coordinatewise bound
on the Stage-30 Witt exponent: the exponent at coordinate `i` is at most the number of
coordinates strictly to its right, `n - 1 - i.val`.  Hence the complete coefficient
sum is bounded by the finite geometric envelope

  `sum_{k=0}^{n-1} (1 + 1/(n-1))^k`.

At standard mutation and `n >= 4`, multiplying this envelope by `1/n` gives at most
`2`.  This is the finite-dimensional estimate used in Case 1 of Witt's refined proof.

Second, the already compiler-promoted C3 erase-map argument in `LinearRuntime.lean`
shows that, conditional on accepted C3 masks, the flip mass of every currently-one
coordinate is at most `p` times the total accepted C3 mass.  Weighting that statement
by the Witt coefficients and summing over coordinates bounds the aggregate worsening
Witt mass by `2` times accepted C3 mass.  Every C3 mask has at least two improving
flips and every Witt coefficient is at least one, so the full C3 contribution is
nonnegative.

No C2A claim is made here.  After this module is compiler verified, the sole genuinely
open branch of the Stage-31 remainder is the one-improving-flip / less-important-
worsening-flips branch (Witt's Subcase 2.2.2).
-/

/-- Reversal of a finite coordinate, used only to reindex the geometric envelope. -/
def wittReverseIndex {n : ℕ} (i : Fin n) : Fin n :=
  ⟨n - (i.val + 1), by omega⟩

@[simp] theorem wittReverseIndex_involutive {n : ℕ} (i : Fin n) :
    wittReverseIndex (wittReverseIndex i) = i := by
  apply Fin.ext
  dsimp [wittReverseIndex]
  omega

/-- The coordinate reversal as an explicit finite equivalence. -/
def wittReverseIndexEquiv (n : ℕ) : Fin n ≃ Fin n where
  toFun := wittReverseIndex
  invFun := wittReverseIndex
  left_inv := by intro i; exact wittReverseIndex_involutive i
  right_inv := by intro i; exact wittReverseIndex_involutive i

@[simp] theorem wittReverseIndexEquiv_apply {n : ℕ} (i : Fin n) :
    wittReverseIndexEquiv n i = wittReverseIndex i := by
  rfl

/-- Under nonincreasing objective weights, a strictly smaller coefficient can occur
only at a strictly larger repository coordinate. -/
theorem wittStandard_strictSmaller_subset_Ioi {n : ℕ}
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    ((Finset.univ : Finset (Fin n)).filter (fun j => w j < w i)) ⊆
      Finset.Ioi i := by
  classical
  intro j hj
  have hjlt : w j < w i := (Finset.mem_filter.mp hj).2
  have hij : i.val < j.val := by
    by_contra hnot
    have hji : j.val ≤ i.val := by omega
    have hwi : w i ≤ w j := hmono j i hji
    linarith
  exact Finset.mem_Ioi.mpr hij

/-- Coordinate-sensitive version of the Stage-30 exponent bound. -/
theorem wittStandardExponent_le_reverseRank {n : ℕ}
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    wittStandardExponent w i ≤ n - 1 - i.val := by
  classical
  unfold wittStandardExponent
  have hcard := Finset.card_le_card
    (wittStandard_strictSmaller_subset_Ioi w hmono i)
  simpa using hcard

/-- Every Witt coefficient lies below the matching coordinate of the full geometric
envelope. -/
theorem wittStandardPotentialWeight_le_reverseGeometric {n : ℕ}
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) (i : Fin n) :
    wittStandardPotentialWeight w i ≤
      wittStandardBase n ^ (n - 1 - i.val) := by
  unfold wittStandardPotentialWeight
  exact (pow_right_mono₀ (one_le_wittStandardBase n))
    (wittStandardExponent_le_reverseRank w hmono i)

/-- Reversing all finite exponents leaves the finite geometric sum unchanged. -/
theorem witt_reverse_geometric_sum_eq (r : ℝ) (n : ℕ) :
    (∑ i : Fin n, r ^ (n - 1 - i.val)) =
      ∑ i : Fin n, r ^ i.val := by
  classical
  symm
  refine Fintype.sum_equiv (wittReverseIndexEquiv n)
    (fun i : Fin n => r ^ i.val)
    (fun j : Fin n => r ^ (n - 1 - j.val)) ?_
  intro i
  congr 1
  dsimp [wittReverseIndexEquiv, wittReverseIndex]
  omega

/-- The complete Witt coefficient sum is bounded by the full finite geometric envelope. -/
theorem sum_wittStandardPotentialWeight_le_geometricEnvelope {n : ℕ}
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) :
    (∑ i : Fin n, wittStandardPotentialWeight w i) ≤
      ∑ i : Fin n, wittStandardBase n ^ i.val := by
  calc
    (∑ i : Fin n, wittStandardPotentialWeight w i) ≤
        ∑ i : Fin n, wittStandardBase n ^ (n - 1 - i.val) := by
      apply Finset.sum_le_sum
      intro i hi
      exact wittStandardPotentialWeight_le_reverseGeometric w hmono i
    _ = ∑ i : Fin n, wittStandardBase n ^ i.val :=
      witt_reverse_geometric_sum_eq (wittStandardBase n) n

/-- Finite geometric power sum, in the multiplication form convenient for the
standard-rate envelope calculation. -/
theorem witt_fin_sum_pow_mul_sub_one (r : ℝ) (n : ℕ) :
    (∑ i : Fin n, r ^ i.val) * (r - 1) = r ^ n - 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      have hshift :
          (∑ i : Fin n, r ^ (i.succ).val) =
            r * ∑ i : Fin n, r ^ i.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [show (i.succ).val = i.val + 1 by rfl]
        rw [pow_succ]
        ring
      rw [hshift]
      simp only [Fin.val_zero, pow_zero]
      calc
        (1 + r * ∑ i : Fin n, r ^ i.val) * (r - 1) =
            (r - 1) + r * ((∑ i : Fin n, r ^ i.val) * (r - 1)) := by
          ring
        _ = (r - 1) + r * (r ^ n - 1) := by rw [ih]
        _ = r ^ (n + 1) - 1 := by rw [pow_succ]; ring

/-- Division form of the finite geometric sum. -/
theorem witt_fin_sum_pow_eq_geom (r : ℝ) (n : ℕ) (hr : r ≠ 1) :
    (∑ i : Fin n, r ^ i.val) = (r ^ n - 1) / (r - 1) := by
  rw [eq_div_iff (sub_ne_zero.mpr hr)]
  exact witt_fin_sum_pow_mul_sub_one r n

/-- At standard mutation, scaling the exact geometric envelope has the simple closed
form `base^(n-1) - (1-p)`. -/
theorem standardMutationRate_mul_wittGeometricEnvelope_eq {n : ℕ} (hn : 2 ≤ n) :
    standardMutationRate n * (∑ i : Fin n, wittStandardBase n ^ i.val) =
      wittStandardBase n ^ (n - 1) - (1 - standardMutationRate n) := by
  let m : ℕ := n - 1
  have hnpos : 0 < n := by omega
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hnreal_ne : (n : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hnpos)
  have hmreal_ne : (m : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast hmpos)
  have hm_succ : m + 1 = n := by
    dsimp [m]
    omega
  have hp : standardMutationRate n = (n : ℝ)⁻¹ := by
    simp [standardMutationRate, Nat.ne_of_gt hnpos]
  have hbase_sub : wittStandardBase n - 1 = (m : ℝ)⁻¹ := by
    simp [wittStandardBase, m]
  have hbase_ne : wittStandardBase n ≠ 1 := by
    have hpredpos : 0 < n - 1 := by omega
    have hinvpos : 0 < (((n - 1 : ℕ) : ℝ))⁻¹ :=
      inv_pos.mpr (by exact_mod_cast hpredpos)
    unfold wittStandardBase
    linarith
  have hmcast : (m : ℝ) + 1 = (n : ℝ) := by
    exact_mod_cast hm_succ
  have hscale :
      standardMutationRate n / (wittStandardBase n - 1) =
        1 - standardMutationRate n := by
    rw [hp, hbase_sub]
    field_simp [hnreal_ne, hmreal_ne]
    nlinarith [hmcast]
  have hnexp : n = (n - 1) + 1 := by omega
  have hpow :
      wittStandardBase n ^ n =
        wittStandardBase n ^ (n - 1) * wittStandardBase n := by
    calc
      wittStandardBase n ^ n =
          wittStandardBase n ^ ((n - 1) + 1) :=
        congrArg (fun k : ℕ => wittStandardBase n ^ k) hnexp
      _ = wittStandardBase n ^ (n - 1) * wittStandardBase n := by
        rw [pow_succ]
  have hpowSurvival :
      (1 - standardMutationRate n) * wittStandardBase n ^ n =
        wittStandardBase n ^ (n - 1) := by
    rw [hpow]
    calc
      (1 - standardMutationRate n) *
          (wittStandardBase n ^ (n - 1) * wittStandardBase n) =
          wittStandardBase n ^ (n - 1) *
            (wittStandardBase n * (1 - standardMutationRate n)) := by
        ring
      _ = wittStandardBase n ^ (n - 1) := by
        rw [wittStandardBase_mul_standardSurvival hn]
        ring
  have hgeom := witt_fin_sum_pow_eq_geom (wittStandardBase n) n hbase_ne
  rw [hgeom]
  calc
    standardMutationRate n *
        ((wittStandardBase n ^ n - 1) / (wittStandardBase n - 1)) =
        (standardMutationRate n / (wittStandardBase n - 1)) *
          (wittStandardBase n ^ n - 1) := by ring
    _ = (1 - standardMutationRate n) *
          (wittStandardBase n ^ n - 1) := by rw [hscale]
    _ = (1 - standardMutationRate n) * wittStandardBase n ^ n -
          (1 - standardMutationRate n) := by ring
    _ = wittStandardBase n ^ (n - 1) -
          (1 - standardMutationRate n) := by rw [hpowSurvival]

/-- The standard mutation rate is at most `1/4` from dimension four onward. -/
theorem standardMutationRate_le_quarter {n : ℕ} (hn : 4 ≤ n) :
    standardMutationRate n ≤ (1 / 4 : ℝ) := by
  have hnpos : 0 < n := by omega
  have hnrealpos : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [standardMutationRate, if_neg (Nat.ne_of_gt hnpos)]
  rw [show (n : ℝ)⁻¹ = 1 / (n : ℝ) by simp]
  apply (div_le_iff₀ hnrealpos).2
  nlinarith

/-- Case-1 numerical estimate from Witt's refined proof: after scaling by `1/n`, the
whole geometric envelope costs at most two units. -/
theorem standardMutationRate_mul_wittGeometricEnvelope_le_two
    {n : ℕ} (hn : 4 ≤ n) :
    standardMutationRate n * (∑ i : Fin n, wittStandardBase n ^ i.val) ≤ 2 := by
  have hn2 : 2 ≤ n := by omega
  rw [standardMutationRate_mul_wittGeometricEnvelope_eq hn2]
  have hpow := wittStandardBase_fullPower_le_exp_one n
  have hpquarter := standardMutationRate_le_quarter hn
  have hsurvival : (3 / 4 : ℝ) ≤ 1 - standardMutationRate n := by
    linarith
  have hexp : Real.exp 1 ≤ (11 / 4 : ℝ) := by
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le
  calc
    wittStandardBase n ^ (n - 1) - (1 - standardMutationRate n) ≤
        Real.exp 1 - (3 / 4 : ℝ) := sub_le_sub hpow hsurvival
    _ ≤ (11 / 4 : ℝ) - (3 / 4 : ℝ) := by linarith
    _ = 2 := by norm_num

/-- Consequently the actual sorted Witt coefficients also have scaled total mass at
most two. -/
theorem standardMutationRate_mul_sum_wittStandardPotentialWeight_le_two
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w) :
    standardMutationRate n *
        (∑ i : Fin n, wittStandardPotentialWeight w i) ≤ 2 := by
  have hp0 : 0 ≤ standardMutationRate n :=
    (standardMutationRate_mem_unitInterval_linear (by omega : 2 ≤ n)).1
  have hsum := sum_wittStandardPotentialWeight_le_geometricEnvelope w hmono
  calc
    standardMutationRate n *
        (∑ i : Fin n, wittStandardPotentialWeight w i) ≤
      standardMutationRate n *
        (∑ i : Fin n, wittStandardBase n ^ i.val) :=
          mul_le_mul_of_nonneg_left hsum hp0
    _ ≤ 2 := standardMutationRate_mul_wittGeometricEnvelope_le_two hn

/-- Expected worsening Witt mass carried by accepted C3 masks. -/
noncomputable def wittStandardCaseC3BadMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x,
    mutationMaskWeight p mask *
      (∑ i ∈ oneToZeroFlips x mask, wittStandardPotentialWeight w i)

/-- The C3 worsening Witt mass can be written coordinatewise using the already-promoted
C3 flip-at masses. -/
theorem wittStandardCaseC3BadMass_eq_sum_coordinate_flipMass {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittStandardCaseC3BadMass p w x =
      ∑ i : Fin n,
        if x i = true then
          wittStandardPotentialWeight w i *
            rankLinearCaseC3FlipAtMass p w x i
        else 0 := by
  classical
  unfold wittStandardCaseC3BadMass
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

/-- Before specializing the rate, the expected C3 worsening Witt mass is bounded by
`p * (sum_i g_i)` times accepted C3 mass. -/
theorem wittStandardCaseC3BadMass_le_rate_mul_weightSum_mul_mass
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    wittStandardCaseC3BadMass p w x ≤
      p * (∑ i : Fin n, wittStandardPotentialWeight w i) *
        rankLinearCaseC3AcceptedMass p w x := by
  rw [wittStandardCaseC3BadMass_eq_sum_coordinate_flipMass]
  have hmass0 : 0 ≤ rankLinearCaseC3AcceptedMass p w x :=
    rankLinearCaseC3AcceptedMass_nonneg hp0 hp1 w x
  have hpmass0 : 0 ≤ p * rankLinearCaseC3AcceptedMass p w x :=
    mul_nonneg hp0 hmass0
  calc
    (∑ i : Fin n,
      if x i = true then
        wittStandardPotentialWeight w i * rankLinearCaseC3FlipAtMass p w x i
      else 0) ≤
        ∑ i : Fin n,
          wittStandardPotentialWeight w i *
            (p * rankLinearCaseC3AcceptedMass p w x) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hxi : x i = true
      · rw [if_pos hxi]
        have hflip := rankLinearCaseC3FlipAtMass_le_p_mul_acceptedMass
          hp0 hp1 w hw x i hxi
        exact mul_le_mul_of_nonneg_left hflip
          (wittStandardPotentialWeight_pos w i).le
      · rw [if_neg hxi]
        exact mul_nonneg (wittStandardPotentialWeight_pos w i).le hpmass0
    _ = (∑ i : Fin n, wittStandardPotentialWeight w i) *
          (p * rankLinearCaseC3AcceptedMass p w x) := by
      rw [Finset.sum_mul]
    _ = p * (∑ i : Fin n, wittStandardPotentialWeight w i) *
          rankLinearCaseC3AcceptedMass p w x := by ring

/-- At `p=1/n`, sorted positive linear objectives satisfy the exact bad-mass threshold
needed for nonnegative C3 drift. -/
theorem wittStandardCaseC3BadMass_le_two_mul_acceptedMass_standard
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    wittStandardCaseC3BadMass (standardMutationRate n) w x ≤
      2 * rankLinearCaseC3AcceptedMass (standardMutationRate n) w x := by
  have hp := standardMutationRate_mem_unitInterval_linear (by omega : 2 ≤ n)
  have hbad := wittStandardCaseC3BadMass_le_rate_mul_weightSum_mul_mass
    hp.1 hp.2 w hw x
  have hscale := standardMutationRate_mul_sum_wittStandardPotentialWeight_le_two
    hn w hmono
  have hmass0 :
      0 ≤ rankLinearCaseC3AcceptedMass (standardMutationRate n) w x :=
    rankLinearCaseC3AcceptedMass_nonneg hp.1 hp.2 w x
  calc
    wittStandardCaseC3BadMass (standardMutationRate n) w x ≤
        standardMutationRate n *
          (∑ i : Fin n, wittStandardPotentialWeight w i) *
            rankLinearCaseC3AcceptedMass (standardMutationRate n) w x := hbad
    _ ≤ 2 * rankLinearCaseC3AcceptedMass (standardMutationRate n) w x :=
      mul_le_mul_of_nonneg_right hscale hmass0

/-- In C3 the improving side of the Witt-potential change has total weight at least two. -/
theorem two_le_wittStandardPotentialWeight_sum_zeroToOne_of_caseC3 {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hC3 : IsClassicalLinearCaseC3 x mask) :
    (2 : ℝ) ≤
      ∑ i ∈ zeroToOneFlips x mask, wittStandardPotentialWeight w i := by
  have hcard : 2 ≤ (zeroToOneFlips x mask).card := by
    simpa [IsClassicalLinearCaseC3, zeroToOneFlipCount] using hC3
  calc
    (2 : ℝ) ≤ ((zeroToOneFlips x mask).card : ℝ) := by exact_mod_cast hcard
    _ = ∑ _i ∈ zeroToOneFlips x mask, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ zeroToOneFlips x mask, wittStandardPotentialWeight w i := by
      apply Finset.sum_le_sum
      intro i hi
      exact one_le_wittStandardPotentialWeight w i

/-- Every accepted C3 mask has Witt-potential drop at least two minus its worsening
Witt mass. -/
theorem wittStandardLinearPotential_selected_drop_ge_two_sub_bad_of_caseC3
    {n : ℕ} (w : Fin n → ℝ) (x : BitString n) (mask : MutationMask n)
    (hC3 : IsClassicalLinearCaseC3 x mask)
    (hacc : Accepts (linearFitness w) x (mutateWithMask x mask)) :
    (2 : ℝ) -
        (∑ i ∈ oneToZeroFlips x mask, wittStandardPotentialWeight w i) ≤
      wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask) := by
  rw [wittStandardLinearPotential_selected_drop_of_accepts w x mask hacc,
    flipContribution_sum_eq_flip_sums]
  have hpos := two_le_wittStandardPotentialWeight_sum_zeroToOne_of_caseC3
    w x mask hC3
  linarith

/-- Witt-drift contribution of accepted C3 masks. -/
noncomputable def wittStandardCaseC3AcceptedContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3AcceptedMasks w x,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Witt-drift contribution of all C3 masks. -/
noncomputable def wittStandardCaseC3Contribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC3Masks x,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- Rejected C3 masks vanish, so the full C3 contribution equals the accepted part. -/
theorem wittStandardCaseC3Contribution_eq_accepted {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    wittStandardCaseC3Contribution p w x =
      wittStandardCaseC3AcceptedContribution p w x := by
  classical
  unfold wittStandardCaseC3Contribution wittStandardCaseC3AcceptedContribution
    classicalLinearCaseC3AcceptedMasks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro mask hmask
  by_cases hacc : Accepts (linearFitness w) x (mutateWithMask x mask)
  · simp [hacc]
  · rw [wittStandardLinearPotential_selected_drop_of_rejects w x mask hacc]
    simp [hacc]

/-- Deterministic C3 reduction: contribution is at least `2 * mass - badMass`. -/
theorem two_mul_wittStandardCaseC3AcceptedMass_sub_badMass_le_contribution
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n) :
    2 * rankLinearCaseC3AcceptedMass p w x - wittStandardCaseC3BadMass p w x ≤
      wittStandardCaseC3AcceptedContribution p w x := by
  unfold rankLinearCaseC3AcceptedMass wittStandardCaseC3BadMass
    wittStandardCaseC3AcceptedContribution
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro mask hmask
  have hmem := (mem_classicalLinearCaseC3AcceptedMasks w x mask).mp hmask
  have hdrop := wittStandardLinearPotential_selected_drop_ge_two_sub_bad_of_caseC3
    w x mask hmem.1 hmem.2
  have hwt : 0 ≤ mutationMaskWeight p mask := mutationMaskWeight_nonneg hp0 hp1 mask
  have hmul := mul_le_mul_of_nonneg_left hdrop hwt
  nlinarith

/-- A bad-mass bound by twice accepted mass implies nonnegative aggregate C3 Witt drift. -/
theorem wittStandardCaseC3Contribution_nonneg_of_badMass_le
    {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (x : BitString n)
    (hbad : wittStandardCaseC3BadMass p w x ≤
      2 * rankLinearCaseC3AcceptedMass p w x) :
    0 ≤ wittStandardCaseC3Contribution p w x := by
  rw [wittStandardCaseC3Contribution_eq_accepted]
  have hlower := two_mul_wittStandardCaseC3AcceptedMass_sub_badMass_le_contribution
    hp0 hp1 w x
  linarith

/-- Stage-32 closure of Witt's multi-improvement (C3) branch at standard mutation. -/
theorem wittStandardCaseC3Contribution_nonneg_standard
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w) (x : BitString n) :
    0 ≤ wittStandardCaseC3Contribution (standardMutationRate n) w x := by
  have hp := standardMutationRate_mem_unitInterval_linear (by omega : 2 ≤ n)
  exact wittStandardCaseC3Contribution_nonneg_of_badMass_le
    hp.1 hp.2 w x
    (wittStandardCaseC3BadMass_le_two_mul_acceptedMass_standard
      hn w hw hmono x)


/-! ### Reduction of the Stage-31 remainder after closing C3 -/

/-- Complete Witt-potential contribution of the numerical C2 mask class.  Rejected
masks are harmless because their selected drop is zero. -/
noncomputable def wittStandardCaseC2Contribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ mask ∈ classicalLinearCaseC2Masks x,
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
          (selectedAfterMask (linearFitness w) x mask))

/-- The complete Witt mask sum splits exactly into C1, C2, and C3 pieces. -/
theorem wittStandard_mask_sum_eq_case_sums {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) :
    (∑ mask : MutationMask n,
      mutationMaskWeight p mask *
        (wittStandardLinearPotential w x -
          wittStandardLinearPotential w
            (selectedAfterMask (linearFitness w) x mask))) =
      (∑ mask ∈ classicalLinearCaseC1Masks x,
        mutationMaskWeight p mask *
          (wittStandardLinearPotential w x -
            wittStandardLinearPotential w
              (selectedAfterMask (linearFitness w) x mask))) +
      wittStandardCaseC2Contribution p w x +
      wittStandardCaseC3Contribution p w x := by
  classical
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (wittStandardLinearPotential w x -
        wittStandardLinearPotential w
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

/-- For positive weights, C1 vanishes, so total Witt drift is exactly C2 plus C3. -/
theorem wittStandardLinear_drift_eq_caseC2_add_caseC3 {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (x : BitString n) :
    driftAt (onePlusOneTransition p (linearFitness w))
        (wittStandardLinearPotential w) x =
      wittStandardCaseC2Contribution p w x +
        wittStandardCaseC3Contribution p w x := by
  rw [wittStandardLinear_drift_eq_mask_sum]
  rw [wittStandard_mask_sum_eq_case_sums]
  rw [wittStandard_caseC1_contribution_eq_zero (p := p) w hw x]
  simp

/-- What remains inside C2 after removing the already-proved zero-singleton term. -/
noncomputable def wittStandardCaseC2RemainderContribution {n : ℕ}
    (p : ℝ) (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  wittStandardCaseC2Contribution p w x -
    linearSingletonRate n p * wittStandardLinearPotential w x

/-- After the C1/C2/C3 partition, the Stage-31 remainder is exactly the C2 remainder
plus the C3 contribution. -/
theorem wittStandardRemainderContribution_eq_caseC2Remainder_add_caseC3
    {n : ℕ} {p : ℝ}
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) (x : BitString n) :
    wittStandardRemainderContribution p w x =
      wittStandardCaseC2RemainderContribution p w x +
        wittStandardCaseC3Contribution p w x := by
  have hsingle := wittStandardLinear_drift_eq_singleton_add_remainder
    (p := p) w hw x
  have hcases := wittStandardLinear_drift_eq_caseC2_add_caseC3 p w hw x
  unfold wittStandardCaseC2RemainderContribution
  linarith

/-- The sole aggregate certificate remaining after Stage 32: C2 must contribute at
least the already-extracted zero-singleton term.  Stage 31 already proved that C2B
masks have zero Witt drop, so the substantive content is Witt's C2A/Subcase-2.2.2
geometric cancellation. -/
def HasWittStandardCaseC2RemainderNonnegativity {n : ℕ}
    (w : Fin n → ℝ) : Prop :=
  ∀ x : BitString n,
    0 ≤ wittStandardCaseC2RemainderContribution
      (standardMutationRate n) w x

/-- Closing the C2 remainder now closes the complete Stage-31 remainder, because Stage
32 has discharged C3. -/
theorem hasWittStandardRemainderNonnegativity_of_caseC2
    {n : ℕ} (hn : 4 ≤ n)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w)
    (hmono : NonincreasingLinearWeights w)
    (hC2 : HasWittStandardCaseC2RemainderNonnegativity w) :
    HasWittStandardRemainderNonnegativity w := by
  intro x
  rw [wittStandardRemainderContribution_eq_caseC2Remainder_add_caseC3
    (p := standardMutationRate n) w hw x]
  exact add_nonneg (hC2 x)
    (wittStandardCaseC3Contribution_nonneg_standard hn w hw hmono x)

end ECRuntime
