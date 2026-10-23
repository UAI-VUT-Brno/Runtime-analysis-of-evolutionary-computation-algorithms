import ECRuntime.LeadingOnesStationaryRootExists
import ECRuntime.LeadingOnesStationaryAntitone
import ECRuntime.LeadingOnesScaledRate
import ECRuntime.WittMutationRateAsymptotics
import Mathlib

open scoped BigOperators
open Filter

namespace ECRuntime

/-!
Candidate 111 (A2): sharp fixed-rate LeadingOnes asymptotics.
Source: Boettcher--Doerr--Neumann (PPSN 2010), Optimal Fixed and Adaptive
Mutation Rates for the LeadingOnes Problem. Only FIXED rates are treated;
there is no adaptive-rate theorem or numerical axiom.
-/

/-- Leading coefficient in the scaled fixed-rate regime p=c/n. -/
noncomputable def leadingOnesFixedRateCoefficient (c : Real) : Real :=
  (Real.exp c - 1) / (2 * c ^ 2)

/-- Local geometric-series identity; its proof uses the same `Fin` reindexing
as the already verified standard-rate LeadingOnes closed form. -/
private theorem leadingOnes_fin_sum_pow_mul_sub_one (r : Real) (n : Nat) :
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

/-- Finite geometric closed form, valid also for dimension zero. -/
private theorem leadingOnes_uniform_formula_geometric
    (n : Nat) (p : Real) (hp : p ≠ 0) (hb : 1 - p ≠ 0) :
    leadingOnesUniformExpectedRuntimeFormula n p =
      ((1 - p) / (2 * p ^ 2)) * (((1 - p)⁻¹) ^ n - 1) := by
  let b : Real := 1 - p
  have hr : b⁻¹ ≠ 1 := by
    intro he
    have hbone : b = 1 := by
      have hi := congrArg (fun z : Real => z⁻¹) he
      simpa using hi
    exact hp (by dsimp [b] at hbone; linarith)
  have hterm (i : Fin n) :
      (p * (1 - p) ^ i.val)⁻¹ = p⁻¹ * (b⁻¹) ^ i.val := by
    dsimp [b]
    rw [mul_inv_rev, inv_pow]
    ring
  have hgeom :
      (∑ i : Fin n, (b⁻¹) ^ i.val) =
        (((b⁻¹) ^ n - 1) / (b⁻¹ - 1)) := by
    rw [eq_div_iff (sub_ne_zero.mpr hr)]
    exact leadingOnes_fin_sum_pow_mul_sub_one (b⁻¹) n
  have hratio : b⁻¹ - 1 = p / b := by
    dsimp [b]
    field_simp [hb]
    ring
  calc
    leadingOnesUniformExpectedRuntimeFormula n p =
        (1 / 2 : Real) * ∑ i : Fin n, p⁻¹ * (b⁻¹) ^ i.val := by
      rw [leadingOnesUniformExpectedRuntimeFormula_eq]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (1 / 2 : Real) * p⁻¹ * ∑ i : Fin n, (b⁻¹) ^ i.val := by
      calc
        (1 / 2 : Real) * (∑ i : Fin n, p⁻¹ * (b⁻¹) ^ i.val) =
            ∑ i : Fin n, ((1 / 2 : Real) * p⁻¹) * (b⁻¹) ^ i.val := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun i _ => by ring)
        _ = ((1 / 2 : Real) * p⁻¹) * ∑ i : Fin n, (b⁻¹) ^ i.val := by
              rw [Finset.mul_sum]
    _ = ((1 - p) / (2 * p ^ 2)) * (((1 - p)⁻¹) ^ n - 1) := by
      rw [hgeom, hratio]
      dsimp [b]
      field_simp [hp, hb]

/-- Limit of the exact, already-certified finite-n expectation formula for
all fixed c>0 (not restricted to c≤1). Terms at small n may be degenerate;
the atTop limit only concerns sufficiently large n. -/
theorem leadingOnes_scaled_fixedRate_limit
    (c : Real) (hc : 0 < c) :
    Tendsto
      (fun n : Nat =>
        leadingOnesUniformExpectedRuntimeFormula n (scaledMutationRate c n) /
          (n : Real) ^ 2)
      atTop (nhds (leadingOnesFixedRateCoefficient c)) := by
  -- Work with the geometric closed form of the already certified finite sum.
  -- The exponential limit below is the same one used in the Witt rate branch.
  have hraw : Tendsto
      (fun n : Nat => (1 - c / (n : Real)) ^ n)
      atTop (nhds (Real.exp (-c))) := by
    simpa [sub_eq_add_neg, neg_div] using
      (Real.tendsto_one_add_div_pow_exp (-c))
  have hrawInv : Tendsto
      (fun n : Nat => ((1 - c / (n : Real))⁻¹) ^ n)
      atTop (nhds (Real.exp c)) := by
    have h := hraw.inv₀ (Real.exp_ne_zero (-c))
    simpa only [inv_pow, Real.exp_neg, inv_inv] using h
  have hpow : Tendsto
      (fun n : Nat => ((1 - scaledMutationRate c n)⁻¹) ^ n)
      atTop (nhds (Real.exp c)) := by
    apply hrawInv.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : Nat)] with n hn
    rw [scaledMutationRate_eq_div_of_pos hn]
  have hbase : Tendsto
      (fun n : Nat => 1 - scaledMutationRate c n)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub (scaledMutationRate_tendsto_zero c))
  have hdiff : Tendsto
      (fun n : Nat => ((1 - scaledMutationRate c n)⁻¹) ^ n - 1)
      atTop (nhds (Real.exp c - 1)) := by
    simpa using (hpow.sub tendsto_const_nhds)
  have hprod : Tendsto
      (fun n : Nat => (1 - scaledMutationRate c n) *
        (((1 - scaledMutationRate c n)⁻¹) ^ n - 1))
      atTop (nhds (Real.exp c - 1)) := by
    simpa using (hbase.mul hdiff)
  have hlim : Tendsto
      (fun n : Nat => ((1 - scaledMutationRate c n) / (2 * c ^ 2)) *
        (((1 - scaledMutationRate c n)⁻¹) ^ n - 1))
      atTop (nhds (leadingOnesFixedRateCoefficient c)) := by
    convert hprod.const_mul ((2 * c ^ 2)⁻¹) using 1 <;>
      simp [leadingOnesFixedRateCoefficient, div_eq_mul_inv, mul_comm,
        mul_left_comm, mul_assoc]
  apply hlim.congr'
  obtain ⟨N, hN⟩ := exists_nat_gt c
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have hcn : c < (n : Real) :=
    lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hnpos : 0 < n := by
    have hnr : (0 : Real) < (n : Real) := lt_trans hc hcn
    exact_mod_cast hnr
  have hnreal : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hnpos)
  have hp : scaledMutationRate c n ≠ 0 :=
    ne_of_gt (scaledMutationRate_pos hc hnpos)
  have hbaseNonzero : 1 - scaledMutationRate c n ≠ 0 :=
    ne_of_gt (sub_pos.mpr (scaledMutationRate_lt_one hnpos hcn))
  have hform := leadingOnes_uniform_formula_geometric n
    (scaledMutationRate c n) hp hbaseNonzero
  have hcoeff :
      ((1 - scaledMutationRate c n) / (2 * (scaledMutationRate c n) ^ 2)) /
          (n : Real) ^ 2 =
        (1 - scaledMutationRate c n) / (2 * c ^ 2) := by
    rw [scaledMutationRate_eq_div_of_pos hnpos]
    field_simp [hc.ne', hnreal]
  symm
  calc
    leadingOnesUniformExpectedRuntimeFormula n (scaledMutationRate c n) /
        (n : Real) ^ 2 =
        (((1 - scaledMutationRate c n) / (2 * (scaledMutationRate c n) ^ 2)) /
          (n : Real) ^ 2) *
          (((1 - scaledMutationRate c n)⁻¹) ^ n - 1) := by
      rw [hform]
      ring
    _ = ((1 - scaledMutationRate c n) / (2 * c ^ 2)) *
          (((1 - scaledMutationRate c n)⁻¹) ^ n - 1) := by
      rw [hcoeff]

/-- The exact derivative, exposed separately for the subsequent
uniqueness/monotonicity argument. No numerical root approximation is used. -/
private theorem stage111_fixedRate_derivative_formula (c : Real) (hc : 0 < c) :
    deriv leadingOnesFixedRateCoefficient c =
      ((c - 2) * Real.exp c + 2) / (2 * c ^ 3) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hden0 : 2 * c ^ 2 ≠ (0 : Real) := by positivity
  have hnum : HasDerivAt (fun z : Real => Real.exp z - 1)
      (Real.exp c) c := by
    simpa using (Real.hasDerivAt_exp c).sub_const (1 : Real)
  have hden : HasDerivAt (fun z : Real => 2 * z ^ 2)
      (4 * c) c := by
    have h := (((hasDerivAt_id c).pow 2).const_mul (2 : Real))
    convert h using 1
    all_goals
      first
      | rfl
      | norm_num [id_eq]; ring
  have hquot : deriv leadingOnesFixedRateCoefficient c =
      (Real.exp c * (2 * c ^ 2) - (Real.exp c - 1) * (4 * c)) /
        (2 * c ^ 2) ^ 2 := by
    have hderiv := (hnum.div hden hden0).deriv
    change deriv leadingOnesFixedRateCoefficient c = _ at hderiv
    exact hderiv
  have hnormalized :
      (Real.exp c * (2 * c ^ 2) - (Real.exp c - 1) * (4 * c)) /
        (2 * c ^ 2) ^ 2 =
      ((c - 2) * Real.exp c + 2) / (2 * c ^ 3) := by
    field_simp [hc0]
    ring
  rw [hquot, hnormalized]

/-- A positive stationary point c solves (2-c)*exp(c)=2. -/
theorem leadingOnes_fixedRate_stationary_iff
    (c : Real) (hc : 0 < c) :
    deriv leadingOnesFixedRateCoefficient c = 0 ↔
      (2 - c) * Real.exp c = 2 := by
  have hdenpos : 0 < 2 * c ^ 3 := by positivity
  rw [stage111_fixedRate_derivative_formula c hc]
  have hdiv (u : Real) : u / (2 * c ^ 3) = 0 ↔ u = 0 := by
    constructor
    · intro hu
      calc
        u = (u / (2 * c ^ 3)) * (2 * c ^ 3) := by
          field_simp [ne_of_gt hdenpos]
        _ = 0 := by simp [hu]
    · intro hu
      simp [hu]
  constructor
  · intro hzero
    have hnumzero : (c - 2) * Real.exp c + 2 = 0 := (hdiv _).mp hzero
    linarith
  · intro hstationary
    apply (hdiv _).mpr
    linarith

/-- The stationary-point equation is strictly on the positive side at c=1.
The rigorous inequality uses Mathlib's bound exp(1)>2, not a numerical axiom. -/
private theorem stage111_stationary_endpoint_one :
    2 < (2 - (1 : Real)) * Real.exp 1 := by
  have hfactor : (2 - (1 : Real)) * Real.exp 1 = Real.exp 1 := by ring
  rw [hfactor]
  exact Real.exp_one_gt_two

/-- At c=2 the stationary-point expression has already crossed 2. -/
private theorem stage111_stationary_endpoint_two :
    (2 - (2 : Real)) * Real.exp 2 < 2 := by
  simp

/-- The stationary equation changes sign between 1 and 2; these
are exact analytic inequalities, not floating-point approximations. -/
private theorem stage111_stationary_equation_pos_at_one :
    0 < (2 - (1 : Real)) * Real.exp 1 - 2 := by
  have h := Real.exp_one_gt_two
  nlinarith

private theorem stage111_stationary_equation_neg_at_two :
    (2 - (2 : Real)) * Real.exp 2 - 2 < 0 := by
  norm_num

/-- Continuity of the equation used to locate the optimizing rate. -/
private theorem stage111_stationary_equation_continuous :
    Continuous (fun c : Real => (2 - c) * Real.exp c - 2) := by
  fun_prop

/-- Below rate 1, the stationary expression stays strictly above 2.
The elementary bound `1+c ≤ exp c` suffices on this interval. -/
private theorem stage111_stationary_above_two_below_one
    (c : Real) (hc : 0 < c) (hc1 : c < 1) :
    2 < (2 - c) * Real.exp c := by
  have hbound := Real.add_one_le_exp c
  have hfactor : 0 ≤ 2 - c := by linarith
  have hmul := mul_le_mul_of_nonneg_left hbound hfactor
  have hstrict : 0 < c * (1 - c) :=
    mul_pos hc (sub_pos.mpr hc1)
  nlinarith

/-- No nonnegative rate at or beyond 2 solves the stationary equation. -/
private theorem stage111_stationary_below_two_at_least_two
    (c : Real) (hc2 : 2 ≤ c) :
    (2 - c) * Real.exp c < 2 := by
  have hexp : 0 ≤ Real.exp c := le_of_lt (Real.exp_pos c)
  have hfac : 2 - c ≤ 0 := by linarith
  have hprod := mul_nonpos_of_nonpos_of_nonneg hfac hexp
  linarith

/-- A positive stationary rate, if one exists, must lie in (1,2).
This is independent of the still-open existence/uniqueness proof. -/
private theorem stage111_stationary_inside_interval
    (c : Real) (hc : 0 < c)
    (hstationary : (2 - c) * Real.exp c = 2) :
    1 < c ∧ c < 2 := by
  constructor
  · by_contra hnot
    have hc1 : c ≤ 1 := le_of_not_gt hnot
    rcases lt_or_eq_of_le hc1 with hlt | heq
    · have hstrict := stage111_stationary_above_two_below_one c hc hlt
      linarith
    · subst c
      have hstrict := stage111_stationary_endpoint_one
      norm_num at hstationary
      linarith
  · by_contra hnot
    have hc2 : 2 ≤ c := le_of_not_gt hnot
    have hstrict := stage111_stationary_below_two_at_least_two c hc2
    linarith

/-- The derivative of the stationary-point expression is `(1-c) exp(c)`.
For `c>1` it is negative; a mean-value/strict-antitonicity argument on
`(1,2)` would then establish uniqueness of the stationary point. -/
private theorem stage111_stationary_expression_derivative (c : Real) :
    deriv (fun x : Real => (2 - x) * Real.exp x) c =
      (1 - c) * Real.exp c := by
  have hsub : HasDerivAt (fun x : Real => (2 : Real) - x) (-1) c := by
    convert (hasDerivAt_id c).const_sub (2 : Real) using 1
    all_goals rfl
  have hprod := hsub.mul (Real.hasDerivAt_exp c)
  have hprod_deriv :
      deriv (fun x : Real => (2 - x) * Real.exp x) c =
        -1 * Real.exp c + (2 - c) * Real.exp c := by
    convert hprod.deriv using 1
    all_goals rfl
  calc
    deriv (fun x : Real => (2 - x) * Real.exp x) c =
        -1 * Real.exp c + (2 - c) * Real.exp c := hprod_deriv
    _ = (1 - c) * Real.exp c := by ring

/-- The derivative of the stationary expression is strictly negative
throughout the interior interval `(1,2)`. This is only a local sign
statement, not yet global optimality. -/
private theorem stage111_stationary_expression_derivative_neg
    (c : Real) (hc : 1 < c) :
    deriv (fun x : Real => (2 - x) * Real.exp x) c < 0 := by
  rw [stage111_stationary_expression_derivative]
  exact mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos c)

/-- The objective coefficient decreases strictly for 0 < c ≤ 1.
This gives a certified-sign proof attempt on the entire left region,
independent of establishing existence of the optimal stationary rate. -/
private theorem stage111_coefficient_derivative_negative_below_one
    (c : Real) (hc : 0 < c) (hc1 : c ≤ 1) :
    deriv leadingOnesFixedRateCoefficient c < 0 := by
  have hstat : 2 < (2 - c) * Real.exp c := by
    rcases lt_or_eq_of_le hc1 with hlt | heq
    · exact stage111_stationary_above_two_below_one c hc hlt
    · subst c
      exact stage111_stationary_endpoint_one
  have hnum : (c - 2) * Real.exp c + 2 < 0 := by
    nlinarith [hstat]
  rw [stage111_fixedRate_derivative_formula c hc]
  exact div_neg_of_neg_of_pos hnum (by positivity)

/-- The objective coefficient increases strictly for c ≥ 2.
The unique positive minimizer, if shown to exist, must therefore
lie in the remaining compact interval. -/
private theorem stage111_coefficient_derivative_positive_above_two
    (c : Real) (hc : 2 ≤ c) :
    0 < deriv leadingOnesFixedRateCoefficient c := by
  have hc0 : 0 < c := by linarith
  have hexp : 0 < Real.exp c := Real.exp_pos c
  have hnum : 0 < (c - 2) * Real.exp c + 2 := by
    have hm : 0 ≤ (c - 2) * Real.exp c :=
      mul_nonneg (by linarith) (le_of_lt hexp)
    linarith
  rw [stage111_fixedRate_derivative_formula c hc0]
  exact div_pos hnum (by positivity)

/-- For any positive rate, being above the stationary threshold makes
the fixed-rate LeadingOnes coefficient decrease locally. This is the
remaining sign implication needed on the left side of the optimizer. -/
private theorem stage111_derivative_negative_of_stationary_above
    (c : Real) (hc : 0 < c)
    (h : 2 < (2 - c) * Real.exp c) :
    deriv leadingOnesFixedRateCoefficient c < 0 := by
  have hnum : (c - 2) * Real.exp c + 2 < 0 := by
    nlinarith [h]
  rw [stage111_fixedRate_derivative_formula c hc]
  exact div_neg_of_neg_of_pos hnum (by positivity)

/-- Dually, below the stationary threshold the coefficient is locally
increasing. Existence and uniqueness of the crossing remain open. -/
private theorem stage111_derivative_positive_of_stationary_below
    (c : Real) (hc : 0 < c)
    (h : (2 - c) * Real.exp c < 2) :
    0 < deriv leadingOnesFixedRateCoefficient c := by
  have hnum : 0 < (c - 2) * Real.exp c + 2 := by
    nlinarith [h]
  rw [stage111_fixedRate_derivative_formula c hc]
  exact div_pos hnum (by positivity)

/-- The fixed-rate LeadingOnes leading coefficient is strictly positive
for every positive rate. This is independent of the stationary-rate
existence or global optimality obligation. -/
private theorem stage111_fixedRate_coefficient_positive
    (c : Real) (hc : 0 < c) :
    0 < leadingOnesFixedRateCoefficient c := by
  have hexp : 1 + c ≤ Real.exp c := by
    simpa only [add_comm] using (Real.add_one_le_exp c)
  have hnum : 0 < Real.exp c - 1 := by linarith
  exact div_pos hnum (by positivity)

/-- Strict antitonicity beyond rate 1 implies uniqueness of any positive
stationary solution. This isolates the exact Stage 152 dependency, without
postulating its conclusion or changing the approved global optimum theorem. -/
private theorem stage111_stationary_unique_of_antitone
    (hanti : StrictAntiOn (fun c : Real => (2 - c) * Real.exp c) (Set.Ioi 1))
    (c d : Real) (hc : 1 < c) (hd : 1 < d)
    (hrootc : (2 - c) * Real.exp c = 2)
    (hrootd : (2 - d) * Real.exp d = 2) : c = d := by
  rcases lt_trichotomy c d with hlt | heq | hgt
  · have hs := hanti (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr hd) hlt
    change (2 - d) * Real.exp d < (2 - c) * Real.exp c at hs
    rw [hrootd, hrootc] at hs
    exact False.elim ((lt_irrefl (2 : Real)) hs)
  · exact heq
  · have hs := hanti (Set.mem_Ioi.mpr hd) (Set.mem_Ioi.mpr hc) hgt
    change (2 - c) * Real.exp c < (2 - d) * Real.exp d at hs
    rw [hrootc, hrootd] at hs
    exact False.elim ((lt_irrefl (2 : Real)) hs)

/-- The now independently compiler-clean Stage 152 argument eliminates the
conditional strict-antitonicity premise: two roots above 1 must coincide.
This is a proved uniqueness ingredient, not yet global minimization. -/
private theorem stage111_stationary_unique
    (c d : Real) (hc : 1 < c) (hd : 1 < d)
    (hrootc : (2 - c) * Real.exp c = 2)
    (hrootd : (2 - d) * Real.exp d = 2) : c = d := by
  exact stage111_stationary_unique_of_antitone
    proposed_leadingOnes_stationaryFactor_strictAntiOn c d hc hd hrootc hrootd

/-- The certified Stage 152 strict antitonicity, together with the
classical exponential lower bound on (0,1], determines the sign of the
stationary expression to the LEFT of any root in (1,2). -/
private theorem stage111_stationary_factor_above_left_of_root
    (r c : Real) (hr : 1 < r)
    (hroot : (2 - r) * Real.exp r = 2)
    (hc : 0 < c) (hcr : c < r) :
    2 < (2 - c) * Real.exp c := by
  by_cases hcle : c ≤ 1
  · rcases lt_or_eq_of_le hcle with hlt | heq
    · exact stage111_stationary_above_two_below_one c hc hlt
    · subst c
      exact stage111_stationary_endpoint_one
  · have hc1 : 1 < c := lt_of_not_ge hcle
    have hanti := proposed_leadingOnes_stationaryFactor_strictAntiOn
      (Set.mem_Ioi.mpr hc1) (Set.mem_Ioi.mpr hr) hcr
    change (2 - r) * Real.exp r < (2 - c) * Real.exp c at hanti
    rw [hroot] at hanti
    exact hanti

/-- To the RIGHT of a stationary root, the stationary expression falls
strictly below 2. This holds even beyond rate 2. -/
private theorem stage111_stationary_factor_below_right_of_root
    (r c : Real) (hr : 1 < r)
    (hroot : (2 - r) * Real.exp r = 2)
    (hrc : r < c) :
    (2 - c) * Real.exp c < 2 := by
  have hc1 : 1 < c := lt_trans hr hrc
  have hanti := proposed_leadingOnes_stationaryFactor_strictAntiOn
    (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hc1) hrc
  change (2 - c) * Real.exp c < (2 - r) * Real.exp r at hanti
  rw [hroot] at hanti
  exact hanti

/-- The derivative of the fixed-rate coefficient is strictly negative
before any positive stationary root. -/
private theorem stage111_derivative_neg_left_of_root
    (r c : Real) (hr : 1 < r)
    (hroot : (2 - r) * Real.exp r = 2)
    (hc : 0 < c) (hcr : c < r) :
    deriv leadingOnesFixedRateCoefficient c < 0 := by
  exact stage111_derivative_negative_of_stationary_above c hc
    (stage111_stationary_factor_above_left_of_root r c hr hroot hc hcr)

/-- The derivative becomes strictly positive after that root. -/
private theorem stage111_derivative_pos_right_of_root
    (r c : Real) (hr : 1 < r)
    (hroot : (2 - r) * Real.exp r = 2)
    (hrc : r < c) :
    0 < deriv leadingOnesFixedRateCoefficient c := by
  exact stage111_derivative_positive_of_stationary_below c
    (lt_trans (by norm_num : (0 : Real) < 1) (lt_trans hr hrc))
    (stage111_stationary_factor_below_right_of_root r c hr hroot hrc)

/-- Conditional global optimality of any positive stationary root. This
is entirely independent of the still-unverified intermediate-value theorem:
once a root is supplied, the derivative signs and the mean-value criterion
force it to minimize the coefficient on the whole positive half-line. -/
private theorem stage111_global_minimum_of_stationary_root
    (r : Real) (hr : 1 < r)
    (hroot : (2 - r) * Real.exp r = 2) :
    ∀ d : Real, 0 < d →
      leadingOnesFixedRateCoefficient r ≤
        leadingOnesFixedRateCoefficient d := by
  have hcont (x : Real) (hx : 0 < x) :
      ContinuousAt leadingOnesFixedRateCoefficient x := by
    have hden : (2 : Real) * x ^ 2 ≠ 0 := by positivity
    have hnumcont : ContinuousAt (fun y : Real => Real.exp y - 1) x := by
      fun_prop
    have hdencont : ContinuousAt (fun y : Real => 2 * y ^ 2) x := by
      fun_prop
    exact hnumcont.div hdencont hden
  intro d hd
  rcases lt_trichotomy d r with hlt | heq | hgt
  · have hanti : StrictAntiOn leadingOnesFixedRateCoefficient
        (Set.Icc d r) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc d r)
      · intro x hx
        have hxpos : 0 < x :=
          lt_of_lt_of_le hd (Set.mem_Icc.mp hx).1
        exact (hcont x hxpos).continuousWithinAt
      · intro x hx
        have hxi : x ∈ Set.Ioo d r := by
          simpa only [interior_Icc] using hx
        exact stage111_derivative_neg_left_of_root r x hr hroot
          (lt_trans hd hxi.1) hxi.2
    have hmin := hanti (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hlt⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hlt, le_rfl⟩) hlt
    exact le_of_lt hmin
  · subst d
    exact le_refl _
  · have hmono : StrictMonoOn leadingOnesFixedRateCoefficient
        (Set.Icc r d) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc r d)
      · intro x hx
        have hxpos : 0 < x :=
          lt_trans (by norm_num : (0 : Real) < 1)
            (lt_of_lt_of_le hr (Set.mem_Icc.mp hx).1)
        exact (hcont x hxpos).continuousWithinAt
      · intro x hx
        have hxi : x ∈ Set.Ioo r d := by
          simpa only [interior_Icc] using hx
        exact stage111_derivative_pos_right_of_root r x hr hroot hxi.1
    have hmin := hmono (Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hgt⟩)
      (Set.mem_Icc.mpr ⟨le_of_lt hgt, le_rfl⟩) hgt
    exact le_of_lt hmin

/-- There is a unique stationary point c in (1,2); it globally minimizes
F(c) for all positive c. There is no numerical approximation in this claim. -/
theorem leadingOnes_fixedRate_unique_optimum :
    ∃ c : Real,
      1 < c ∧ c < 2 ∧
      (2 - c) * Real.exp c = 2 ∧
      (∀ d : Real, 0 < d →
        leadingOnesFixedRateCoefficient c ≤
          leadingOnesFixedRateCoefficient d) ∧
      (∀ d : Real, 1 < d → d < 2 →
        (2 - d) * Real.exp d = 2 → d = c) := by
  obtain ⟨c, hc1, hc2, hroot⟩ :=
    proposed_leadingOnes_stationaryRoot_exists
  refine ⟨c, hc1, hc2, hroot, ?_, ?_⟩
  · exact stage111_global_minimum_of_stationary_root c hc1 hroot
  · intro d hd1 _hd2 hdroot
    exact stage111_stationary_unique d c hd1 hc1 hdroot hroot

end ECRuntime
