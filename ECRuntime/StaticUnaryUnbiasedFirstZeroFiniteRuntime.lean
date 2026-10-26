import ECRuntime.StaticUnaryUnbiasedFirstZeroPathVisits
import ECRuntime.HittingTime
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

section FiniteRuntimeDecidability
attribute [local instance] Classical.propDecidable

/-!
# Stage 105: finite-horizon runtime / first-zero visitation (APPROVED PROOF CANDIDATE)

The user approved all nine theorem statements on 21 October 2026. The approved
signatures are frozen; this is the first proof-development batch. The module
remains excluded from the public root and is not claimed compiler-certified.
Strict Lean verification and a separate promotion approval remain mandatory.

Stage 104 identifies cumulative entry mass with actual finite-path visitation.
Stage 105 bridges the finite-time probability of being nonoptimal to the
existing Bellman truncated first-hitting-time runtime and then applies the
hazard-weighted visit cap. The new absorption argument is stated explicitly:
without an absorbing optimum, sums of nonoptimal marginals need not equal
truncated first-hitting-time expectations.

No infinite-horizon limit, bound uniform in dimension, or sharp general-linear
runtime theorem is asserted. The model is the superincreasing/BinVal case.
-/

/-- The all-ones target, a singleton even in dimension zero. -/
def firstZeroOptimalSet {n : Nat} : Set (BitString n) :=
  {z | firstZeroAllOnes z}

/-- Expected number of nonoptimal observations at times `0, ..., T-1`.
Its equivalence to a truncated hitting-time expectation requires absorption. -/
noncomputable def firstZeroFiniteRuntimeMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) : Real :=
  ∑ t ∈ Finset.range T, firstZeroNonoptimalMass law w x t

/-- The finite-horizon upper budget expressed using actual visitation masses
and the exact state-independent first-zero exit hazards. -/
noncomputable def firstZeroFiniteVisitBudget {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) : Real :=
  ∑ i : Fin n,
    firstZeroTrajectoryVisitMass law w x i T /
      law.maskEventMass (lowestMaskEvent i)

/-- (1/9) Under the true superincreasing elitist kernel, a positive-mass
transition out of the all-ones optimum is impossible. -/
theorem firstZeroOptimum_transition_supported {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (z y : BitString n) (hz : firstZeroAllOnes z)
    (htrans : 0 < (law.transition (linearFitness w)) z y) :
    firstZeroAllOnes y := by
  classical
  have hselected (mask : MutationMask n) :
      firstZeroAllOnes (selectedAfterMask (linearFitness w) z mask) := by
    intro j
    have hprefix : firstZeroCorrectPrefixThrough z j := by
      intro k _
      exact hz k
    exact firstZeroCorrectPrefixThrough_selected_preserves
      w hw z j hprefix mask j (le_refl j)
  by_contra hnot
  have hzero : (law.transition (linearFitness w)) z y = 0 := by
    change pushforwardWeight law.weight
      (selectedAfterMask (linearFitness w) z) y = 0
    unfold pushforwardWeight
    apply Finset.sum_eq_zero
    intro mask _
    have hne : selectedAfterMask (linearFitness w) z mask ≠ y := by
      intro heq
      exact hnot (heq ▸ hselected mask)
    simp [hne]
  exact (ne_of_gt htrans) hzero

/-- (2/9) Zero observations have zero truncated runtime mass. -/
theorem firstZeroFiniteRuntimeMass_zero {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) :
    firstZeroFiniteRuntimeMass law w x 0 = 0 := by
  simp [firstZeroFiniteRuntimeMass]

/-- (3/9) The additional horizon step costs exactly its nonoptimal marginal. -/
theorem firstZeroFiniteRuntimeMass_succ {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) :
    firstZeroFiniteRuntimeMass law w x (T + 1) =
      firstZeroFiniteRuntimeMass law w x T +
        firstZeroNonoptimalMass law w x T := by
  simp [firstZeroFiniteRuntimeMass, Finset.sum_range_succ]

/-- (4/9) Expected nonoptimal-observation count is nonnegative for any law. -/
theorem firstZeroFiniteRuntimeMass_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) :
    0 ≤ firstZeroFiniteRuntimeMass law w x T := by
  unfold firstZeroFiniteRuntimeMass
  apply Finset.sum_nonneg
  intro t _
  rw [← firstZeroGlobalOccupationMass_eq_nonoptimal law w x t]
  unfold firstZeroGlobalOccupationMass
  exact Finset.sum_nonneg
    (fun i _ => firstZeroOccupationMass_nonneg law w x i t)

/-- (5/9) Increasing the finite horizon never reduces expected runtime mass. -/
theorem firstZeroFiniteRuntimeMass_mono {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) :
    firstZeroFiniteRuntimeMass law w x T ≤
      firstZeroFiniteRuntimeMass law w x (T + 1) := by
  rw [firstZeroFiniteRuntimeMass_succ]
  exact le_add_of_nonneg_right (by
    rw [← firstZeroGlobalOccupationMass_eq_nonoptimal law w x T]
    unfold firstZeroGlobalOccupationMass
    exact Finset.sum_nonneg
      (fun i _ => firstZeroOccupationMass_nonneg law w x i T))

/-- (6/9) The finite runtime mass is exactly Stage 103's global occupation
summed over the same horizon; no fitness restriction is needed. -/
theorem firstZeroFiniteRuntimeMass_eq_globalOccupation {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) :
    firstZeroFiniteRuntimeMass law w x T =
      ∑ t ∈ Finset.range T, firstZeroGlobalOccupationMass law w x t := by
  unfold firstZeroFiniteRuntimeMass
  apply Finset.sum_congr rfl
  intro t _
  exact (firstZeroGlobalOccupationMass_eq_nonoptimal law w x t).symm

/-! ### Forward-marginal/Bellman bridge

The state-mass recursion is written with the *terminal* transition on the
right. The following finite Chapman--Kolmogorov identity moves the initial
transition to the left. It is proved by finite-sum interchange, rather than
by assuming a time-homogeneous Markov law from an external measure model.
-/

private theorem firstZeroStateMass_from_start {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real) :
    ∀ (t : Nat) (x z : BitString n),
      firstZeroStateMass law w x (t + 1) z =
        ∑ y : BitString n,
          (law.transition (linearFitness w)) x y *
            firstZeroStateMass law w y t z := by
  let P := law.transition (linearFitness w)
  intro t
  induction t with
  | zero =>
      intro x z
      change (∑ y : BitString n,
        (if y = x then (1 : Real) else 0) * P y z) =
        ∑ y : BitString n, P x y * (if z = y then (1 : Real) else 0)
      simp [mul_ite, ite_mul, eq_comm]
  | succ t ih =>
      intro x z
      change (∑ u : BitString n,
        firstZeroStateMass law w x (t + 1) u * P u z) =
        ∑ y : BitString n, P x y *
          (∑ u : BitString n,
            firstZeroStateMass law w y t u * P u z)
      calc
        (∑ u : BitString n,
          firstZeroStateMass law w x (t + 1) u * P u z) =
            ∑ u : BitString n, ∑ y : BitString n,
              (P x y * firstZeroStateMass law w y t u) * P u z := by
                apply Finset.sum_congr rfl
                intro u _
                rw [ih x u, Finset.sum_mul]
        _ = ∑ y : BitString n, ∑ u : BitString n,
              (P x y * firstZeroStateMass law w y t u) * P u z :=
                Finset.sum_comm
        _ = ∑ y : BitString n, P x y *
              (∑ u : BitString n,
                firstZeroStateMass law w y t u * P u z) := by
                apply Finset.sum_congr rfl
                intro y _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro u _
                ring

/-- A finite-event marginal also admits the initial-transition expansion. -/
private theorem firstZeroNonoptimalMass_from_start {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (t : Nat) :
    firstZeroNonoptimalMass law w x (t + 1) =
      ∑ y : BitString n,
        (law.transition (linearFitness w)) x y *
          firstZeroNonoptimalMass law w y t := by
  classical
  let P := law.transition (linearFitness w)
  let S : Set (BitString n) := {z | ¬ firstZeroAllOnes z}
  change (∑ z : BitString n,
      S.indicator (firstZeroStateMass law w x (t + 1)) z) =
    ∑ y : BitString n, P x y *
      (∑ z : BitString n,
        S.indicator (firstZeroStateMass law w y t) z)
  calc
    (∑ z : BitString n,
        S.indicator (firstZeroStateMass law w x (t + 1)) z) =
      ∑ z : BitString n, ∑ y : BitString n,
        P x y * S.indicator (firstZeroStateMass law w y t) z := by
          apply Finset.sum_congr rfl
          intro z _
          by_cases hz : z ∈ S
          · simp only [Set.indicator_of_mem hz]
            exact firstZeroStateMass_from_start law w t x z
          · simp only [Set.indicator_of_notMem hz, mul_zero,
              Finset.sum_const_zero]
    _ = ∑ y : BitString n, P x y *
          (∑ z : BitString n,
            S.indicator (firstZeroStateMass law w y t) z) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]

private theorem firstZeroNonoptimalMass_zero_ite {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) :
    firstZeroNonoptimalMass law w x 0 =
      if firstZeroAllOnes x then 0 else 1 := by
  classical
  -- At time zero the point mass is supported exactly at the initial state.
  -- Do not expect `simp` to eliminate the finite sum automatically.
  unfold firstZeroNonoptimalMass finiteEventMass
  let S : Set (BitString n) := {z | ¬ firstZeroAllOnes z}
  change (∑ z : BitString n,
      S.indicator (firstZeroStateMass law w x 0) z) =
    if firstZeroAllOnes x then 0 else 1
  calc
    (∑ z : BitString n,
        S.indicator (firstZeroStateMass law w x 0) z) =
        S.indicator (firstZeroStateMass law w x 0) x := by
          apply Fintype.sum_eq_single x
          intro z hz
          have hzero : firstZeroStateMass law w x 0 z = 0 := by
            simp [firstZeroStateMass, hz]
          by_cases hzS : z ∈ S
          · rw [Set.indicator_of_mem hzS]
            exact hzero
          · simp only [Set.indicator_of_notMem hzS]
    _ = if firstZeroAllOnes x then 0 else 1 := by
          by_cases hx : firstZeroAllOnes x
          · have hxmem : x ∉ S := by
              change ¬ ¬ firstZeroAllOnes x
              exact not_not_intro hx
            rw [Set.indicator_of_notMem hxmem]
            simp [hx]
          · have hxmem : x ∈ S := hx
            rw [Set.indicator_of_mem hxmem]
            simp [firstZeroStateMass, hx]

/-- The forward expected occupation sum obeys a *backward* one-step
recurrence in the initial state. This is the precise Bellman bridge. -/
private theorem firstZeroFiniteRuntimeMass_from_start {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) :
    firstZeroFiniteRuntimeMass law w x (T + 1) =
      firstZeroNonoptimalMass law w x 0 +
        ∑ y : BitString n,
          (law.transition (linearFitness w)) x y *
            firstZeroFiniteRuntimeMass law w y T := by
  induction T generalizing x with
  | zero =>
      simp [firstZeroFiniteRuntimeMass]
  | succ T ih =>
      let P := law.transition (linearFitness w)
      calc
        firstZeroFiniteRuntimeMass law w x (T + 1 + 1) =
            firstZeroFiniteRuntimeMass law w x (T + 1) +
              firstZeroNonoptimalMass law w x (T + 1) :=
                firstZeroFiniteRuntimeMass_succ law w x (T + 1)
        _ = (firstZeroNonoptimalMass law w x 0 +
              ∑ y : BitString n, P x y *
                firstZeroFiniteRuntimeMass law w y T) +
              ∑ y : BitString n, P x y *
                firstZeroNonoptimalMass law w y T := by
                  rw [ih x, firstZeroNonoptimalMass_from_start law w x T]
        _ = firstZeroNonoptimalMass law w x 0 +
              ∑ y : BitString n, P x y *
                (firstZeroFiniteRuntimeMass law w y T +
                  firstZeroNonoptimalMass law w y T) := by
                  simp only [mul_add, Finset.sum_add_distrib]
                  ring
        _ = firstZeroNonoptimalMass law w x 0 +
              ∑ y : BitString n, P x y *
                firstZeroFiniteRuntimeMass law w y (T + 1) := by
                  congr 1
                  apply Finset.sum_congr rfl
                  intro y _
                  rw [firstZeroFiniteRuntimeMass_succ law w y T]

private theorem firstZeroHittingRuntime_of_allOnes {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (t : Nat) (y : BitString n) (hy : firstZeroAllOnes y) :
    finiteHorizonRuntime (law.transition (linearFitness w))
      (firstZeroOptimalSet (n := n)) t y = 0 := by
  cases t with
  | zero => rfl
  | succ t =>
      exact finiteHorizonRuntime_succ_of_mem
        (law.transition (linearFitness w))
        (firstZeroOptimalSet (n := n)) t y hy

/-- (7/9) Under superincreasing weights, the expected truncated hitting time
of the all-ones optimum equals the sum of nonoptimal state marginals.
Crucially, this uses result (1): for a nonabsorbing target it is false. -/
theorem firstZeroFiniteRuntimeMass_eq_hittingRuntime {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) :
    firstZeroFiniteRuntimeMass law w x T =
      finiteHorizonRuntime (law.transition (linearFitness w))
        (firstZeroOptimalSet (n := n)) T x := by
  classical
  let P := law.transition (linearFitness w)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  induction T generalizing x with
  | zero =>
      simp [firstZeroFiniteRuntimeMass]
  | succ T ih =>
      rw [firstZeroFiniteRuntimeMass_from_start law w x T]
      by_cases hx : firstZeroAllOnes x
      · have hnonopt : firstZeroNonoptimalMass law w x 0 = 0 := by
          rw [firstZeroNonoptimalMass_zero_ite]
          simp [hx]
        have hsum :
            (∑ y : BitString n, P x y *
              firstZeroFiniteRuntimeMass law w y T) = 0 := by
          apply Finset.sum_eq_zero
          intro y _
          by_cases hy : firstZeroAllOnes y
          · rw [ih y, firstZeroHittingRuntime_of_allOnes law w T y hy]
            simp
          · have hzero : P x y = 0 := by
              apply le_antisymm _ (hP.1 x y)
              apply le_of_not_gt
              intro hpos
              exact hy (firstZeroOptimum_transition_supported
                law w hw x y hx hpos)
            simp [hzero]
        have hmem : x ∈ firstZeroOptimalSet (n := n) := hx
        -- Rewrite the left-hand occupation mass *before* applying the
        -- target-membership hitting-time identity. The generic simplifier
        -- leaves the finite transition sum unchanged here.
        change firstZeroNonoptimalMass law w x 0 +
            (∑ y : BitString n, P x y *
              firstZeroFiniteRuntimeMass law w y T) =
          finiteHorizonRuntime P (firstZeroOptimalSet (n := n)) (T + 1) x
        rw [hnonopt, hsum, zero_add]
        exact (finiteHorizonRuntime_succ_of_mem P
          (firstZeroOptimalSet (n := n)) T x hmem).symm
      · have hnonopt : firstZeroNonoptimalMass law w x 0 = 1 := by
          rw [firstZeroNonoptimalMass_zero_ite]
          simp [hx]
        rw [hnonopt]
        simp_rw [ih]
        change 1 + expectedValueAfter P
            (finiteHorizonRuntime P (firstZeroOptimalSet (n := n)) T) x =
          finiteHorizonRuntime P (firstZeroOptimalSet (n := n)) (T + 1) x
        have hnotmem : x ∉ firstZeroOptimalSet (n := n) := hx
        exact (finiteHorizonRuntime_succ_of_not_mem P
          (firstZeroOptimalSet (n := n)) T x hnotmem).symm

/-- (8/9) Finite-horizon runtime is bounded by the exact visitation/hazard
budget, for positive one-bit mutation mass. -/
theorem firstZeroFiniteRuntimeMass_le_visitBudget {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) (hp1 : 0 < law.oneBitMass) :
    firstZeroFiniteRuntimeMass law w x T ≤
      firstZeroFiniteVisitBudget law w x T := by
  calc
    firstZeroFiniteRuntimeMass law w x T =
        ∑ t ∈ Finset.range T, firstZeroGlobalOccupationMass law w x t :=
      firstZeroFiniteRuntimeMass_eq_globalOccupation law w x T
    _ ≤ firstZeroFiniteVisitBudget law w x T :=
      firstZeroGlobalOccupation_horizon_le_visits law w hw x T hp1

/-- (9/9) Since each visit probability is at most one, the finite expected
runtime has a horizon-uniform hazard cap. This is not yet an infinite-horizon
expected-runtime theorem, because the limit passage is still unproved. -/
theorem firstZeroFiniteRuntimeMass_le_hazardCap {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) (hp1 : 0 < law.oneBitMass) :
    firstZeroFiniteRuntimeMass law w x T ≤
      ∑ i : Fin n, 1 / law.maskEventMass (lowestMaskEvent i) := by
  calc
    firstZeroFiniteRuntimeMass law w x T ≤
        firstZeroFiniteVisitBudget law w x T :=
      firstZeroFiniteRuntimeMass_le_visitBudget law w hw x T hp1
    _ ≤ ∑ i : Fin n, 1 / law.maskEventMass (lowestMaskEvent i) := by
      unfold firstZeroFiniteVisitBudget
      apply Finset.sum_le_sum
      intro i _
      have hnNat : 0 < n :=
        lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
      have hn : (0 : Real) < n := by exact_mod_cast hnNat
      have hq : 0 < law.maskEventMass (lowestMaskEvent i) :=
        lt_of_lt_of_le (div_pos hp1 hn)
          (law.lowestMaskEvent_mass_ge_oneBit_per_coordinate i)
      apply (div_le_div_iff₀ hq hq).2
      exact mul_le_mul_of_nonneg_right
        (firstZeroTrajectoryVisitMass_le_one law w x i T) (le_of_lt hq)

end FiniteRuntimeDecidability
end StaticUnaryUnbiasedMutation
end ECRuntime
