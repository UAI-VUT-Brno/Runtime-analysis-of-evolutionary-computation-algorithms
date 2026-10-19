import ECRuntime.MultiplicativeDrift
import ECRuntime.LinearPotential
import Mathlib

namespace ECRuntime

/-- Per-coordinate singleton progress rate for independent bit mutation. -/
def linearSingletonRate (n : ℕ) (p : ℝ) : ℝ :=
  p * (1 - p) ^ (n - 1)

/-- The singleton progress rate is positive for `0 < p < 1`. -/
theorem linearSingletonRate_pos {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    0 < linearSingletonRate n p := by
  unfold linearSingletonRate
  exact mul_pos hp0 (pow_pos (sub_pos.mpr hp1) _)

/--
Using the objective error itself as potential gives a coefficient-sensitive but very
clean multiplicative-drift theorem for every positive linear function.  This is weaker
than the bounded rank potential for arbitrary coefficients, but it is an important
second end-to-end problem class and a useful baseline for the rank-potential proof.
-/
theorem linearObjectiveError_hasMultiplicativeDriftLowerBound
    {n : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : Fin n → ℝ) (hw : PositiveLinearWeights w) :
    HasMultiplicativeDriftLowerBound (α := BitString n)
      (onePlusOneTransition p (linearFitness w))
      (linearErrorPotential w)
      (linearSingletonRate n p) := by
  intro x _hx
  rw [onePlusOneTransition_drift_eq_mask_sum]
  let F : MutationMask n → ℝ := fun mask =>
    mutationMaskWeight p mask *
      (linearErrorPotential w x -
        linearErrorPotential w (selectedAfterMask (linearFitness w) x mask))
  have hsingleton :
      linearSingletonRate n p * linearErrorPotential w x =
        ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) := by
    rw [linearErrorPotential_eq_sum_zeroPositions, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hzero : x i = false := (mem_zeroPositions x i).mp hi
    dsimp [F]
    rw [mutationMaskWeight_singleton,
      linearErrorPotential_selected_single_zero_flip_drop w hw x i hzero]
    rfl
  have himage :
      (∑ i ∈ zeroPositions x, F ({i} : MutationMask n)) =
        ∑ mask ∈ zeroSingletonMasks x, F mask := by
    symm
    unfold zeroSingletonMasks
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact Finset.singleton_injective hab
  calc
    linearSingletonRate n p * linearErrorPotential w x =
        ∑ i ∈ zeroPositions x, F ({i} : MutationMask n) := hsingleton
    _ = ∑ mask ∈ zeroSingletonMasks x, F mask := himage
    _ ≤ ∑ mask : MutationMask n, F mask := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro mask hmask hnotmem
        dsimp [F]
        exact mul_nonneg
          (mutationMaskWeight_nonneg hp0 hp1 mask)
          (linearErrorPotential_selected_drop_nonneg w x mask)

/-- The zero level of the objective-error potential. -/
def linearObjectiveErrorTarget {n : ℕ} (w : Fin n → ℝ) : Set (BitString n) :=
  realPotentialTarget (linearErrorPotential w)

/-- Membership in the objective-error target is classically decidable. -/
noncomputable instance instDecidablePredLinearObjectiveErrorTarget
    {n : ℕ} (w : Fin n → ℝ) :
    DecidablePred (fun x : BitString n => x ∈ linearObjectiveErrorTarget w) := by
  classical
  intro x
  change Decidable (linearErrorPotential w x = 0)
  infer_instance

/--
A positive uniform lower bound on all objective coefficients makes the objective-error
target exactly the all-one optimum.
-/
theorem linearObjectiveErrorTarget_eq_singleton_of_lower_bound
    {n : ℕ} (w : Fin n → ℝ) (wmin : ℝ)
    (hwmin : 0 < wmin) (hwl : ∀ i, wmin ≤ w i) :
    linearObjectiveErrorTarget w = ({allOnes n} : Set (BitString n)) := by
  ext x
  constructor
  · intro hx
    have hx0 : linearErrorPotential w x = 0 := by
      simpa [linearObjectiveErrorTarget, realPotentialTarget] using hx
    have hlower := mul_zeroCount_le_linearErrorPotential wmin w hwl x
    rw [hx0] at hlower
    have hzreal : (zeroCount x : ℝ) = 0 := by
      have hznonneg : 0 ≤ (zeroCount x : ℝ) := by positivity
      nlinarith
    have hz : zeroCount x = 0 := by exact_mod_cast hzreal
    have hall : x = allOnes n := (zeroCount_eq_zero_iff_allOnes x).mp hz
    simp [hall]
  · intro hx
    have hall : x = allOnes n := by simpa using hx
    subst x
    simp [linearObjectiveErrorTarget, realPotentialTarget]

/-- Every non-target objective error is at least the supplied positive coefficient floor. -/
theorem linearObjectiveError_lower_bound_of_not_target
    {n : ℕ} (w : Fin n → ℝ) (wmin : ℝ)
    (hwmin : 0 < wmin) (hwl : ∀ i, wmin ≤ w i)
    (x : BitString n) (hx : x ∉ linearObjectiveErrorTarget w) :
    wmin ≤ linearErrorPotential w x := by
  have htarget := linearObjectiveErrorTarget_eq_singleton_of_lower_bound
    w wmin hwmin hwl
  have hxne : x ≠ allOnes n := by
    intro hall
    apply hx
    rw [htarget]
    simp [hall]
  have hz : zeroCount x ≠ 0 := by
    intro hz0
    exact hxne ((zeroCount_eq_zero_iff_allOnes x).mp hz0)
  have honeNat : 1 ≤ zeroCount x := Nat.one_le_iff_ne_zero.mpr hz
  have hone : (1 : ℝ) ≤ (zeroCount x : ℝ) := by exact_mod_cast honeNat
  have hscaled := mul_zeroCount_le_linearErrorPotential wmin w hwl x
  have hfirst : wmin ≤ wmin * (zeroCount x : ℝ) := by
    nlinarith
  exact hfirst.trans hscaled

/--
End-to-end coefficient-sensitive runtime certificate for every positive linear
objective.  The dependence on `wmin` is precisely why the bounded rank potential is
needed to obtain a coefficient-independent `O(n log n)` theorem.
-/
theorem linearObjectiveError_runtimeSup_le
    {n : ℕ} {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (w : Fin n → ℝ) (wmin : ℝ)
    (hwmin : 0 < wmin) (hwl : ∀ i, wmin ≤ w i)
    (x : BitString n) :
    runtimeSup
        (onePlusOneTransition p (linearFitness w))
        (linearObjectiveErrorTarget w) x ≤
      ENNReal.ofReal
        (multiplicativeDriftRuntime
          (linearSingletonRate n p) wmin (linearErrorPotential w) x) := by
  have hw : PositiveLinearWeights w := fun i => lt_of_lt_of_le hwmin (hwl i)
  have hP : IsStochastic (onePlusOneTransition p (linearFitness w)) :=
    onePlusOneTransition_stochastic hp0.le hp1.le (linearFitness w)
  have hV : ∀ z : BitString n, 0 ≤ linearErrorPotential w z := by
    intro z
    exact linearErrorPotential_nonneg w (fun i => (hw i).le) z
  have hmin : ∀ z : BitString n,
      z ∉ realPotentialTarget (linearErrorPotential w) →
        wmin ≤ linearErrorPotential w z := by
    intro z hz
    apply linearObjectiveError_lower_bound_of_not_target w wmin hwmin hwl z
    simpa [linearObjectiveErrorTarget] using hz
  have hbound := multiplicativeDrift_runtimeSup_le
    (onePlusOneTransition p (linearFitness w))
    (linearErrorPotential w)
    (linearSingletonRate n p) wmin
    hP (linearSingletonRate_pos hp0 hp1) hwmin hV hmin
    (linearObjectiveError_hasMultiplicativeDriftLowerBound hp0.le hp1.le w hw) x
  calc
    runtimeSup
        (onePlusOneTransition p (linearFitness w))
        (linearObjectiveErrorTarget w) x =
      runtimeSup
        (onePlusOneTransition p (linearFitness w))
        (realPotentialTarget (linearErrorPotential w)) x := by
          exact runtimeSup_congr_target
            (onePlusOneTransition p (linearFitness w))
            (linearObjectiveErrorTarget w)
            (realPotentialTarget (linearErrorPotential w)) rfl x
    _ ≤ ENNReal.ofReal
        (multiplicativeDriftRuntime
          (linearSingletonRate n p) wmin (linearErrorPotential w) x) := hbound

end ECRuntime
