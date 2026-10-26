import ECRuntime.OneMaxUnaryHarmonic
import ECRuntime.StaticUnaryZeroFlipExpectationDoubleCount
import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.OneMaxEANoFlipMaskWeight
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.OneMax
import Mathlib

namespace ECRuntime

/-! P07: the additive constant-level lower bound from Stage 379 does
not recover the coupon-collector logarithm. A sharper lower theorem
needs a bound on expected *harmonic potential* progress rather than
expected zero-count progress, and has to exclude unrestricted multi-bit
jumps. We explicitly use singleton-supported laws. -/

/-- For a static unary-unbiased law supported on the empty mask and
singletons, one-step expected harmonic-potential progress is at most
meanRadius/n for every nonoptimal state. The restriction on mask support
is essential; arbitrary multi-bit mutation does not satisfy this bound. -/
theorem proposed_unaryOneMax_singletonHarmonicProgress_le_radiusDivN
    {n : Nat} (hn : 0 < n)
    (law : StaticUnaryUnbiasedMutation n)
    (hsmall : ∀ mask : MutationMask n,
      law.weight mask ≠ 0 → mask.card ≤ 1)
    (x : BitString n) (hx : x ≠ allOnes n) :
    (∑ y : BitString n,
      (law.transition oneMaxReal) x y *
        (harmonicReal (zeroCount x) - harmonicReal (zeroCount y))) ≤
      law.meanRadius / (n : Real) := by
  classical
  let V : BitString n → Real := fun y => harmonicReal (zeroCount y)
  have hpos : 0 < zeroCount x := Nat.pos_of_ne_zero (by
    intro hzero
    exact hx ((zeroCount_eq_zero_iff_allOnes x).mp hzero))
  have hd0 : (zeroCount x : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have hn0 : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hP : IsStochastic (law.transition oneMaxReal) :=
    law.transition_stochastic _
  have hrewrite :
      (∑ y : BitString n, (law.transition oneMaxReal) x y * (V x - V y)) =
        driftAt (law.transition oneMaxReal) V x := by
    unfold driftAt
    calc
      (∑ y : BitString n,
          (law.transition oneMaxReal) x y * (V x - V y)) =
        (∑ y : BitString n, (law.transition oneMaxReal) x y) * V x -
          ∑ y : BitString n, (law.transition oneMaxReal) x y * V y := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro y _
            ring
      _ = V x - expectedValueAfter (law.transition oneMaxReal) V x := by
            rw [hP.2 x, one_mul]
            rfl
  have hsingle (i : Fin n) :
      V x - V (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
        if x i = false then (zeroCount x : Real)⁻¹ else 0 := by
    dsimp [V]
    rw [candidate_rls_harmonic_oneBit_drop x i]
    ring
  have hcard (i : Fin n) :
      (((zeroPositions x ∩ ({i} : MutationMask n)).card : Real)) =
        if x i = false then 1 else 0 := by
    by_cases hi : x i = false
    · have hm : i ∈ zeroPositions x := (mem_zeroPositions x i).mpr hi
      simp [hm, hi]
    · have hm : i ∉ zeroPositions x := by
        intro himem
        exact hi ((mem_zeroPositions x i).mp himem)
      simp [hm, hi]
  have hmask (mask : MutationMask n) :
      law.weight mask *
          (V x - V (selectedAfterMask oneMaxReal x mask)) =
        law.weight mask *
          (((zeroPositions x ∩ mask).card : Real) *
            (zeroCount x : Real)⁻¹) := by
    by_cases hw : law.weight mask = 0
    · simp [hw]
    · have hc : mask.card ≤ 1 := hsmall mask hw
      have hcases : mask.card = 0 ∨ mask.card = 1 := by omega
      rcases hcases with hzero | hone
      · have hempty : mask = ∅ := Finset.card_eq_zero.mp hzero
        subst mask
        simp [V, selectedAfterMask, elitistSelect, mutateWithMask_empty]
      · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hone
        subst mask
        rw [hsingle i, hcard i]
        by_cases hxi : x i = false <;> simp [hxi]
  have hsum :
      (∑ mask : MutationMask n,
        law.weight mask *
          (V x - V (selectedAfterMask oneMaxReal x mask))) =
        (∑ mask : MutationMask n,
          law.weight mask * ((zeroPositions x ∩ mask).card : Real)) *
            (zeroCount x : Real)⁻¹ := by
    calc
      (∑ mask : MutationMask n,
        law.weight mask *
          (V x - V (selectedAfterMask oneMaxReal x mask))) =
        ∑ mask : MutationMask n,
          law.weight mask *
            (((zeroPositions x ∩ mask).card : Real) *
              (zeroCount x : Real)⁻¹) := by
                apply Finset.sum_congr rfl
                intro mask _
                exact hmask mask
      _ = (∑ mask : MutationMask n,
        law.weight mask * ((zeroPositions x ∩ mask).card : Real)) *
          (zeroCount x : Real)⁻¹ := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro mask _
            ring
  calc
    (∑ y : BitString n,
      (law.transition oneMaxReal) x y *
        (harmonicReal (zeroCount x) - harmonicReal (zeroCount y))) =
      driftAt (law.transition oneMaxReal) V x := hrewrite
    _ = ∑ mask : MutationMask n,
          law.weight mask *
            (V x - V (selectedAfterMask oneMaxReal x mask)) :=
        law.drift_eq_mask_sum oneMaxReal V x
    _ = (∑ mask : MutationMask n,
          law.weight mask * ((zeroPositions x ∩ mask).card : Real)) *
            (zeroCount x : Real)⁻¹ := hsum
    _ ≤ law.meanRadius / (n : Real) := by
      have hident :
          (∑ mask : MutationMask n,
            law.weight mask * ((zeroPositions x ∩ mask).card : Real)) *
              (zeroCount x : Real)⁻¹ = law.meanRadius / (n : Real) := by
        rw [proposed_unaryMask_expectedFlippedZeroCount_eq_meanRadius hn law x]
        field_simp [hd0, hn0]
      exact hident.le

end ECRuntime
