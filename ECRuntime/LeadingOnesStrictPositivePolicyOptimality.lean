import ECRuntime.LeadingOnesOptimalAdaptiveSchedule
import ECRuntime.AdaptiveLeadingOnesUniquePositiveLevelOptimizer
import ECRuntime.AdaptiveLeadingOnesUniformFullRuntime
import ECRuntime.FiniteENNRealCostEqualityRigidity
import ECRuntime.AdaptiveLeadingOnesOptimalPositiveLevelRate
import Mathlib

open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable
namespace ECRuntime

/-! P01: an equality of *finite* complete runtimes implies equality of
all levelwise costs, and hence the unique optimal interior rate at every
positive level.  We explicitly prove that the ENNReal cost terms are
non-top before using equality rigidity: at top, cancellation would be
invalid. -/

/-- At fixed level-zero rate, equality of genuine uniform runtime forces
all positive-level mutation rates to be locally optimal. -/
theorem proposed_leadingOnes_referenceOptimal_uniformRuntime_equality_iff
    (n : Nat) [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (base : Real) (hb0 : 0 < base) (hb1 : base < 1)
    (rate : Nat → Real)
    (hinterior : ∀ j : Nat, j ≤ n → 0 < rate j ∧ rate j < 1)
    (hfirst : rate 0 = base)
    (hequality :
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          runtimeSup (leadingOnesAdaptiveTransition rate)
            (leadingOnesTarget n) x) =
      ((Fintype.card (BitString n) : ENNReal)⁻¹) *
        (∑ x : BitString n,
          runtimeSup (leadingOnesAdaptiveTransition
            (proposed_leadingOnes_referenceOptimalRate base))
            (leadingOnesTarget n) x)) :
    ∀ i : Fin n, 0 < i.val →
      rate i.val = proposed_leadingOnes_referenceOptimalRate base i.val := by
  classical
  let opt : Nat → Real := proposed_leadingOnes_referenceOptimalRate base
  let exitRate (i : Fin n) : Real :=
    rate i.val * (1 - rate i.val) ^ i.val
  let exitOpt (i : Fin n) : Real :=
    opt i.val * (1 - opt i.val) ^ i.val
  let a (i : Fin n) : ENNReal :=
    (1 / 2 : ENNReal) * ENNReal.ofReal ((exitOpt i)⁻¹)
  let b (i : Fin n) : ENNReal :=
    (1 / 2 : ENNReal) * ENNReal.ofReal ((exitRate i)⁻¹)
  have hopt : ∀ j : Nat, j ≤ n → 0 < opt j ∧ opt j < 1 := by
    intro j _hj
    by_cases hj0 : j = 0
    · subst j
      simpa [opt, proposed_leadingOnes_referenceOptimalRate] using
        (show 0 < base ∧ base < 1 from ⟨hb0, hb1⟩)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      simpa only [opt, proposed_leadingOnes_referenceOptimalRate,
        if_neg hj0, leadingOnesLocallyOptimalSchedule, one_div] using
        (proposed_leadingOnesAdaptive_optimalPositiveLevelRate_strict j hjpos)
  have hposRate (i : Fin n) : 0 < exitRate i := by
    dsimp [exitRate]
    exact mul_pos (hinterior i.val i.isLt.le).1
      (pow_pos (sub_pos.mpr (hinterior i.val i.isLt.le).2) _)
  have hposOpt (i : Fin n) : 0 < exitOpt i := by
    dsimp [exitOpt]
    exact mul_pos (hopt i.val i.isLt.le).1
      (pow_pos (sub_pos.mpr (hopt i.val i.isLt.le).2) _)
  have hmass (i : Fin n) : exitRate i ≤ exitOpt i := by
    by_cases hi0 : i.val = 0
    · dsimp [exitRate, exitOpt, opt]
      simp [hi0, hfirst, proposed_leadingOnes_referenceOptimalRate]
    · have hiPos : 0 < i.val := Nat.pos_of_ne_zero hi0
      have hbound := proposed_leadingOnes_levelExitMass_le_optimal
        i.val hiPos (rate i.val)
        (hinterior i.val i.isLt.le).1.le
        (hinterior i.val i.isLt.le).2.le
      simpa only [exitRate, exitOpt, opt,
        proposed_leadingOnes_referenceOptimalRate, if_neg hi0] using hbound
  have hterm (i : Fin n) : a i ≤ b i := by
    have hinv : (exitOpt i)⁻¹ ≤ (exitRate i)⁻¹ :=
      (inv_le_inv₀ (hposOpt i) (hposRate i)).2 (hmass i)
    exact mul_le_mul_of_nonneg_left
      (ENNReal.ofReal_le_ofReal hinv) (bot_le : (0 : ENNReal) ≤ 1 / 2)
  have hhalf : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : Real) := by
    simpa only [one_div] using ENNReal_ofReal_half.symm
  have haOfReal (i : Fin n) :
      a i = ENNReal.ofReal ((1 / 2 : Real) * (exitOpt i)⁻¹) := by
    dsimp [a]
    rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 1 / 2)]
  have hbOfReal (i : Fin n) :
      b i = ENNReal.ofReal ((1 / 2 : Real) * (exitRate i)⁻¹) := by
    dsimp [b]
    rw [hhalf, ← ENNReal.ofReal_mul (by norm_num : (0 : Real) ≤ 1 / 2)]
  have hbFinite (i : Fin n) : b i ≠ ⊤ := by
    rw [hbOfReal]
    exact ENNReal.ofReal_ne_top
  have hsum : (∑ i : Fin n, a i) = ∑ i : Fin n, b i := by
    have hrate := proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum
      n rate hinterior
    have hoptRuntime := proposed_leadingOnesAdaptive_uniformRuntime_eq_halfExitSum
      n opt hopt
    dsimp [a, b]
    exact hoptRuntime.symm.trans (hequality.symm.trans hrate)
  have hpoint := proposed_finiteENNRealCosts_eq_of_sum_eq
    (Finset.univ : Finset (Fin n)) a b
    (fun i _ => hbFinite i) (fun i _ => hterm i) hsum
  intro i hi
  have heqCost : a i = b i := hpoint i (Finset.mem_univ i)
  have hreal :
      (1 / 2 : Real) * (exitOpt i)⁻¹ =
        (1 / 2 : Real) * (exitRate i)⁻¹ := by
    have h := congrArg ENNReal.toReal heqCost
    rw [haOfReal, hbOfReal,
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (inv_nonneg.mpr (hposOpt i).le)),
      ENNReal.toReal_ofReal (mul_nonneg (by norm_num) (inv_nonneg.mpr (hposRate i).le))] at h
    exact h
  have hinv : (exitOpt i)⁻¹ = (exitRate i)⁻¹ :=
    mul_left_cancel₀ (by norm_num : (1 / 2 : Real) ≠ 0) hreal
  have hexit : exitRate i = exitOpt i := by
    have h := congrArg (fun t : Real => t⁻¹) hinv
    simpa only [inv_inv] using h.symm
  have hunique := proposed_leadingOnes_positiveLevelExit_uniqueMaximizer
    i.val hi (rate i.val)
    (hinterior i.val i.isLt.le).1.le
    (hinterior i.val i.isLt.le).2.le
  have heq : rate i.val = 1 / ((i.val + 1 : Nat) : Real) :=
    hunique (by
      simpa only [exitRate, exitOpt, opt,
        proposed_leadingOnes_referenceOptimalRate,
        if_neg (Nat.ne_of_gt hi)] using hexit)
  simpa only [opt, proposed_leadingOnes_referenceOptimalRate,
    if_neg (Nat.ne_of_gt hi)] using heq

end ECRuntime
