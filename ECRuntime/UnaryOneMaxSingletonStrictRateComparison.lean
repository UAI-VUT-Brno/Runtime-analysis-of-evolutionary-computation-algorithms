import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import Mathlib

namespace ECRuntime

/-! P07: strictly increasing the one-bit mutation probability makes
the *real exact-runtime factor* smaller for nonoptimal starting states,
within the singleton-only mutation class. This does not claim the same
monotonicity for arbitrary multi-bit mutation operators. -/

/-- The harmonic singleton runtime factor is strictly decreasing in the
positive one-bit mass when at least one zero bit remains. -/
theorem proposed_unaryOneMax_singletonRate_strictRuntimeFactor
    {n : Nat} (hn : 0 < n) (d : Nat) (hd : 0 < d)
    (qSlow qFast : Real)
    (hs : 0 < qSlow) (hfast : qSlow < qFast) :
    ((n : Real) / qFast) * harmonicReal d <
      ((n : Real) / qSlow) * harmonicReal d := by
  have hdim : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hf : 0 < qFast := lt_trans hs hfast
  have hH : 0 < harmonicReal d := by
    have hstep := harmonicReal_add_inv_le_of_lt (j := 0) (k := d) hd
    have hinv : (0 : Real) < (d : Real)⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr hd)
    have hle : (d : Real)⁻¹ ≤ harmonicReal d := by simpa using hstep
    exact lt_of_lt_of_le hinv hle
  have hdiv : (n : Real) / qFast < (n : Real) / qSlow := by
    apply (div_lt_div_iff₀ hf hs).2
    nlinarith [mul_pos hdim (sub_pos.mpr hfast)]
  exact mul_lt_mul_of_pos_right hdiv hH

end ECRuntime
