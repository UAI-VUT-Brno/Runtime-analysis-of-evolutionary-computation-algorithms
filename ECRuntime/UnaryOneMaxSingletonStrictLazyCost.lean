import ECRuntime.UnaryOneMaxSingletonExactHarmonicNoRedundancy
import Mathlib

namespace ECRuntime

/-! P07: strict quantitative cost of zero-radius mutation under the
singleton-only model; distinguish this from a universal harmonic lower
bound for arbitrary static unary operators. -/

/-- For a nonzero zero-count and a one-bit mass below one, the real
harmonic runtime factor is strictly above standard RLS. -/
theorem proposed_unaryOneMax_lazySingletonStrictFactor
    {n : Nat} (hn : 0 < n)
    (d : Nat) (hd : 0 < d)
    (q : Real) (hq0 : 0 < q) (hq1 : q < 1) :
    (n : Real) * harmonicReal d <
      ((n : Real) / q) * harmonicReal d := by
  have hdim : (0 : Real) < n := Nat.cast_pos.mpr hn
  have hH : 0 < harmonicReal d := by
    have hstep := harmonicReal_add_inv_le_of_lt (j := 0) (k := d) hd
    have hinv : (0 : Real) < (d : Real)⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr hd)
    have hle : (d : Real)⁻¹ <= harmonicReal d := by
      simpa using hstep
    exact lt_of_lt_of_le hinv hle
  have hscaled : (n : Real) < (n : Real) / q := by
    apply (lt_div_iff₀ hq0).2
    nlinarith
  exact mul_lt_mul_of_pos_right hscaled hH

end ECRuntime
