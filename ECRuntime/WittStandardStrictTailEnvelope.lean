import ECRuntime.WittStandardStrictTailGeometry
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 35: ordered strict-tail envelope and pessimistic raw drift

Stage 34 separates the remaining sharp-standard-rate argument into a geometric
cancellation and one selected/accepted bad-mass inequality.  This module closes the
purely geometric side for the *actual state-dependent strict tail*.

For a fixed improving coordinate `i`, enumerate the currently-correct coordinates
with strictly smaller objective coefficient in increasing coordinate order.  If `j_r`
is the element of rank `r`, then the definition of the Witt exponent implies

`exponent(j_r) + r <= exponent(i)`.

At the standard mutation rate the reciprocal identity

`wittStandardBase n * (1 - 1/n) = 1`

therefore gives

`g(j_r) <= g(i) * (1 - 1/n)^r`.

Summing over the tail and using the Stage-34 survival-series identity proves that the
pessimistic Bernoulli worsening mass is bounded by the good mass attached to seeing at
least one tail flip.  Equivalently, the corresponding raw strict-tail contribution is
nonnegative.  The only issue deliberately left open is the comparison between this raw
pessimistic family and the selected accepted family of Stage 34.
-/

/-! ## Ordered tail ranks -/

/-- Increasing coordinate enumeration of the state-dependent strict tail. -/
noncomputable def wittStandardStrictTailOrder {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) :
    Fin (wittStandardStrictTailIndices w x i).card ≃o
      ↥(wittStandardStrictTailIndices w x i) :=
  (wittStandardStrictTailIndices w x i).orderIsoOfFin rfl

/-- The `r` earlier strict-tail coordinates witness an exponent gap of at least `r`.
This is the combinatorial core of the state-dependent geometric envelope. -/
theorem wittStandardExponent_add_strictTailRank_le {n : ℕ}
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittStandardExponent w
        ((wittStandardStrictTailOrder w x i r).1) + r.val ≤
      wittStandardExponent w i := by
  classical
  let T : Finset (Fin n) := wittStandardStrictTailIndices w x i
  let e : Fin T.card ↪o Fin n := T.orderEmbOfFin rfl
  let A : Finset (Fin n) := Finset.univ.filter (fun j => w j < w i)
  let j : Fin n := e r
  let B : Finset (Fin n) := Finset.univ.filter (fun l => w l < w j)
  let P : Finset (Fin n) := (Finset.Iio r).map e.toEmbedding

  have hjT : j ∈ T := by
    dsimp [j, e]
    exact Finset.orderEmbOfFin_mem T rfl r
  have hjData : x j = true ∧ w j < w i := by
    exact (mem_wittStandardStrictTailIndices w x i j).mp (by simpa [T] using hjT)

  have hBA : B ⊆ A := by
    intro l hl
    have hlB : w l < w j := by
      simpa [B] using hl
    have : w l < w i := lt_trans hlB hjData.2
    simpa [A] using this

  have hPsub : P ⊆ A \ B := by
    intro l hl
    rcases Finset.mem_map.mp hl with ⟨s, hs, rfl⟩
    have hslt : s < r := Finset.mem_Iio.mp hs
    have hesT : e s ∈ T := Finset.orderEmbOfFin_mem T rfl s
    have hesData : x (e s) = true ∧ w (e s) < w i := by
      exact (mem_wittStandardStrictTailIndices w x i (e s)).mp
        (by simpa [T] using hesT)
    have hcoord : e s < e r := e.lt_iff_lt.mpr hslt
    have hweight : w (e r) ≤ w (e s) :=
      hmono (e s) (e r) (Nat.le_of_lt hcoord)
    have hnotB : ¬ w (e s) < w (e r) := not_lt_of_ge hweight
    have heA : e s ∈ A := by
      simp [A, hesData.2]
    have heNotB : e s ∉ B := by
      simp [B, j, hnotB]
    exact Finset.mem_sdiff.mpr ⟨heA, heNotB⟩

  have hPcard : P.card = r.val := by
    dsimp [P]
    rw [Finset.card_map, Fin.card_Iio]

  have hPcard_le : r.val ≤ (A \ B).card := by
    rw [← hPcard]
    exact Finset.card_le_card hPsub

  have hdecomp : (A \ B).card + B.card = A.card :=
    Finset.card_sdiff_add_card_eq_card hBA

  have hrank : B.card + r.val ≤ A.card := by
    omega

  simpa [A, B, j, e, T, wittStandardExponent, wittStandardStrictTailOrder,
    Nat.add_comm] using hrank

/-- The `r`-th state-dependent strict-tail Witt coefficient is bounded by the `r`-th
survival term below the improving coefficient. -/
theorem wittStandardStrictTail_ordered_weight_le {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n)
    (r : Fin (wittStandardStrictTailIndices w x i).card) :
    wittStandardPotentialWeight w
        ((wittStandardStrictTailOrder w x i r).1) ≤
      wittStandardPotentialWeight w i *
        (1 - standardMutationRate n) ^ r.val := by
  have hgap := wittStandardExponent_add_strictTailRank_le w hmono x i r
  have hpow :
      wittStandardBase n ^
          (wittStandardExponent w ((wittStandardStrictTailOrder w x i r).1) + r.val) ≤
        wittStandardBase n ^ wittStandardExponent w i :=
    (pow_right_mono₀ (one_le_wittStandardBase n)) hgap
  have hp := standardMutationRate_mem_unitInterval_linear hn
  have hsurv : 0 ≤ 1 - standardMutationRate n := sub_nonneg.mpr hp.2
  have hmul := mul_le_mul_of_nonneg_right hpow (pow_nonneg hsurv r.val)
  have hcancel := wittStandardBase_pow_mul_standardSurvival_pow
    (n := n) (k := r.val) hn
  simpa [wittStandardPotentialWeight, pow_add, mul_assoc, hcancel] using hmul

/-! ## Summed state-dependent envelope -/

/-- The actual state-dependent strict-tail weight sum lies below the Stage-34
conditional geometric envelope with exactly the tail cardinality. -/
theorem sum_wittStandardStrictTailWeight_le_conditionalEnvelope {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    (∑ j ∈ wittStandardStrictTailIndices w x i,
        wittStandardPotentialWeight w j) ≤
      wittStandardStrictTailConditionalEnvelope w i
        (wittStandardStrictTailIndices w x i).card := by
  classical
  let T : Finset (Fin n) := wittStandardStrictTailIndices w x i
  have hsum :
      (∑ j ∈ T, wittStandardPotentialWeight w j) =
        ∑ r : Fin T.card,
          wittStandardPotentialWeight w (T.orderEmbOfFin rfl r) := by
    have himage :
        Finset.image (fun r : Fin T.card => T.orderEmbOfFin rfl r) Finset.univ = T :=
      T.image_orderEmbOfFin_univ rfl
    calc
      (∑ j ∈ T, wittStandardPotentialWeight w j) =
          ∑ j ∈ Finset.image (fun r : Fin T.card => T.orderEmbOfFin rfl r) Finset.univ,
            wittStandardPotentialWeight w j := by
        rw [himage]
      _ = ∑ r : Fin T.card,
          wittStandardPotentialWeight w (T.orderEmbOfFin rfl r) := by
        rw [Finset.sum_image (by
          intro a _ b _ hab
          exact (T.orderEmbOfFin rfl).injective hab)]
  rw [show wittStandardStrictTailIndices w x i = T by rfl]
  rw [hsum]
  unfold wittStandardStrictTailConditionalEnvelope
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  simpa [T, wittStandardStrictTailOrder] using
    wittStandardStrictTail_ordered_weight_le hn w hmono x i r

/-- Sharp pessimistic bad-mass envelope for the whole state-dependent strict tail.
The left side is the Bernoulli first moment `p * sum g_j`; the right side is the good
coefficient times the probability that at least one of the tail coordinates flips. -/
theorem standardMutationRate_mul_sum_wittStandardStrictTailWeight_le_goodMass
    {n : ℕ} (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    standardMutationRate n *
        (∑ j ∈ wittStandardStrictTailIndices w x i,
          wittStandardPotentialWeight w j) ≤
      wittStandardPotentialWeight w i *
        (1 - (1 - standardMutationRate n) ^
          (wittStandardStrictTailIndices w x i).card) := by
  have hsum := sum_wittStandardStrictTailWeight_le_conditionalEnvelope
    hn w hmono x i
  have hp0 := (standardMutationRate_mem_unitInterval_linear hn).1
  calc
    standardMutationRate n *
        (∑ j ∈ wittStandardStrictTailIndices w x i,
          wittStandardPotentialWeight w j) ≤
      standardMutationRate n *
        wittStandardStrictTailConditionalEnvelope w i
          (wittStandardStrictTailIndices w x i).card :=
      mul_le_mul_of_nonneg_left hsum hp0
    _ = wittStandardPotentialWeight w i *
        (1 - (1 - standardMutationRate n) ^
          (wittStandardStrictTailIndices w x i).card) :=
      standardMutationRate_mul_wittStandardStrictTailConditionalEnvelope
        w i (wittStandardStrictTailIndices w x i).card

/-! ## Pessimistic raw strict-tail contribution -/

/-- Closed first-moment form of Witt's pessimistic strict-tail experiment: require the
improving coordinate, expose at least one tail flip, and pessimistically count every
strict-tail worsening flip before any acceptance filtering.  A common outside-mask
factor is intentionally omitted; it is nonnegative and irrelevant for the sign. -/
noncomputable def wittStandardStrictTailPessimisticContribution {n : ℕ}
    (w : Fin n → ℝ) (x : BitString n) (i : Fin n) : ℝ :=
  wittStandardPotentialWeight w i *
      (1 - (1 - standardMutationRate n) ^
        (wittStandardStrictTailIndices w x i).card) -
    standardMutationRate n *
      (∑ j ∈ wittStandardStrictTailIndices w x i,
        wittStandardPotentialWeight w j)

/-- The pessimistic raw strict-tail first moment is nonnegative.  This closes the
finite geometric part of Witt's Subcase 2.2.2 for the actual state-dependent tail. -/
theorem wittStandardStrictTailPessimisticContribution_nonneg {n : ℕ}
    (hn : 2 ≤ n)
    (w : Fin n → ℝ) (hmono : NonincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    0 ≤ wittStandardStrictTailPessimisticContribution w x i := by
  unfold wittStandardStrictTailPessimisticContribution
  exact sub_nonneg.mpr
    (standardMutationRate_mul_sum_wittStandardStrictTailWeight_le_goodMass
      hn w hmono x i)

end ECRuntime
