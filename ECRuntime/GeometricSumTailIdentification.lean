import ECRuntime.GeometricSumTailRecursion
import ECRuntime.GeometricPrefixTailCongruence
import ECRuntime.DirectGeometricTailDomination
import Mathlib

open MeasureTheory

namespace ECRuntime

/-!
# Stage 26 fix 70: identify the recursive table with the geometric-sum tail

The geometric sum and the algebraic comparison table now have matching base
cases and matching final-coordinate recurrences.  A threshold induction closes
the identification: the `k+1` step uses the induction hypothesis at threshold
`k` both for the full vector and for its prefix.
-/

/-- Exact natural-threshold tail identification for an arbitrary nonzero vector
of unit-interval geometric parameters. -/
theorem geometricWaitingSumMeasure_tail_eq_finiteGeometricComparisonTail
    (k : Nat) :
    forall (m : Nat) (q : Fin m -> unitInterval),
      (forall i, Not (q i = 0)) ->
      runtimeTailMass (geometricWaitingSumMeasure q) id (k : ENNReal) =
        ENNReal.ofReal
          (finiteGeometricComparisonTail
            (fun i : Fin m => (q i : Real)) m k) := by
  induction k with
  | zero =>
      intro m q hq
      cases m with
      | zero =>
          rw [geometricWaitingSumMeasure_fin_zero_tail]
          simp
      | succ n =>
          simpa using (geometricWaitingSumMeasure_positive_tail_zero q)
  | succ k ih =>
      intro m q hq
      cases m with
      | zero =>
          rw [geometricWaitingSumMeasure_fin_zero_tail]
          simp
      | succ n =>
          let r : Fin (n + 1) -> Real := fun i => (q i : Real)
          let qpre : Fin n -> unitInterval := fun i => q i.castSucc
          have hqpre : forall i, Not (qpre i = 0) := by
            intro i
            exact hq i.castSucc
          have hr0 : forall i : Fin (n + 1), 0 <= r i := by
            intro i
            exact (q i).property.1
          have hr1 : forall i : Fin (n + 1), r i <= 1 := by
            intro i
            exact (q i).property.2
          have hlast0 : 0 <= r (Fin.last n) := hr0 (Fin.last n)
          have hlast1m : 0 <= 1 - r (Fin.last n) :=
            sub_nonneg.mpr (hr1 (Fin.last n))
          have hBfull :
              0 <= finiteGeometricComparisonTail r (n + 1) k :=
            finiteGeometricComparisonTail_nonneg r hr0 hr1 k (n + 1)
          have hBprefixR :
              0 <= finiteGeometricComparisonTail
                (fun i : Fin n => r i.castSucc) n k := by
            apply finiteGeometricComparisonTail_nonneg
            · intro i
              exact hr0 i.castSucc
            · intro i
              exact hr1 i.castSucc
          have hrec :
              finiteGeometricComparisonTail r (n + 1) (k + 1) =
                (1 - r (Fin.last n)) *
                    finiteGeometricComparisonTail r (n + 1) k +
                  r (Fin.last n) *
                    finiteGeometricComparisonTail
                      (fun i : Fin n => r i.castSucc) n k := by
            have hrec0 :=
              finiteGeometricComparisonTail_succ_succ r n k
                (Nat.lt_succ_self n)
            rw [finiteGeometricComparisonTail_castSucc_prefix r k] at hrec0
            have hlastFin :
                (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by
              apply Fin.ext
              rfl
            rw [hlastFin] at hrec0
            exact hrec0
          rw [geometricWaitingSumMeasure_tail_succ q hq k]
          rw [ih (n + 1) q hq]
          rw [ih n qpre hqpre]
          change
            ENNReal.ofReal (1 - r (Fin.last n)) *
                ENNReal.ofReal
                  (finiteGeometricComparisonTail r (n + 1) k) +
              ENNReal.ofReal (r (Fin.last n)) *
                ENNReal.ofReal
                  (finiteGeometricComparisonTail
                    (fun i : Fin n => r i.castSucc) n k) =
              ENNReal.ofReal
                (finiteGeometricComparisonTail r (n + 1) (k + 1))
          rw [hrec]
          rw [ENNReal.ofReal_add
            (mul_nonneg hlast1m hBfull)
            (mul_nonneg hlast0 hBprefixR)]
          rw [ENNReal.ofReal_mul hlast1m]
          rw [ENNReal.ofReal_mul hlast0]

/-- The abstract geometric-side assumption introduced by fix 69 is now
satisfied by the canonical independent geometric-sum law. -/
theorem hasGeometricSumTailIdentification_geometricWaitingSum
    {m : Nat} (p : Fin m -> Real)
    (hp : forall i, 0 < p i) (hp1 : forall i, p i <= 1) :
    HasGeometricSumTailIdentification p hp hp1 := by
  intro k
  let q : Fin m -> unitInterval := geometricLevelProbabilityVector p hp hp1
  have hq : forall i, Not (q i = 0) := by
    intro i hzero
    have hcoe : (q i : Real) = 0 := by
      rw [hzero]
      rfl
    have hpzero : p i = 0 := by
      simpa [q] using hcoe
    exact (ne_of_gt (hp i)) hpzero
  have h :=
    geometricWaitingSumMeasure_tail_eq_finiteGeometricComparisonTail
      k m q hq
  simpa [q] using h

end ECRuntime
