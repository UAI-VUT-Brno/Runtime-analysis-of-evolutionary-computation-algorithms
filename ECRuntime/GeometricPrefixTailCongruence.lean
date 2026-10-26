import ECRuntime.GeometricPrefixTailRecursion
import Mathlib

namespace ECRuntime

/-!
# Stage 26 fix 70: prefix congruence for the recursive comparison table

The direct Bellman/tail route introduced in Stage 26 fix 69 is now compiler
verified through the abstract geometric-sum endpoint.  The geometric
identification proof below repeatedly removes the final waiting phase.  This
module records the purely algebraic fact needed for that induction: the tail
for the first `n` phases depends only on probability coordinates strictly below
`n`.
-/

/-- Two infinite probability sequences that agree below `n` give the same
`n`-phase recursive tail at every natural threshold. -/
theorem geometricPrefixTailRec_congr_prefix
    (p q : Nat -> Real) :
    forall k n,
      (forall j, j < n -> p j = q j) ->
      geometricPrefixTailRec p n k = geometricPrefixTailRec q n k := by
  intro k
  induction k with
  | zero =>
      intro n _h
      cases n <;> simp
  | succ k ih =>
      intro n h
      cases n with
      | zero => simp
      | succ n =>
          rw [geometricPrefixTailRec_succ_succ,
            geometricPrefixTailRec_succ_succ]
          have hlast : p n = q n := h n (Nat.lt_succ_self n)
          have hsmall : forall j, j < n -> p j = q j := by
            intro j hj
            exact h j (Nat.lt_trans hj (Nat.lt_succ_self n))
          rw [hlast, ih (n + 1) h, ih n hsmall]

/-- Removing the last coordinate of a finite probability vector leaves every
comparison tail that uses only the preceding coordinates unchanged. -/
theorem finiteGeometricComparisonTail_castSucc_prefix
    {n : Nat} (p : Fin (n + 1) -> Real) (k : Nat) :
    finiteGeometricComparisonTail p n k =
      finiteGeometricComparisonTail (fun i : Fin n => p i.castSucc) n k := by
  unfold finiteGeometricComparisonTail
  apply geometricPrefixTailRec_congr_prefix
  intro j hj
  have hjfull : j < n + 1 := Nat.lt_trans hj (Nat.lt_succ_self n)
  simp [finiteProbabilitySequence, hj, hjfull]

end ECRuntime
