import Mathlib

namespace ECRuntime

/-!
# Stage 26 fix 69: recursive geometric-prefix tail table

The previous Stage-26 route constructs an explicit multi-coordinate coupling between
an adaptive EC trajectory and independent geometric waiting times.  That construction
is retained, but fix 69 opens a shorter Bellman/tail route.

For a sequence of success probabilities `p 0, p 1, ...`,
`geometricPrefixTailRec p n k` is the tail table characterized by

* zero remaining levels: tail `0`;
* a positive number of remaining one-based waits exceeds threshold zero with
  probability `1`;
* at level `n+1`, one transition is a failure with probability `1-p n` and a success
  with probability `p n`.

Thus

`B (n+1) (k+1) = (1-p n) * B (n+1) k + p n * B n k`.

This file deliberately treats the table algebraically.  The important new fact for the
direct fitness-level proof is that adding a positive waiting phase can only increase
this tail, even when the level probabilities are nonuniform.  The separate remaining
probability theorem is to identify the full-prefix table with the natural-threshold
tail of `geometricWaitingSumMeasure`.
-/

/-- Recursive real-valued tail table for a sequential family of one-based geometric
waiting phases.  The first argument after `p` is the number of phases. -/
def geometricPrefixTailRec (p : Nat -> Real) : Nat -> Nat -> Real
  | 0, _ => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 =>
      (1 - p n) * geometricPrefixTailRec p (n + 1) k +
        p n * geometricPrefixTailRec p n k

@[simp] theorem geometricPrefixTailRec_zero_levels
    (p : Nat -> Real) (k : Nat) :
    geometricPrefixTailRec p 0 k = 0 := by
  cases k <;> rfl

@[simp] theorem geometricPrefixTailRec_positive_zero
    (p : Nat -> Real) (n : Nat) :
    geometricPrefixTailRec p (n + 1) 0 = 1 := by
  rfl

@[simp] theorem geometricPrefixTailRec_succ_succ
    (p : Nat -> Real) (n k : Nat) :
    geometricPrefixTailRec p (n + 1) (k + 1) =
      (1 - p n) * geometricPrefixTailRec p (n + 1) k +
        p n * geometricPrefixTailRec p n k := by
  rfl

/-- The recursive table is nonnegative whenever every supplied success probability
lies in `[0,1]`. -/
theorem geometricPrefixTailRec_nonneg
    (p : Nat -> Real)
    (hp0 : forall n, 0 <= p n) (hp1 : forall n, p n <= 1) :
    forall k n, 0 <= geometricPrefixTailRec p n k := by
  intro k
  induction k with
  | zero =>
      intro n
      cases n <;> simp
  | succ k ih =>
      intro n
      cases n with
      | zero => simp
      | succ n =>
          rw [geometricPrefixTailRec_succ_succ]
          exact add_nonneg
            (mul_nonneg (sub_nonneg.mpr (hp1 n)) (ih (n + 1)))
            (mul_nonneg (hp0 n) (ih n))

/-- Adding one more positive waiting phase can only increase the recursive tail.  The
proof is purely algebraic and does not require the probabilities of adjacent levels to
be ordered. -/
theorem geometricPrefixTailRec_mono_level
    (p : Nat -> Real)
    (hp0 : forall n, 0 <= p n) (hp1 : forall n, p n <= 1) :
    forall k n,
      geometricPrefixTailRec p n k <=
        geometricPrefixTailRec p (n + 1) k := by
  intro k
  induction k with
  | zero =>
      intro n
      cases n <;> simp
  | succ k ih =>
      intro n
      cases n with
      | zero =>
          exact geometricPrefixTailRec_nonneg p hp0 hp1 (k + 1) 1
      | succ n =>
          have hleft :
              geometricPrefixTailRec p (n + 1) (k + 1) <=
                geometricPrefixTailRec p (n + 1) k := by
            rw [geometricPrefixTailRec_succ_succ]
            have hmul := mul_le_mul_of_nonneg_left
              (ih n) (hp0 n)
            calc
              (1 - p n) * geometricPrefixTailRec p (n + 1) k +
                    p n * geometricPrefixTailRec p n k <=
                  (1 - p n) * geometricPrefixTailRec p (n + 1) k +
                    p n * geometricPrefixTailRec p (n + 1) k := by
                exact add_le_add (le_refl _) hmul
              _ = geometricPrefixTailRec p (n + 1) k := by ring
          have hright :
              geometricPrefixTailRec p (n + 1) k <=
                geometricPrefixTailRec p (n + 2) (k + 1) := by
            rw [geometricPrefixTailRec_succ_succ]
            have hmul := mul_le_mul_of_nonneg_left
              (ih (n + 1)) (sub_nonneg.mpr (hp1 (n + 1)))
            calc
              geometricPrefixTailRec p (n + 1) k =
                  (1 - p (n + 1)) * geometricPrefixTailRec p (n + 1) k +
                    p (n + 1) * geometricPrefixTailRec p (n + 1) k := by ring
              _ <=
                  (1 - p (n + 1)) * geometricPrefixTailRec p (n + 2) k +
                    p (n + 1) * geometricPrefixTailRec p (n + 1) k := by
                exact add_le_add hmul (le_refl _)
          exact hleft.trans hright

/-- Monotonicity for an arbitrary increase in the number of waiting phases. -/
theorem geometricPrefixTailRec_mono_level_of_le
    (p : Nat -> Real)
    (hp0 : forall n, 0 <= p n) (hp1 : forall n, p n <= 1)
    (k : Nat) {a b : Nat} (hab : a <= b) :
    geometricPrefixTailRec p a k <= geometricPrefixTailRec p b k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev :
          geometricPrefixTailRec p a k <=
            geometricPrefixTailRec p (a + d) k :=
        ih (by omega)
      have hstep := geometricPrefixTailRec_mono_level p hp0 hp1 k (a + d)
      simpa [Nat.add_assoc, Nat.succ_eq_add_one] using hprev.trans hstep

/-- Extend a finite level-indexed probability vector to the natural numbers.  Values
outside the finite range are set to one; they are never used by the bounded-potential
application. -/
def finiteProbabilitySequence {m : Nat} (p : Fin m -> Real) (n : Nat) : Real :=
  if h : n < m then p ⟨n, h⟩ else 1

@[simp] theorem finiteProbabilitySequence_fin
    {m : Nat} (p : Fin m -> Real) (i : Fin m) :
    finiteProbabilitySequence p i.val = p i := by
  simp [finiteProbabilitySequence, i.isLt]

/-- The finite-vector comparison tail used by the direct Stage-26 proof. -/
def finiteGeometricComparisonTail {m : Nat}
    (p : Fin m -> Real) (n k : Nat) : Real :=
  geometricPrefixTailRec (finiteProbabilitySequence p) n k

@[simp] theorem finiteGeometricComparisonTail_zero_levels
    {m : Nat} (p : Fin m -> Real) (k : Nat) :
    finiteGeometricComparisonTail p 0 k = 0 := by
  simp [finiteGeometricComparisonTail]

@[simp] theorem finiteGeometricComparisonTail_positive_zero
    {m : Nat} (p : Fin m -> Real) (n : Nat) :
    finiteGeometricComparisonTail p (n + 1) 0 = 1 := by
  simp [finiteGeometricComparisonTail]

/-- Inside the finite level range, the comparison recursion uses exactly the supplied
coordinate probability. -/
theorem finiteGeometricComparisonTail_succ_succ
    {m : Nat} (p : Fin m -> Real) (n k : Nat) (hn : n < m) :
    finiteGeometricComparisonTail p (n + 1) (k + 1) =
      (1 - p ⟨n, hn⟩) * finiteGeometricComparisonTail p (n + 1) k +
        p ⟨n, hn⟩ * finiteGeometricComparisonTail p n k := by
  unfold finiteGeometricComparisonTail
  rw [geometricPrefixTailRec_succ_succ]
  simp [finiteProbabilitySequence, hn]

/-- Nonnegativity of the finite-vector comparison tail. -/
theorem finiteGeometricComparisonTail_nonneg
    {m : Nat} (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1) :
    forall k n, 0 <= finiteGeometricComparisonTail p n k := by
  intro k n
  apply geometricPrefixTailRec_nonneg
    (finiteProbabilitySequence p)
  · intro j
    unfold finiteProbabilitySequence
    split_ifs with hj
    · exact hp0 ⟨j, hj⟩
    · norm_num
  · intro j
    unfold finiteProbabilitySequence
    split_ifs with hj
    · exact hp1 ⟨j, hj⟩
    · norm_num

/-- Prefix monotonicity for the finite-vector comparison table. -/
theorem finiteGeometricComparisonTail_mono_level_of_le
    {m : Nat} (p : Fin m -> Real)
    (hp0 : forall i, 0 <= p i) (hp1 : forall i, p i <= 1)
    (k : Nat) {a b : Nat} (hab : a <= b) :
    finiteGeometricComparisonTail p a k <=
      finiteGeometricComparisonTail p b k := by
  unfold finiteGeometricComparisonTail
  apply geometricPrefixTailRec_mono_level_of_le
    (finiteProbabilitySequence p)
  · intro j
    unfold finiteProbabilitySequence
    split_ifs with hj
    · exact hp0 ⟨j, hj⟩
    · norm_num
  · intro j
    unfold finiteProbabilitySequence
    split_ifs with hj
    · exact hp1 ⟨j, hj⟩
    · norm_num
  · exact hab

end ECRuntime
