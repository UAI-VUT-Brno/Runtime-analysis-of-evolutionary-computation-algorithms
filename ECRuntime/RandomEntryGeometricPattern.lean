import ECRuntime.PreEntryCoordinateMarginalization
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 36: geometric post-entry patterns at a history-dependent entry

Stage 26 fix 35 fix 3 compiler-verifies exact marginalization of every value of an
inactive comparison coordinate before the actual first visit of exact level `i+1`.
The next random-entry step must attach the post-entry comparison pattern used by a
geometric waiting time: `r` failures followed by one success.

This module isolates that algebra without yet summing over real first-entry histories.
It proves that the scalar Bernoulli prefix weight of `r` failures followed by success is
exactly `(1-q)^r * q`, then instantiates the fix-35 marginalization theorem with this
post-entry mass.  Thus, for every fixed real first-entry history, summing out all
pre-entry values of coordinate `i` leaves the complementary history weight multiplied
by the geometric singleton factor.  A final normalized-mixture lemma records the exact
finite-history summation shape needed by the next slice.

No stopping-time independence theorem is assumed: freshness is still obtained from the
verified inactive-coordinate factorization before first entry.
-/

/-- Transition-indexed scalar comparison pattern consisting of `r` failures followed by
one success.  Values after the success are irrelevant to the prefix theorem below. -/
def failuresThenSuccessCoordinate (r : Nat) : Nat -> Bool :=
  fun t => if t = r then true else false

@[simp] theorem failuresThenSuccessCoordinate_at (r : Nat) :
    failuresThenSuccessCoordinate r r = true := by
  simp [failuresThenSuccessCoordinate]

theorem failuresThenSuccessCoordinate_of_lt
    {t r : Nat} (htr : t < r) :
    failuresThenSuccessCoordinate r t = false := by
  have hne : t ≠ r := Nat.ne_of_lt htr
  simp [failuresThenSuccessCoordinate, hne]

/-- A scalar Bernoulli stream that is false throughout a prefix of length `r` has
weight `(1-q)^r`. -/
theorem bernoulliBoolPrefixWeight_allFalse
    (q : Real) : forall r : Nat,
    bernoulliBoolPrefixWeight q (fun _ => false) r = (1 - q) ^ r := by
  intro r
  induction r with
  | zero =>
      simp [bernoulliBoolPrefixWeight]
  | succ r ih =>
      unfold bernoulliBoolPrefixWeight
      rw [Finset.prod_range_succ]
      change
        bernoulliBoolPrefixWeight q (fun _ => false) r *
            bernoulliBoolWeight q false =
          (1 - q) ^ (Nat.succ r)
      rw [ih, bernoulliBoolWeight_false, pow_succ]

/-- Exact scalar Bernoulli mass of `r` failures followed by one success. -/
theorem bernoulliBoolPrefixWeight_failuresThenSuccess
    (q : Real) (r : Nat) :
    bernoulliBoolPrefixWeight q (failuresThenSuccessCoordinate r) (r + 1) =
      (1 - q) ^ r * q := by
  unfold bernoulliBoolPrefixWeight
  rw [Finset.prod_range_succ]
  have hfail :
      (∏ t ∈ Finset.range r,
        bernoulliBoolWeight q (failuresThenSuccessCoordinate r t)) =
        (1 - q) ^ r := by
    calc
      (∏ t ∈ Finset.range r,
          bernoulliBoolWeight q (failuresThenSuccessCoordinate r t)) =
          bernoulliBoolPrefixWeight q (fun _ => false) r := by
            unfold bernoulliBoolPrefixWeight
            apply Finset.prod_congr rfl
            intro t ht
            have htr : t < r := Finset.mem_range.mp ht
            rw [failuresThenSuccessCoordinate_of_lt htr]
      _ = (1 - q) ^ r := bernoulliBoolPrefixWeight_allFalse q r
  rw [hfail, failuresThenSuccessCoordinate_at, bernoulliBoolWeight_true]

/-- Before first entry, complete marginalization of the inactive coordinate can carry the
geometric `r`-failures-then-success mass as an independent continuation factor. -/
theorem sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccessWeight_before_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (T r : Nat)
    (hT : T <= firstExactLevelEntryTime V x path i hvisit) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool T =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord)) T *
        bernoulliBoolPrefixWeight (p i)
          (failuresThenSuccessCoordinate r) (r + 1)) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels T *
          ((1 - p i) ^ r * p i) := by
  rw [sum_all_preEntryCoordinatePrefixes_mul_constant_before_firstEntry
    P V hbound p x path labels i hvisit T hT
      (bernoulliBoolPrefixWeight (p i)
        (failuresThenSuccessCoordinate r) (r + 1))]
  rw [bernoulliBoolPrefixWeight_failuresThenSuccess]

/-- Exact first-entry specialization: once the real history and realized entry state are
fixed, summing every inactive pre-entry coordinate prefix leaves precisely the common
first-entry-history complement times the geometric singleton factor. -/
theorem sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccessWeight_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (r : Nat) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool
        (firstExactLevelEntryTime V x path i hvisit) =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord))
          (firstExactLevelEntryTime V x path i hvisit) *
        bernoulliBoolPrefixWeight (p i)
          (failuresThenSuccessCoordinate r) (r + 1)) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels
          (firstExactLevelEntryTime V x path i hvisit) *
        ((1 - p i) ^ r * p i) := by
  exact
    sum_all_preEntryCoordinatePrefixes_mul_failuresThenSuccessWeight_before_firstEntry
      P V hbound p x path labels i hvisit
      (firstExactLevelEntryTime V x path i hvisit) r le_rfl

/-- A normalized finite mixture of fixed first-entry histories preserves the geometric
`r`-failure/success mass.  The next slice only has to instantiate `w` by the concrete
first-entry-history weights and prove their normalization. -/
theorem finiteProbabilityMixture_failuresThenSuccessWeight
    {beta : Type*} [Fintype beta]
    (w : beta -> Real) (q : Real) (r : Nat)
    (hw : Finset.univ.sum w = 1) :
    (Finset.univ.sum fun a =>
      w a * bernoulliBoolPrefixWeight q
        (failuresThenSuccessCoordinate r) (r + 1)) =
      (1 - q) ^ r * q := by
  calc
    (Finset.univ.sum fun a =>
      w a * bernoulliBoolPrefixWeight q
        (failuresThenSuccessCoordinate r) (r + 1)) =
        bernoulliBoolPrefixWeight q
          (failuresThenSuccessCoordinate r) (r + 1) :=
      finiteProbabilityMixture_constant w
        (bernoulliBoolPrefixWeight q
          (failuresThenSuccessCoordinate r) (r + 1)) hw
    _ = (1 - q) ^ r * q :=
      bernoulliBoolPrefixWeight_failuresThenSuccess q r

end ECRuntime
