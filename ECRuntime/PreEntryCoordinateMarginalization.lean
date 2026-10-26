import ECRuntime.PreEntryConditionalFreshness
import ECRuntime.FiniteTrajectoryConsistency
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 26 fix 35: exact marginalization of the inactive pre-entry coordinate

Stage 26 fix 34 compiler-verifies the ratio-free finite-family factorization at the
history-dependent first entry.  To turn that generic finite family into an actual
marginal, this module enumerates every Boolean prefix of the inactive coordinate.

A finite Boolean trajectory is embedded into a total Nat-indexed stream by padding it
with `false` after its horizon.  Only the first `T` entries are observed, so the padding
is irrelevant.  The scalar Bernoulli prefix weights of all such length-`T` prefixes sum
to one.  Combining this normalization with the fix-34 finite-family theorem removes the
entire pre-entry coordinate from the adaptive coupled prefix exactly.

The final lemmas also allow an arbitrary coordinate-independent continuation mass to be
carried through this marginalization.  This is the form needed next: for a fixed real
first-entry history and realized entry state, the post-entry first-success/geometric
suffix mass is independent of the discarded pre-entry coordinate pattern.
-/

/-- Embed a finite Boolean prefix as a total transition-indexed stream, padding with
`false` after the finite horizon. -/
def finiteBoolPrefixStream {T : Nat}
    (coord : FiniteTrajectory Bool T) : Nat -> Bool :=
  fun t => if ht : t < T then coord (Fin.mk t ht) else false

/-- Before the last position of a `Fin.snoc` extension, the embedded stream agrees with
that of the original prefix. -/
theorem finiteBoolPrefixStream_snoc_of_lt
    {T : Nat} (pref : FiniteTrajectory Bool T) (b : Bool)
    {t : Nat} (ht : t < T) :
    finiteBoolPrefixStream (Fin.snoc pref b) t =
      finiteBoolPrefixStream pref t := by
  have htSucc : t < T + 1 := lt_trans ht (Nat.lt_succ_self T)
  unfold finiteBoolPrefixStream
  simp only [dif_pos htSucc, dif_pos ht]
  have hidx :
      (Fin.mk t htSucc : Fin (T + 1)) = (Fin.mk t ht).castSucc := by
    apply Fin.ext
    rfl
  rw [hidx]
  exact Fin.snoc_castSucc (n := T) (α := fun _ => Bool) b pref (Fin.mk t ht)

/-- The new last coordinate of a `Fin.snoc` extension appears at transition index `T`. -/
@[simp] theorem finiteBoolPrefixStream_snoc_last
    {T : Nat} (pref : FiniteTrajectory Bool T) (b : Bool) :
    finiteBoolPrefixStream (Fin.snoc pref b) T = b := by
  have htSucc : T < T + 1 := Nat.lt_succ_self T
  unfold finiteBoolPrefixStream
  simp only [dif_pos htSucc]
  have hidx : (Fin.mk T htSucc : Fin (T + 1)) = Fin.last T := by
    apply Fin.ext
    rfl
  rw [hidx]
  simp

/-- The existing range-product Bernoulli prefix weight obeys the expected append
recursion when a finite Boolean prefix is extended with one last bit. -/
theorem bernoulliBoolPrefixWeight_finiteBoolPrefixStream_snoc
    (q : Real) {T : Nat}
    (pref : FiniteTrajectory Bool T) (b : Bool) :
    bernoulliBoolPrefixWeight q
        (finiteBoolPrefixStream (Fin.snoc pref b)) (T + 1) =
      bernoulliBoolPrefixWeight q (finiteBoolPrefixStream pref) T *
        bernoulliBoolWeight q b := by
  unfold bernoulliBoolPrefixWeight
  rw [Finset.prod_range_succ]
  rw [finiteBoolPrefixStream_snoc_last]
  congr 1
  apply Finset.prod_congr rfl
  intro t ht
  have htT : t < T := Finset.mem_range.mp ht
  rw [finiteBoolPrefixStream_snoc_of_lt pref b htT]

/-- The Bernoulli prefix weights of all Boolean prefixes of a fixed finite horizon have
total mass one.  This is the concrete exhaustive family needed by fix 34. -/
theorem sum_bernoulliBoolPrefixWeight_finiteBoolPrefixStream
    (q : Real) :
    forall T : Nat,
      (Finset.univ.sum fun coord : FiniteTrajectory Bool T =>
        bernoulliBoolPrefixWeight q (finiteBoolPrefixStream coord) T) = 1 := by
  intro T
  induction T with
  | zero =>
      simp [bernoulliBoolPrefixWeight]
  | succ T ih =>
      rw [sum_finiteTrajectory_snoc]
      simp_rw [bernoulliBoolPrefixWeight_finiteBoolPrefixStream_snoc]
      calc
        (Finset.univ.sum fun b : Bool =>
          Finset.univ.sum fun pref : FiniteTrajectory Bool T =>
            bernoulliBoolPrefixWeight q (finiteBoolPrefixStream pref) T *
              bernoulliBoolWeight q b) =
            Finset.univ.sum fun b : Bool =>
              (Finset.univ.sum fun pref : FiniteTrajectory Bool T =>
                bernoulliBoolPrefixWeight q (finiteBoolPrefixStream pref) T) *
                  bernoulliBoolWeight q b := by
              apply Finset.sum_congr rfl
              intro b _hb
              rw [Finset.sum_mul]
        _ = Finset.univ.sum fun b : Bool => bernoulliBoolWeight q b := by
              simp [ih]
        _ = 1 := sum_bernoulliBoolWeight q

/-- Summing the adaptive coupled prefix over every possible value of the inactive
coordinate prefix removes that coordinate exactly on any horizon no later than first
entry. -/
theorem sum_all_preEntryCoordinatePrefixes_before_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (T : Nat)
    (hT : T <= firstExactLevelEntryTime V x path i hvisit) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool T =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord)) T) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels T := by
  rw [sum_multiLevelBernoulliCoupledPrefixWeight_update_coordinate_before_firstEntry
    P V hbound p x path labels i hvisit
    (fun coord : FiniteTrajectory Bool T => finiteBoolPrefixStream coord) T hT]
  rw [sum_bernoulliBoolPrefixWeight_finiteBoolPrefixStream (p i) T]
  rw [one_mul]

/-- Exact first-entry specialization of complete pre-entry-coordinate marginalization. -/
theorem sum_all_preEntryCoordinatePrefixes_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool
        (firstExactLevelEntryTime V x path i hvisit) =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord))
          (firstExactLevelEntryTime V x path i hvisit)) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels
          (firstExactLevelEntryTime V x path i hvisit) := by
  exact
    sum_all_preEntryCoordinatePrefixes_before_firstEntry
      P V hbound p x path labels i hvisit
      (firstExactLevelEntryTime V x path i hvisit) le_rfl

/-- An arbitrary continuation mass that is independent of the discarded coordinate
prefix passes through complete pre-entry-coordinate marginalization. -/
theorem sum_all_preEntryCoordinatePrefixes_mul_constant_before_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (T : Nat)
    (hT : T <= firstExactLevelEntryTime V x path i hvisit)
    (postMass : Real) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool T =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord)) T * postMass) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels T * postMass := by
  calc
    (Finset.univ.sum fun coord : FiniteTrajectory Bool T =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord)) T * postMass) =
        (Finset.univ.sum fun coord : FiniteTrajectory Bool T =>
          multiLevelBernoulliCoupledPrefixWeight
            P V hbound p x path
              (updateLabelCoordinateStream labels i
                (finiteBoolPrefixStream coord)) T) * postMass := by
          rw [Finset.sum_mul]
    _ = preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels T * postMass := by
      rw [sum_all_preEntryCoordinatePrefixes_before_firstEntry
        P V hbound p x path labels i hvisit T hT]

/-- Exact first-entry form carrying a coordinate-independent post-entry suffix mass.
The next slice can instantiate `postMass` with the fixed-restart geometric pattern mass
at the realized entry state. -/
theorem sum_all_preEntryCoordinatePrefixes_mul_constant_to_firstEntry
    {alpha : Type*} [Fintype alpha] {m : Nat}
    (P : TransitionMatrix alpha)
    (V : alpha -> Nat) (hbound : forall z, V z <= m)
    (p : Fin m -> Real)
    (x : alpha) (path : Nat -> alpha)
    (labels : Nat -> (Fin m -> Bool))
    (i : Fin m)
    (hvisit : Exists fun s =>
      V (transitionTrajectoryState x path s) = i.val + 1)
    (postMass : Real) :
    (Finset.univ.sum fun coord : FiniteTrajectory Bool
        (firstExactLevelEntryTime V x path i hvisit) =>
      multiLevelBernoulliCoupledPrefixWeight
        P V hbound p x path
          (updateLabelCoordinateStream labels i
            (finiteBoolPrefixStream coord))
          (firstExactLevelEntryTime V x path i hvisit) * postMass) =
      preEntryInactiveCoordinateComplementPrefixWeight
        P V hbound p i x path labels
          (firstExactLevelEntryTime V x path i hvisit) * postMass := by
  exact
    sum_all_preEntryCoordinatePrefixes_mul_constant_before_firstEntry
      P V hbound p x path labels i hvisit
      (firstExactLevelEntryTime V x path i hvisit) le_rfl postMass

end ECRuntime
