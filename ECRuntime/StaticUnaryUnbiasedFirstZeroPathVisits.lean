import ECRuntime.StaticUnaryUnbiasedFirstZeroWeightedVisits
import ECRuntime.FiniteTrajectory
import ECRuntime.FiniteMarginalIdentification
import ECRuntime.FiniteTrajectoryConsistency
import ECRuntime.LeadingOnesExactStayBranch
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

section PathVisitsDecidability
attribute [local instance] Classical.propDecidable

/-!
# Stage 104: finite-path first-zero visitation (APPROVED PROOF CANDIDATE)

The user approved these nine exact theorem statements on 21 October 2026.
This is proof-development batch 6. The complete visitation/entry proof
compiled in batch 4, but batch 5 exposed an omitted endpoint-exclusion step
in a supporting Boolean case and a redundant simplifier fact. The present
revision supplies exactly that missing implication and removes the redundant
fact, preserving all nine approved theorem statements. This revision has NOT
yet been Lean-verified and remains outside the public root and promotion
guards.

Stage 103 bounds occupation by cumulative entry mass. Stage 104 proposes to
identify that mass with the probability of *ever visiting* a first-zero level
within a finite horizon, using the actual finite-trajectory law. In particular,
paths with zero weight cannot be treated as admissible dynamical trajectories.
No infinite-horizon interchange, absorption theorem, or sharp runtime bound is
asserted here.
-/

/-- The state at time `s ≤ T` along the finite tail of length `T`, with the
supplied deterministic initial state at time zero. -/
def firstZeroTrajectoryState {n : Nat} (x : BitString n)
    (T : Nat) (path : FiniteTrajectory (BitString n) T)
    (s : Fin (T + 1)) : BitString n :=
  if h : s.val = 0 then x
  else path ⟨s.val - 1, by have hs := s.isLt; omega⟩

/-- The finite trajectory occupies first-zero level `i` at least once during
`0, ..., T`, including at the supplied initial state. -/
def firstZeroTrajectoryVisited {n : Nat} (x : BitString n)
    (i : Fin n) (T : Nat) (path : FiniteTrajectory (BitString n) T) : Prop :=
  ∃ s : Fin (T + 1), firstZeroTrajectoryState x T path s ∈ firstZeroLevel i

/-- Exact finite-path probability of at least one visit to first-zero level
`i`, taken under the genuine mutation-induced transition matrix. -/
noncomputable def firstZeroTrajectoryVisitMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (i : Fin n) (T : Nat) : Real :=
  finiteEventMass
    (finiteTrajectoryWeight (law.transition (linearFitness w)) T x)
    (fun path : FiniteTrajectory (BitString n) T =>
      firstZeroTrajectoryVisited x i T path)

/-- The marginal mass of a specified state at a specified time along a finite
trajectory (a finite-path version of `firstZeroStateMass`). -/
noncomputable def firstZeroTrajectoryStateAtMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) (s : Fin (T + 1))
    (z : BitString n) : Real :=
  finiteEventMass
    (finiteTrajectoryWeight (law.transition (linearFitness w)) T x)
    (fun path : FiniteTrajectory (BitString n) T =>
      firstZeroTrajectoryState x T path s = z)

/-- (1/9) Time zero is the supplied initial state. -/
theorem firstZeroTrajectoryState_zero {n : Nat}
    (x : BitString n) (T : Nat)
    (path : FiniteTrajectory (BitString n) T) :
    firstZeroTrajectoryState x T path ⟨0, Nat.zero_lt_succ T⟩ = x := by
  simp [firstZeroTrajectoryState]

/-- (2/9) Every positive-time observation is the corresponding tail state. -/
theorem firstZeroTrajectoryState_succ {n : Nat}
    (x : BitString n) (T : Nat)
    (path : FiniteTrajectory (BitString n) T) (s : Fin T) :
    firstZeroTrajectoryState x T path
      ⟨s.val + 1, Nat.succ_lt_succ s.isLt⟩ = path s := by
  simp [firstZeroTrajectoryState]

/-- (3/9) Finite-path visitation probability is nonnegative. -/
theorem firstZeroTrajectoryVisitMass_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (i : Fin n) (T : Nat) :
    0 ≤ firstZeroTrajectoryVisitMass law w x i T := by
  classical
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  unfold firstZeroTrajectoryVisitMass finiteEventMass
  apply Finset.sum_nonneg
  intro path _
  by_cases hv : firstZeroTrajectoryVisited x i T path
  · have hmem : path ∈
        ({p : FiniteTrajectory (BitString n) T |
          firstZeroTrajectoryVisited x i T p} :
          Set (FiniteTrajectory (BitString n) T)) := hv
    rw [Set.indicator_of_mem hmem]
    exact finiteTrajectoryWeight_nonneg
      (law.transition (linearFitness w)) hP T x path
  · have hnot : path ∉
        ({p : FiniteTrajectory (BitString n) T |
          firstZeroTrajectoryVisited x i T p} :
          Set (FiniteTrajectory (BitString n) T)) := hv
    rw [Set.indicator_of_notMem hnot]

/-- (4/9) Visitation probability is at most one, with no objective
hypothesis and no positive-singleton assumption. -/
theorem firstZeroTrajectoryVisitMass_le_one {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (i : Fin n) (T : Nat) :
    firstZeroTrajectoryVisitMass law w x i T ≤ 1 := by
  classical
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  have hbound :
      firstZeroTrajectoryVisitMass law w x i T ≤
        ∑ path : FiniteTrajectory (BitString n) T,
          finiteTrajectoryWeight (law.transition (linearFitness w)) T x path := by
    unfold firstZeroTrajectoryVisitMass finiteEventMass
    apply Finset.sum_le_sum
    intro path _
    by_cases hv : firstZeroTrajectoryVisited x i T path
    · have hmem : path ∈
          ({p : FiniteTrajectory (BitString n) T |
            firstZeroTrajectoryVisited x i T p} :
            Set (FiniteTrajectory (BitString n) T)) := hv
      rw [Set.indicator_of_mem hmem]
    · have hnot : path ∉
          ({p : FiniteTrajectory (BitString n) T |
            firstZeroTrajectoryVisited x i T p} :
            Set (FiniteTrajectory (BitString n) T)) := hv
      rw [Set.indicator_of_notMem hnot]
      exact finiteTrajectoryWeight_nonneg
        (law.transition (linearFitness w)) hP T x path
  rw [finiteTrajectoryWeight_sum (law.transition (linearFitness w)) hP T x] at hbound
  exact hbound

/-! ## Finite-path marginals

The existing finite-state marginal uses the forward Chapman-Kolmogorov
recursion.  We identify it with the terminal coordinate of the exact
finite-trajectory weight using the already certified snoc factorization,
then remove superfluous final coordinates by projective consistency.
-/

private theorem firstZeroTrajectoryState_last_eq_endpoint {n T : Nat}
    (x : BitString n) (path : FiniteTrajectory (BitString n) T) :
    firstZeroTrajectoryState x T path
      (Fin.last T) = finiteTrajectoryEndpoint x T path := by
  cases T with
  | zero => simp [firstZeroTrajectoryState, finiteTrajectoryEndpoint]
  | succ T =>
      have hne : (Fin.last (T + 1)).val ≠ 0 := by simp
      unfold firstZeroTrajectoryState
      rw [dif_neg hne]
      apply congrArg path
      apply Fin.ext
      simp

private theorem firstZeroTrajectoryState_init {n T : Nat}
    (x : BitString n)
    (path : FiniteTrajectory (BitString n) (T + 1))
    (s : Fin (T + 1)) :
    firstZeroTrajectoryState x (T + 1) path
      (Fin.castSucc s) =
      firstZeroTrajectoryState x T (Fin.init path) s := by
  by_cases hzero : s.val = 0
  . simp [firstZeroTrajectoryState, hzero]
  . have hpred : s.val - 1 < T := by omega
    have hidx :
        (Fin.mk (s.val - 1) (by omega) : Fin (T + 1)) =
          (Fin.mk (s.val - 1) hpred).castSucc := Fin.ext rfl
    simp only [firstZeroTrajectoryState, Fin.val_castSucc, dif_neg hzero]
    rw [hidx]
    rfl

private theorem firstZeroStateMass_eq_terminalPathSum {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n -> Real)
    (x : BitString n) (T : Nat) (z : BitString n) :
    firstZeroStateMass law w x T z =
      (Finset.univ.sum fun path : FiniteTrajectory (BitString n) T =>
        if finiteTrajectoryEndpoint x T path = z then
          finiteTrajectoryWeight (law.transition (linearFitness w)) T x path
        else 0) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    law.transition (linearFitness w)
  induction T generalizing z with
  | zero =>
      by_cases hz : z = x
      · subst z
        simp [firstZeroStateMass, finiteTrajectoryEndpoint,
          finiteTrajectoryWeight]
      · have hx : x ≠ z := Ne.symm hz
        simp [firstZeroStateMass, finiteTrajectoryEndpoint, hz, hx]
  | succ T ih =>
      have hsnoc :
          (Finset.univ.sum fun path : FiniteTrajectory (BitString n) (T + 1) =>
            if finiteTrajectoryEndpoint x (T + 1) path = z then
              finiteTrajectoryWeight P (T + 1) x path else 0) =
          (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            finiteTrajectoryWeight P T x pref *
              P (finiteTrajectoryEndpoint x T pref) z) := by
        rw [sum_finiteTrajectory_snoc]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro pref _
        -- Rewrite the last-coordinate facts *before* using the general
        -- endpoint simplifier, which otherwise unfolds via `Fin.tail`.
        simp only [finiteTrajectoryEndpoint_snoc, finiteTrajectoryWeight_snoc]
        simp
      rw [hsnoc]
      change (Finset.univ.sum fun y : BitString n =>
        firstZeroStateMass law w x T y * P y z) = _
      calc
        (Finset.univ.sum fun y : BitString n =>
            firstZeroStateMass law w x T y * P y z) =
          (Finset.univ.sum fun y : BitString n =>
            (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
              if finiteTrajectoryEndpoint x T pref = y then
                finiteTrajectoryWeight P T x pref else 0) * P y z) := by
            apply Finset.sum_congr rfl
            intro y _
            rw [ih y]
        _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
              finiteTrajectoryWeight P T x pref *
                P (finiteTrajectoryEndpoint x T pref) z) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro pref _
          simp

/-- Rewrite a path marginal as an explicit conditional sum. This isolates
`Set.indicator`'s choice of decidability instance from the ordinary `if` used
in the path-consistency calculation. -/
private theorem firstZeroTrajectoryStateAtMass_eq_ite_sum {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) (s : Fin (T + 1))
    (z : BitString n) :
    firstZeroTrajectoryStateAtMass law w x T s z =
      (Finset.univ.sum fun path : FiniteTrajectory (BitString n) T =>
        if firstZeroTrajectoryState x T path s = z then
          finiteTrajectoryWeight (law.transition (linearFitness w)) T x path
        else 0) := by
  classical
  unfold firstZeroTrajectoryStateAtMass finiteEventMass
  apply Finset.sum_congr rfl
  intro path _
  by_cases hp : firstZeroTrajectoryState x T path s = z
  · have hmem : path ∈
        ({p : FiniteTrajectory (BitString n) T |
          firstZeroTrajectoryState x T p s = z} :
          Set (FiniteTrajectory (BitString n) T)) := hp
    rw [Set.indicator_of_mem hmem]
    simp [hp]
  · have hnot : path ∉
        ({p : FiniteTrajectory (BitString n) T |
          firstZeroTrajectoryState x T p s = z} :
          Set (FiniteTrajectory (BitString n) T)) := hp
    rw [Set.indicator_of_notMem hnot]
    simp [hp]

/-- (5/9) A marginal extracted from length-`T` paths agrees exactly with
 the time-`s` finite-state marginal, for every `s <= T`. -/
theorem firstZeroTrajectoryStateAtMass_eq_stateMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (T : Nat) (s : Fin (T + 1))
    (z : BitString n) :
    firstZeroTrajectoryStateAtMass law w x T s z =
      firstZeroStateMass law w x s.val z := by
  classical
  let P : TransitionMatrix (BitString n) :=
    law.transition (linearFitness w)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  induction T with
  | zero =>
      have hs : s = Fin.last 0 := Fin.ext (by omega)
      subst s
      rw [firstZeroTrajectoryStateAtMass_eq_ite_sum]
      simp only [firstZeroTrajectoryState_last_eq_endpoint]
      exact (firstZeroStateMass_eq_terminalPathSum law w x 0 z).symm
  | succ T ih =>
      by_cases hlast : s.val = T + 1
      . have hs : s = Fin.last (T + 1) := Fin.ext hlast
        subst s
        rw [firstZeroTrajectoryStateAtMass_eq_ite_sum]
        simp only [firstZeroTrajectoryState_last_eq_endpoint]
        exact (firstZeroStateMass_eq_terminalPathSum law w x (T + 1) z).symm
      . have hlt : s.val < T + 1 := by omega
        let t : Fin (T + 1) := Fin.mk s.val hlt
        have hcast : Fin.castSucc t = s := Fin.ext rfl
        have hproj := finiteTrajectoryWeight_init_expectation P hP T x
          (fun pref : FiniteTrajectory (BitString n) T =>
            if firstZeroTrajectoryState x T pref t = z then (1 : Real) else 0)
        have hsum :
            (Finset.univ.sum fun path : FiniteTrajectory (BitString n) (T + 1) =>
              if firstZeroTrajectoryState x (T + 1) path s = z then
                finiteTrajectoryWeight P (T + 1) x path else 0) =
            (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
              if firstZeroTrajectoryState x T pref t = z then
                finiteTrajectoryWeight P T x pref else 0) := by
          calc
            _ = (Finset.univ.sum fun path : FiniteTrajectory (BitString n) (T + 1) =>
              finiteTrajectoryWeight P (T + 1) x path *
                (if firstZeroTrajectoryState x T (Fin.init path) t = z
                  then (1 : Real) else 0)) := by
                apply Finset.sum_congr rfl
                intro path _
                rw [← firstZeroTrajectoryState_init x path t, hcast]
                split_ifs <;> simp
            _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
                finiteTrajectoryWeight P T x pref *
                  (if firstZeroTrajectoryState x T pref t = z
                    then (1 : Real) else 0)) := hproj
            _ = _ := by
              apply Finset.sum_congr rfl
              intro pref _
              split_ifs <;> simp
        have hprevSum :
            (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
              if firstZeroTrajectoryState x T pref t = z then
                finiteTrajectoryWeight P T x pref else 0) =
              firstZeroStateMass law w x t.val z := by
          have hbridge :=
            (firstZeroTrajectoryStateAtMass_eq_ite_sum law w x T t z).symm
          exact (by simpa [P] using hbridge.trans (ih t))
        calc
          firstZeroTrajectoryStateAtMass law w x (T + 1) s z =
              (Finset.univ.sum fun path : FiniteTrajectory (BitString n) (T + 1) =>
                if firstZeroTrajectoryState x (T + 1) path s = z then
                  finiteTrajectoryWeight P (T + 1) x path else 0) := by
                simpa [P] using
                  (firstZeroTrajectoryStateAtMass_eq_ite_sum
                    law w x (T + 1) s z)
          _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
                if firstZeroTrajectoryState x T pref t = z then
                  finiteTrajectoryWeight P T x pref else 0) := hsum
          _ = firstZeroStateMass law w x s.val z := by
                simpa [t] using hprevSum

/-- (6/9) A visited level has a first visiting time. This is purely a
finite combinatorial fact, even for paths of zero transition weight. -/
theorem firstZeroTrajectoryVisited_iff_first_visit {n : Nat}
    (x : BitString n) (i : Fin n) (T : Nat)
    (path : FiniteTrajectory (BitString n) T) :
    firstZeroTrajectoryVisited x i T path ↔
      ∃ s : Fin (T + 1),
        firstZeroTrajectoryState x T path s ∈ firstZeroLevel i ∧
          ∀ r : Fin (T + 1), r < s →
            firstZeroTrajectoryState x T path r ∉ firstZeroLevel i := by
  classical
  constructor
  · rintro ⟨s, hs⟩
    let visits : Finset (Fin (T + 1)) :=
      Finset.univ.filter (fun k =>
        firstZeroTrajectoryState x T path k ∈ firstZeroLevel i)
    have hnonempty : visits.Nonempty := by
      refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩⟩
    refine ⟨visits.min' hnonempty, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (Finset.min'_mem visits hnonempty)).2
    · intro r hr hrmem
      have hrvisits : r ∈ visits :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrmem⟩
      have hle : visits.min' hnonempty ≤ r :=
        Finset.min'_le visits r hrvisits
      exact (not_lt_of_ge hle) hr
  · rintro ⟨s, hs, _⟩
    exact ⟨s, hs⟩

/-! ## Positive-weight no-return

The transition row is a push-forward of actual deterministic elitist updates.
Consequently positive transition mass implies the existence of a mask mapping
its source to its destination.  The certified Stage 102 prefix-permanence
result therefore holds on every supported step.  We propagate it through a
finite trajectory by induction on its length, using the certified snoc
factorization to exclude zero-weight prefixes and transitions.
-/

private theorem firstZeroCorrectPrefixThrough_transition_support {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (z y : BitString n) (i : Fin n)
    (hp : firstZeroCorrectPrefixThrough z i)
    (hpos : 0 < (law.transition (linearFitness w)) z y) :
    firstZeroCorrectPrefixThrough y i := by
  classical
  by_contra hnot
  have hzero : (law.transition (linearFitness w)) z y = 0 := by
    change pushforwardWeight law.weight
      (selectedAfterMask (linearFitness w) z) y = 0
    unfold pushforwardWeight
    apply Finset.sum_eq_zero
    intro mask _
    have hne : selectedAfterMask (linearFitness w) z mask ≠ y := by
      intro heq
      apply hnot
      rw [← heq]
      exact firstZeroCorrectPrefixThrough_selected_preserves
        w hw z i hp mask
    simp [hne]
  exact (ne_of_gt hpos) hzero

private theorem firstZeroTrajectoryState_snoc_earlier {n T : Nat}
    (x : BitString n) (pref : FiniteTrajectory (BitString n) T)
    (y : BitString n) (s : Fin (T + 1)) :
    firstZeroTrajectoryState x (T + 1) (Fin.snoc pref y)
      (Fin.castSucc s) = firstZeroTrajectoryState x T pref s := by
  simpa [Fin.init_snoc] using
    (firstZeroTrajectoryState_init x (Fin.snoc pref y) s)

private theorem firstZeroTrajectoryState_snoc_final {n T : Nat}
    (x : BitString n) (pref : FiniteTrajectory (BitString n) T)
    (y : BitString n) :
    firstZeroTrajectoryState x (T + 1) (Fin.snoc pref y)
      (Fin.last (T + 1)) = y := by
  rw [firstZeroTrajectoryState_last_eq_endpoint]
  exact finiteTrajectoryEndpoint_snoc x T pref y

private theorem firstZeroTrajectory_prefix_persistent {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (i : Fin n) (x : BitString n) (T : Nat)
    (path : FiniteTrajectory (BitString n) T)
    (hpos : 0 < finiteTrajectoryWeight
      (law.transition (linearFitness w)) T x path)
    (r s : Fin (T + 1)) (hrs : r <= s)
    (hp : firstZeroCorrectPrefixThrough
      (firstZeroTrajectoryState x T path r) i) :
    firstZeroCorrectPrefixThrough
      (firstZeroTrajectoryState x T path s) i := by
  classical
  let P : TransitionMatrix (BitString n) :=
    law.transition (linearFitness w)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  induction T generalizing x with
  | zero =>
      have heq : r = s := Fin.ext (by omega)
      subst s
      exact hp
  | succ T ih =>
      let pref : FiniteTrajectory (BitString n) T := Fin.init path
      let y : BitString n := path (Fin.last T)
      have hpath : path = Fin.snoc pref y := by
        exact (Fin.snoc_init_self path).symm
      have hmul : 0 < finiteTrajectoryWeight P T x pref *
          P (finiteTrajectoryEndpoint x T pref) y := by
        simpa [P, hpath, finiteTrajectoryWeight_snoc] using hpos
      have hpreNonneg : 0 <= finiteTrajectoryWeight P T x pref :=
        finiteTrajectoryWeight_nonneg P hP T x pref
      have htransNonneg : 0 <= P (finiteTrajectoryEndpoint x T pref) y :=
        hP.1 _ _
      have hprePos : 0 < finiteTrajectoryWeight P T x pref := by
        have hne : finiteTrajectoryWeight P T x pref ≠ 0 := by
          intro hz
          simp [hz] at hmul
        exact lt_of_le_of_ne hpreNonneg (Ne.symm hne)
      have htransPos : 0 < P (finiteTrajectoryEndpoint x T pref) y := by
        have hne : P (finiteTrajectoryEndpoint x T pref) y ≠ 0 := by
          intro hz
          simp [hz] at hmul
        exact lt_of_le_of_ne htransNonneg (Ne.symm hne)
      by_cases hlast : s.val = T + 1
      . have hs : s = Fin.last (T + 1) := Fin.ext hlast
        subst s
        by_cases hrLast : r.val = T + 1
        . have hr : r = Fin.last (T + 1) := Fin.ext hrLast
          subst r
          exact hp
        . have hrBound : r.val < T + 1 := by omega
          let r0 : Fin (T + 1) := Fin.mk r.val hrBound
          have hr : Fin.castSucc r0 = r := Fin.ext rfl
          have hrBefore : r0 <= Fin.last T := by
            change r0.val <= (Fin.last T).val
            dsimp [r0]
            omega
          have hprev : firstZeroCorrectPrefixThrough
              (firstZeroTrajectoryState x T pref (Fin.last T)) i := by
            apply ih x pref hprePos r0 (Fin.last T) hrBefore
            simpa [hpath, ← hr, firstZeroTrajectoryState_snoc_earlier] using hp
          have hendpoint : firstZeroCorrectPrefixThrough
              (finiteTrajectoryEndpoint x T pref) i := by
            simpa [firstZeroTrajectoryState_last_eq_endpoint] using hprev
          have hnext := firstZeroCorrectPrefixThrough_transition_support
            law w hw (finiteTrajectoryEndpoint x T pref) y i
            hendpoint htransPos
          simpa [hpath, firstZeroTrajectoryState_snoc_final] using hnext
      . have hsBound : s.val < T + 1 := by omega
        have hrBound : r.val < T + 1 := by omega
        let s0 : Fin (T + 1) := Fin.mk s.val hsBound
        let r0 : Fin (T + 1) := Fin.mk r.val hrBound
        have hs : Fin.castSucc s0 = s := Fin.ext rfl
        have hr : Fin.castSucc r0 = r := Fin.ext rfl
        have hrs0 : r0 <= s0 := by
          change r0.val <= s0.val
          dsimp [r0, s0]
          exact hrs
        have hnew := ih x pref hprePos r0 s0 hrs0
          (by simpa [hpath, ← hr, firstZeroTrajectoryState_snoc_earlier] using hp)
        simpa [hpath, ← hs, firstZeroTrajectoryState_snoc_earlier] using hnew

/-- (7/9) Under positive trajectory weight, a superincreasing elitist walk
 cannot return to a first-zero level after leaving it. -/
theorem firstZeroTrajectory_no_return {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (T : Nat)
    (path : FiniteTrajectory (BitString n) T)
    (hpos : 0 < finiteTrajectoryWeight
      (law.transition (linearFitness w)) T x path)
    (r s u : Fin (T + 1)) (hrs : r < s) (hsu : s ≤ u)
    (hr : firstZeroTrajectoryState x T path r ∈ firstZeroLevel i)
    (hs : firstZeroTrajectoryState x T path s ∉ firstZeroLevel i) :
    firstZeroTrajectoryState x T path u ∉ firstZeroLevel i := by
  have hpBefore : firstZeroPrefixOnes
      (firstZeroTrajectoryState x T path s) i := by
    intro j hj
    have hpAtR : firstZeroCorrectPrefixThrough
        (firstZeroTrajectoryState x T path r) j := by
      intro k hk
      exact hr.1 k (lt_of_le_of_lt hk hj)
    have hpAtS := firstZeroTrajectory_prefix_persistent
      law w hw j x T path hpos r s (le_of_lt hrs) hpAtR
    exact hpAtS j (le_refl _)
  have hi : firstZeroTrajectoryState x T path s i = true := by
    cases hb : firstZeroTrajectoryState x T path s i with
    | true => rfl
    | false =>
        exact False.elim (hs (And.intro hpBefore hb))
  have hthrough : firstZeroCorrectPrefixThrough
      (firstZeroTrajectoryState x T path s) i := by
    intro j hj
    rcases lt_or_eq_of_le hj with hlt | heq
    . exact hpBefore j hlt
    . have hji : j = i := Fin.ext heq
      subst j
      exact hi
  have hthroughU := firstZeroTrajectory_prefix_persistent
    law w hw i x T path hpos s u hsu hthrough
  exact firstZeroCorrectPrefixThrough_not_level _ i hthroughU


/-! ## Visitation/entry reconciliation

The finite path law is stochastic, so marginalizing its last coordinate
recovers the shorter law.  Every positive-weight first-zero trajectory has
at most one outside-to-inside entry: once it has exited a level it cannot
return.  We prove the finite-horizon visitation/entry identity by separating
an earlier visit from a first entry during the terminal transition.  No
infinite-path measure, conditional mutation law, or independence is used.
-/

private theorem firstZeroTrajectoryVisitMass_eq_ite_sum {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n -> Real)
    (x : BitString n) (i : Fin n) (T : Nat) :
    firstZeroTrajectoryVisitMass law w x i T =
      (Finset.univ.sum fun path : FiniteTrajectory (BitString n) T =>
        if firstZeroTrajectoryVisited x i T path then
          finiteTrajectoryWeight (law.transition (linearFitness w)) T x path
        else 0) := by
  classical
  unfold firstZeroTrajectoryVisitMass finiteEventMass
  apply Finset.sum_congr rfl
  intro path _
  by_cases hp : firstZeroTrajectoryVisited x i T path
  . have hmem : path ∈
        ({p : FiniteTrajectory (BitString n) T |
          firstZeroTrajectoryVisited x i T p} :
          Set (FiniteTrajectory (BitString n) T)) := hp
    rw [Set.indicator_of_mem hmem]
    simp [hp]
  . have hnot : path ∉
        ({p : FiniteTrajectory (BitString n) T |
          firstZeroTrajectoryVisited x i T p} :
          Set (FiniteTrajectory (BitString n) T)) := hp
    rw [Set.indicator_of_notMem hnot]
    simp [hp]

private theorem firstZeroTrajectoryVisited_snoc_iff {n T : Nat}
    (x : BitString n) (i : Fin n)
    (pref : FiniteTrajectory (BitString n) T) (y : BitString n) :
    firstZeroTrajectoryVisited x i (T + 1) (Fin.snoc pref y) <->
      firstZeroTrajectoryVisited x i T pref ∨ y ∈ firstZeroLevel i := by
  constructor
  . rintro ⟨s, hs⟩
    by_cases hlast : s.val = T + 1
    . right
      have hs' : s = Fin.last (T + 1) := Fin.ext hlast
      simpa [hs', firstZeroTrajectoryState_snoc_final] using hs
    . left
      have hlt : s.val < T + 1 := by omega
      let r : Fin (T + 1) := ⟨s.val, hlt⟩
      have hcast : Fin.castSucc r = s := Fin.ext rfl
      refine ⟨r, ?_⟩
      have h' : firstZeroTrajectoryState x (T + 1) (Fin.snoc pref y)
          (Fin.castSucc r) ∈ firstZeroLevel i := by
        simpa [hcast] using hs
      simpa only [firstZeroTrajectoryState_snoc_earlier] using h'
  . rintro (⟨r, hr⟩ | hy)
    . refine ⟨Fin.castSucc r, ?_⟩
      simpa only [firstZeroTrajectoryState_snoc_earlier] using hr
    . refine ⟨Fin.last (T + 1), ?_⟩
      simpa only [firstZeroTrajectoryState_snoc_final] using hy

private theorem firstZeroTrajectoryVisitMass_zero {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n -> Real)
    (x : BitString n) (i : Fin n) :
    firstZeroTrajectoryVisitMass law w x i 0 =
      firstZeroEntryMass law w x i 0 := by
  classical
  let P : TransitionMatrix (BitString n) :=
    law.transition (linearFitness w)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  have hvisit (path : FiniteTrajectory (BitString n) 0) :
      firstZeroTrajectoryVisited x i 0 path <-> x ∈ firstZeroLevel i := by
    constructor
    . rintro ⟨s, hs⟩
      have hs0 : s = ⟨0, Nat.zero_lt_succ 0⟩ := Fin.ext (by omega)
      simpa [hs0, firstZeroTrajectoryState] using hs
    . intro hx
      exact ⟨⟨0, Nat.zero_lt_succ 0⟩,
        by simpa [firstZeroTrajectoryState] using hx⟩
  rw [firstZeroTrajectoryVisitMass_eq_ite_sum]
  by_cases hx : x ∈ firstZeroLevel i
  . simp only [hvisit, if_pos hx]
    rw [finiteTrajectoryWeight_sum P hP 0 x]
    simp [firstZeroEntryMass, hx]
  . simp [hvisit, hx, firstZeroEntryMass]

/-- Positive-weight paths cannot visit a level, leave it and then enter
again on their last transition.  Its contrapositive is precisely the
zero-weight term needed in the finite-path mass computation. -/
private theorem firstZeroTrajectory_forbidden_reentry_weight_zero {n T : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n)
    (pref : FiniteTrajectory (BitString n) T) (y : BitString n)
    (hvisited : firstZeroTrajectoryVisited x i T pref)
    (hout : finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i)
    (hy : y ∈ firstZeroLevel i) :
    finiteTrajectoryWeight (law.transition (linearFitness w)) (T + 1)
      x (Fin.snoc pref y) = 0 := by
  classical
  let P : TransitionMatrix (BitString n) := law.transition (linearFitness w)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  have hn : 0 ≤ finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) :=
    finiteTrajectoryWeight_nonneg P hP (T + 1) x (Fin.snoc pref y)
  by_contra hne
  have hpos : 0 < finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) :=
    lt_of_le_of_ne hn (Ne.symm hne)
  obtain ⟨r, hr⟩ := hvisited
  have hrneq : r.val ≠ T := by
    intro heq
    have hrLast : r = Fin.last T := Fin.ext heq
    apply hout
    simpa [hrLast, firstZeroTrajectoryState_last_eq_endpoint] using hr
  have hrlt : r.val < T := by
    have hb := r.isLt
    omega
  have hrs : (Fin.castSucc r : Fin (T + 2)) <
      (Fin.castSucc (Fin.last T) : Fin (T + 2)) := by
    change r.val < T
    exact hrlt
  have hsu : (Fin.castSucc (Fin.last T) : Fin (T + 2)) ≤
      Fin.last (T + 1) := by
    change T ≤ T + 1
    omega
  have hr' : firstZeroTrajectoryState x (T + 1) (Fin.snoc pref y)
      (Fin.castSucc r) ∈ firstZeroLevel i := by
    simpa only [firstZeroTrajectoryState_snoc_earlier] using hr
  have hs' : firstZeroTrajectoryState x (T + 1) (Fin.snoc pref y)
      (Fin.castSucc (Fin.last T)) ∉ firstZeroLevel i := by
    simpa only [firstZeroTrajectoryState_snoc_earlier,
      firstZeroTrajectoryState_last_eq_endpoint] using hout
  have hu' : firstZeroTrajectoryState x (T + 1) (Fin.snoc pref y)
      (Fin.last (T + 1)) ∈ firstZeroLevel i := by
    simpa only [firstZeroTrajectoryState_snoc_final] using hy
  have hnr := firstZeroTrajectory_no_return law w hw x i (T + 1)
    (Fin.snoc pref y) hpos
    (Fin.castSucc r) (Fin.castSucc (Fin.last T)) (Fin.last (T + 1))
    hrs hsu hr' hs'
  exact hnr hu'

/-- Pointwise renewal of the visited indicator, weighted by the genuine
path law.  Its only nontrivial case has weight zero by no-return. -/
private theorem firstZeroTrajectory_visit_step_weight {n T : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n)
    (pref : FiniteTrajectory (BitString n) T) (y : BitString n) :
    (if firstZeroTrajectoryVisited x i (T + 1) (Fin.snoc pref y) then
      finiteTrajectoryWeight (law.transition (linearFitness w)) (T + 1)
        x (Fin.snoc pref y) else 0) =
    (if firstZeroTrajectoryVisited x i T pref then
      finiteTrajectoryWeight (law.transition (linearFitness w)) (T + 1)
        x (Fin.snoc pref y) else 0) +
    (if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
        y ∈ firstZeroLevel i then
      finiteTrajectoryWeight (law.transition (linearFitness w)) (T + 1)
        x (Fin.snoc pref y) else 0) := by
  classical
  by_cases hp : firstZeroTrajectoryVisited x i T pref
  . by_cases he : finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
        y ∈ firstZeroLevel i
    . have hw0 := firstZeroTrajectory_forbidden_reentry_weight_zero
        law w hw x i pref y hp he.1 he.2
      simp [firstZeroTrajectoryVisited_snoc_iff, hp, he, hw0]
    . simp [firstZeroTrajectoryVisited_snoc_iff, hp, he]
  . by_cases hy : y ∈ firstZeroLevel i
    . -- If the prefix has never visited the level, its terminal state
      -- cannot be in the level: that state is the observation at time T.
      have hout : finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i := by
        intro hend
        apply hp
        exact ⟨Fin.last T, by
          simpa only [firstZeroTrajectoryState_last_eq_endpoint] using hend⟩
      simp [firstZeroTrajectoryVisited_snoc_iff, hp, hy, hout]
    . simp [firstZeroTrajectoryVisited_snoc_iff, hp, hy]

/-- The independently defined Stage 102 one-step entry flow is exactly the
finite-path mass of outside-to-inside terminal transitions. -/
private theorem firstZeroEntryMass_succ_eq_snoc_mass {n T : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n -> Real)
    (x : BitString n) (i : Fin n) :
    firstZeroEntryMass law w x i (T + 1) =
      (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
        Finset.univ.sum fun y : BitString n =>
          if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
              y ∈ firstZeroLevel i then
            finiteTrajectoryWeight (law.transition (linearFitness w))
              (T + 1) x (Fin.snoc pref y)
          else 0) := by
  classical
  let P : TransitionMatrix (BitString n) := law.transition (linearFitness w)
  have hevent (z : BitString n) :
      finiteEventMass (P z)
        (fun y : BitString n => z ∉ firstZeroLevel i ∧
          y ∈ firstZeroLevel i) =
        (Finset.univ.sum fun y : BitString n =>
          if z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i
          then P z y else 0) := by
    unfold finiteEventMass
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i
    . have hmem : y ∈
          ({v : BitString n | z ∉ firstZeroLevel i ∧
            v ∈ firstZeroLevel i} : Set (BitString n)) := hy
      rw [Set.indicator_of_mem hmem]
      simp [hy]
    . have hnot : y ∉
          ({v : BitString n | z ∉ firstZeroLevel i ∧
            v ∈ firstZeroLevel i} : Set (BitString n)) := hy
      rw [Set.indicator_of_notMem hnot]
      simp [hy]
  change (Finset.univ.sum fun z : BitString n =>
    firstZeroStateMass law w x T z *
      finiteEventMass (P z)
        (fun y : BitString n => z ∉ firstZeroLevel i ∧
          y ∈ firstZeroLevel i)) = _
  calc
    _ = (Finset.univ.sum fun z : BitString n =>
          firstZeroStateMass law w x T z *
            (Finset.univ.sum fun y : BitString n =>
              if z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i
              then P z y else 0)) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [hevent z]
    _ = (Finset.univ.sum fun z : BitString n =>
          (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            if finiteTrajectoryEndpoint x T pref = z then
              finiteTrajectoryWeight P T x pref else 0) *
            (Finset.univ.sum fun y : BitString n =>
              if z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i
              then P z y else 0)) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [firstZeroStateMass_eq_terminalPathSum law w x T z]
    _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
          finiteTrajectoryWeight P T x pref *
            (Finset.univ.sum fun y : BitString n =>
              if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
                  y ∈ firstZeroLevel i then
                P (finiteTrajectoryEndpoint x T pref) y else 0)) := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro pref _
          simp
    _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
          Finset.univ.sum fun y : BitString n =>
            if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
                y ∈ firstZeroLevel i then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y)
            else 0) := by
          apply Finset.sum_congr rfl
          intro pref _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
              y ∈ firstZeroLevel i
          . simp [hy, finiteTrajectoryWeight_snoc]
          . simp [hy]

/-- The finite-horizon visit probability grows by precisely the mass of
new entries at the final time.  Projective consistency handles old visits;
the no-return lemma handles paths that otherwise appear to re-enter. -/
private theorem firstZeroTrajectoryVisitMass_succ_eq_add_entry {n T : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n -> Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) :
    firstZeroTrajectoryVisitMass law w x i (T + 1) =
      firstZeroTrajectoryVisitMass law w x i T +
        firstZeroEntryMass law w x i (T + 1) := by
  classical
  let P : TransitionMatrix (BitString n) := law.transition (linearFitness w)
  have hP : IsStochastic P := law.transition_stochastic (linearFitness w)
  have hsplit :
      firstZeroTrajectoryVisitMass law w x i (T + 1) =
        (Finset.univ.sum fun y : BitString n =>
          Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            (if firstZeroTrajectoryVisited x i T pref then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0) +
            (if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
                y ∈ firstZeroLevel i then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0)) := by
    rw [firstZeroTrajectoryVisitMass_eq_ite_sum]
    rw [sum_finiteTrajectory_snoc]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro pref _
    exact firstZeroTrajectory_visit_step_weight law w hw x i pref y
  have hprev :
      (Finset.univ.sum fun y : BitString n =>
        Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
          if firstZeroTrajectoryVisited x i T pref then
            finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0) =
        firstZeroTrajectoryVisitMass law w x i T := by
    rw [Finset.sum_comm]
    calc
      _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            if firstZeroTrajectoryVisited x i T pref then
              (Finset.univ.sum fun y : BitString n =>
                finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y))
            else 0) := by
            apply Finset.sum_congr rfl
            intro pref _
            by_cases hv : firstZeroTrajectoryVisited x i T pref
            . simp [hv]
            . simp [hv]
      _ = (Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            if firstZeroTrajectoryVisited x i T pref then
              finiteTrajectoryWeight P T x pref else 0) := by
            apply Finset.sum_congr rfl
            intro pref _
            rw [finiteTrajectoryWeight_snoc_sum P hP T x pref]
      _ = firstZeroTrajectoryVisitMass law w x i T :=
          (firstZeroTrajectoryVisitMass_eq_ite_sum law w x i T).symm
  have hnew :
      (Finset.univ.sum fun y : BitString n =>
        Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
          if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
              y ∈ firstZeroLevel i then
            finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0) =
        firstZeroEntryMass law w x i (T + 1) := by
    rw [Finset.sum_comm]
    exact (firstZeroEntryMass_succ_eq_snoc_mass law w x i).symm
  calc
    firstZeroTrajectoryVisitMass law w x i (T + 1) =
        (Finset.univ.sum fun y : BitString n =>
          Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            (if firstZeroTrajectoryVisited x i T pref then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0) +
            (if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
                y ∈ firstZeroLevel i then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0)) := hsplit
    _ = (Finset.univ.sum fun y : BitString n =>
          Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            if firstZeroTrajectoryVisited x i T pref then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0) +
        (Finset.univ.sum fun y : BitString n =>
          Finset.univ.sum fun pref : FiniteTrajectory (BitString n) T =>
            if finiteTrajectoryEndpoint x T pref ∉ firstZeroLevel i ∧
                y ∈ firstZeroLevel i then
              finiteTrajectoryWeight P (T + 1) x (Fin.snoc pref y) else 0) := by
          simp_rw [Finset.sum_add_distrib]
    _ = firstZeroTrajectoryVisitMass law w x i T +
          firstZeroEntryMass law w x i (T + 1) := by
          rw [hprev, hnew]

/-- (8/9) Expected cumulative entry count equals the probability of at
least one finite-horizon visit, by the no-return property. This is the
principal Stage 104 proposed bridge. -/
theorem firstZeroTrajectoryVisitMass_eq_cumulativeEntryMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (T : Nat) :
    firstZeroTrajectoryVisitMass law w x i T =
      firstZeroCumulativeEntryMass law w x i T := by
  induction T with
  | zero =>
      simpa [firstZeroCumulativeEntryMass] using
        (firstZeroTrajectoryVisitMass_zero law w x i)
  | succ T ih =>
      calc
        firstZeroTrajectoryVisitMass law w x i (T + 1) =
            firstZeroTrajectoryVisitMass law w x i T +
              firstZeroEntryMass law w x i (T + 1) :=
                firstZeroTrajectoryVisitMass_succ_eq_add_entry law w hw x i
        _ = firstZeroCumulativeEntryMass law w x i T +
              firstZeroEntryMass law w x i (T + 1) := by rw [ih]
        _ = firstZeroCumulativeEntryMass law w x i (T + 1) := by
              simp only [firstZeroCumulativeEntryMass, Finset.sum_range_succ]

/-- (9/9) The finite-horizon occupation bound now depends on actual
visitation probabilities, rather than the abstract cumulative entry masses.
This still does not imply an infinite-horizon runtime identity. -/
theorem firstZeroGlobalOccupation_horizon_le_visits {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) (hp1 : 0 < law.oneBitMass) :
    (∑ t ∈ Finset.range T, firstZeroGlobalOccupationMass law w x t) ≤
      ∑ i : Fin n,
        firstZeroTrajectoryVisitMass law w x i T /
          law.maskEventMass (lowestMaskEvent i) := by
  calc
    (∑ t ∈ Finset.range T, firstZeroGlobalOccupationMass law w x t) ≤
        ∑ i : Fin n,
          firstZeroCumulativeEntryMass law w x i T /
            law.maskEventMass (lowestMaskEvent i) :=
      firstZeroGlobalOccupation_horizon_le_weighted_entries law w hw x T hp1
    _ = ∑ i : Fin n,
          firstZeroTrajectoryVisitMass law w x i T /
            law.maskEventMass (lowestMaskEvent i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [firstZeroTrajectoryVisitMass_eq_cumulativeEntryMass law w hw x i T]

end PathVisitsDecidability
end StaticUnaryUnbiasedMutation
end ECRuntime
