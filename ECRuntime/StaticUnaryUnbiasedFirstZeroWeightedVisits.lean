import ECRuntime.StaticUnaryUnbiasedFirstZeroOccupationRenewal
import Mathlib

open scoped BigOperators

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

section WeightedVisitsDecidability
attribute [local instance] Classical.propDecidable

/-!
# Stage 103: weighted first-zero entry / global occupation (INTEGRATION CANDIDATE)

The user approved all nine theorem statements and subsequently authorized
promotion after the first strict proof attempt. The first compiler run exposed
one tactic-level elaboration mismatch in theorem (3); this integration candidate
repairs the expansion of Set.indicator without changing any theorem statement.
It is included in the root only for the next strict compiler gate. The source
is NOT claimed compiler-certified until that gate passes.

This stage builds a finite-horizon weighted-entry identity for genuine
superincreasing BinVal-type dynamics. It *does not* establish an infinite-time
runtime formula or any general-positive-linear asymptotic bound. Cumulative
entry mass is not yet identified with the probability of ever visiting the
level by a pathwise proof. The long-term target is
  E[T] = ∑ i, Pr(visit level i) / Pr(exit level i).
Keeping the terminal occupation term explicit prevents an unjustified
finite-to-infinite limit passage.
-/

/-- The unique optimum bit pattern for a positive linear objective. -/
def firstZeroAllOnes {n : Nat} (z : BitString n) : Prop :=
  ∀ j : Fin n, z j = true

/-- Exact-time mass outside the all-ones state. -/
noncomputable def firstZeroNonoptimalMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (t : Nat) : Real :=
  finiteEventMass (firstZeroStateMass law w x t)
    (fun z : BitString n => ¬ firstZeroAllOnes z)

/-- Aggregate first-zero occupation at a fixed time; level sets are disjoint. -/
noncomputable def firstZeroGlobalOccupationMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (t : Nat) : Real :=
  ∑ i : Fin n, firstZeroOccupationMass law w x i t

/-- Entry mass accumulated through time `T`, including an initial entry. -/
noncomputable def firstZeroCumulativeEntryMass {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (i : Fin n) (T : Nat) : Real :=
  ∑ s ∈ Finset.range (T + 1), firstZeroEntryMass law w x i s

/-- (1/9) Two distinct first-zero levels cannot contain the same state. -/
theorem firstZeroAt_level_unique {n : Nat} (z : BitString n)
    (i j : Fin n) (hi : firstZeroAt z i) (hj : firstZeroAt z j) :
    i = j := by
  by_cases hij : i.val < j.val
  · have htrue : z i = true := hj.1 i hij
    rw [hi.2] at htrue
    cases htrue
  by_cases hji : j.val < i.val
  · have htrue : z j = true := hi.1 j hji
    rw [hj.2] at htrue
    cases htrue
  exact Fin.ext (by omega)

/-- (2/9) A bit string has a first-zero index exactly when it is not all ones,
including the empty bit string in dimension zero. -/
theorem firstZeroAt_level_exists_iff_not_allOnes {n : Nat}
    (z : BitString n) :
    (∃ i : Fin n, z ∈ firstZeroLevel i) ↔ ¬ firstZeroAllOnes z := by
  classical
  constructor
  · rintro ⟨i, hi⟩ hall
    have htrue : z i = true := hall i
    have hfalse : z i = false := hi.2
    rw [htrue] at hfalse
    cases hfalse
  · intro hnot
    have hex : ∃ k : Fin n, z k = false := by
      by_contra h
      apply hnot
      intro k
      cases hk : z k with
      | true => rfl
      | false => exact False.elim (h ⟨k, hk⟩)
    let s : Finset (Fin n) := Finset.univ.filter (fun k => z k = false)
    have hs : s.Nonempty := by
      rcases hex with ⟨k, hk⟩
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    let i : Fin n := s.min' hs
    have hi_mem : i ∈ s := Finset.min'_mem s hs
    have hizero : z i = false := (Finset.mem_filter.mp hi_mem).2
    refine ⟨i, ?_⟩
    constructor
    · intro j hj
      cases hz : z j with
      | true => rfl
      | false =>
          have hjmem : j ∈ s :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
          have hle : i ≤ j := Finset.min'_le s j hjmem
          have hval : i.val ≤ j.val := hle
          omega
    · exact hizero

/-- (3/9) The exact-time mass outside the all-ones state is the sum of the
disjoint first-zero level occupation masses, without a fitness hypothesis. -/
theorem firstZeroGlobalOccupationMass_eq_nonoptimal {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (x : BitString n) (t : Nat) :
    firstZeroGlobalOccupationMass law w x t =
      firstZeroNonoptimalMass law w x t := by
  classical
  -- `finiteEventMass` is defined using `Set.indicator`, not a literal `if`.
  -- Unfold it explicitly before exchanging the two finite sums: a bare
  -- `change` to nested `if` expressions did not elaborate in fix 1.
  unfold firstZeroGlobalOccupationMass firstZeroNonoptimalMass
    firstZeroOccupationMass finiteEventMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hall : firstZeroAllOnes z
  · have hnone : ∀ i : Fin n, z ∉ firstZeroLevel i := by
      intro i hi
      exact ((firstZeroAt_level_exists_iff_not_allOnes z).1 ⟨i, hi⟩) hall
    simp [Set.indicator, hall, hnone]
  · obtain ⟨i, hi⟩ := (firstZeroAt_level_exists_iff_not_allOnes z).2 hall
    have hunique (j : Fin n) : (z ∈ firstZeroLevel j) ↔ j = i := by
      constructor
      · intro hj
        exact firstZeroAt_level_unique z j i hj hi
      · intro hj
        subst j
        exact hi
    simp [Set.indicator, hall, hunique]

/-- Every coordinate of the genuine finite-time law is nonnegative. -/
private theorem firstZeroStateMass_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n) (w : Fin n → Real)
    (x : BitString n) (t : Nat) (z : BitString n) :
    0 ≤ firstZeroStateMass law w x t z := by
  have hP : IsStochastic (law.transition (linearFitness w)) :=
    law.transition_stochastic (linearFitness w)
  have hall : ∀ s : Nat, ∀ y : BitString n,
      0 ≤ firstZeroStateMass law w x s y := by
    intro s
    induction s with
    | zero =>
        intro y
        by_cases hy : y = x <;> simp [firstZeroStateMass, hy]
    | succ s ih =>
        intro y
        change 0 ≤ ∑ u : BitString n,
          firstZeroStateMass law w x s u *
            (law.transition (linearFitness w)) u y
        exact Finset.sum_nonneg (fun u _ => mul_nonneg (ih u) (hP.1 u y))
  exact hall t z

/-- (4/9) Exact-time occupation mass is nonnegative for a genuine mutation
law, including laws with zero-radius mass. -/
theorem firstZeroOccupationMass_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (x : BitString n) (i : Fin n) (t : Nat) :
    0 ≤ firstZeroOccupationMass law w x i t := by
  classical
  change 0 ≤ finiteEventMass (firstZeroStateMass law w x t)
    (fun z : BitString n => z ∈ firstZeroLevel i)
  unfold finiteEventMass
  apply Finset.sum_nonneg
  intro z _
  by_cases hz : z ∈ firstZeroLevel i
  · have hmem : z ∈
        ({y : BitString n | y ∈ firstZeroLevel i} : Set (BitString n)) := hz
    rw [Set.indicator_of_mem hmem]
    exact firstZeroStateMass_nonneg law w x t z
  · have hnot : z ∉
        ({y : BitString n | y ∈ firstZeroLevel i} : Set (BitString n)) := hz
    rw [Set.indicator_of_notMem hnot]

/-- (5/9) Each initial or later entry-flow mass is nonnegative. -/
theorem firstZeroEntryMass_nonneg {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (x : BitString n) (i : Fin n) (t : Nat) :
    0 ≤ firstZeroEntryMass law w x i t := by
  classical
  cases t with
  | zero =>
      by_cases hx : x ∈ firstZeroLevel i <;>
        simp [firstZeroEntryMass, hx]
  | succ t =>
      change 0 ≤ ∑ z : BitString n,
        firstZeroStateMass law w x t z *
          finiteEventMass ((law.transition (linearFitness w)) z)
            (fun y : BitString n => z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i)
      apply Finset.sum_nonneg
      intro z _
      apply mul_nonneg (firstZeroStateMass_nonneg law w x t z)
      unfold finiteEventMass
      apply Finset.sum_nonneg
      intro y _
      by_cases hy : z ∉ firstZeroLevel i ∧ y ∈ firstZeroLevel i
      · have hmem : y ∈
            ({v : BitString n |
              z ∉ firstZeroLevel i ∧ v ∈ firstZeroLevel i} : Set (BitString n)) := hy
        rw [Set.indicator_of_mem hmem]
        exact (law.transition_stochastic (linearFitness w)).1 z y
      · have hnot : y ∉
            ({v : BitString n |
              z ∉ firstZeroLevel i ∧ v ∈ firstZeroLevel i} : Set (BitString n)) := hy
        rw [Set.indicator_of_notMem hnot]

/-- (6/9) Exact horizon budget: cumulative entries consist of residual
occupation at `T` and the original-law exit hazard charged to all earlier
occupations. The terminal term is essential and the identity also handles
`T=0`, `n=0` (no index) and a zero exit hazard. -/
theorem firstZeroCumulativeEntryMass_eq_terminal_add_exit {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (T : Nat) :
    firstZeroCumulativeEntryMass law w x i T =
      firstZeroOccupationMass law w x i T +
        law.maskEventMass (lowestMaskEvent i) *
          (∑ t ∈ Finset.range T, firstZeroOccupationMass law w x i t) := by
  classical
  let a : Nat → Real := firstZeroOccupationMass law w x i
  let e : Nat → Real := firstZeroEntryMass law w x i
  let q : Real := law.maskEventMass (lowestMaskEvent i)
  have hzero : a 0 = e 0 := by
    have hconv := firstZeroOccupationMass_eq_entry_convolution law w hw x i 0
    simpa [a, e] using hconv
  have hstep (t : Nat) : a (t + 1) = e (t + 1) + (1 - q) * a t := by
    exact firstZeroOccupationMass_succ_eq_entry_add_stay law w hw x i t
  have hbudget (t : Nat) :
      (∑ s ∈ Finset.range (t + 1), e s) =
        a t + q * (∑ s ∈ Finset.range t, a s) := by
    induction t with
    | zero =>
        simp [hzero]
    | succ t ih =>
        calc
          (∑ s ∈ Finset.range ((t + 1) + 1), e s) =
              (∑ s ∈ Finset.range (t + 1), e s) + e (t + 1) := by
                rw [Finset.sum_range_succ]
          _ = (a t + q * (∑ s ∈ Finset.range t, a s)) + e (t + 1) := by
                rw [ih]
          _ = a (t + 1) + q * (∑ s ∈ Finset.range (t + 1), a s) := by
                rw [Finset.sum_range_succ, hstep]
                ring
  exact hbudget T

/-- (7/9) A positive singleton mass makes each first-zero exit hazard
positive. Thus finite occupation is bounded by cumulative entry mass divided
by the *exact* level hazard (not the looser `n/p1` residence cap). -/
theorem firstZeroOccupationMass_horizon_le_entry_div_hazard {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (i : Fin n) (T : Nat)
    (hp1 : 0 < law.oneBitMass) :
    (∑ t ∈ Finset.range T, firstZeroOccupationMass law w x i t) ≤
      firstZeroCumulativeEntryMass law w x i T /
        law.maskEventMass (lowestMaskEvent i) := by
  classical
  have hnNat : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hn : (0 : Real) < n := by exact_mod_cast hnNat
  have hq : 0 < law.maskEventMass (lowestMaskEvent i) :=
    lt_of_lt_of_le (div_pos hp1 hn)
      (law.lowestMaskEvent_mass_ge_oneBit_per_coordinate i)
  apply (le_div_iff₀ hq).2
  have hbudget :=
    firstZeroCumulativeEntryMass_eq_terminal_add_exit law w hw x i T
  have hterminal := firstZeroOccupationMass_nonneg law w x i T
  nlinarith

/-- (8/9) Sum the exact horizon balance over disjoint first-zero levels.
There is no division, so the identity holds with zero singleton mass. -/
theorem firstZeroGlobalOccupation_exit_entry_balance {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) :
    (∑ i : Fin n, firstZeroCumulativeEntryMass law w x i T) =
      firstZeroGlobalOccupationMass law w x T +
        ∑ i : Fin n,
          law.maskEventMass (lowestMaskEvent i) *
            (∑ t ∈ Finset.range T,
              firstZeroOccupationMass law w x i t) := by
  classical
  change (∑ i : Fin n, firstZeroCumulativeEntryMass law w x i T) =
      (∑ i : Fin n, firstZeroOccupationMass law w x i T) +
      ∑ i : Fin n,
        law.maskEventMass (lowestMaskEvent i) *
          (∑ t ∈ Finset.range T, firstZeroOccupationMass law w x i t)
  calc
    (∑ i : Fin n, firstZeroCumulativeEntryMass law w x i T) =
        ∑ i : Fin n,
          (firstZeroOccupationMass law w x i T +
            law.maskEventMass (lowestMaskEvent i) *
              (∑ t ∈ Finset.range T, firstZeroOccupationMass law w x i t)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact firstZeroCumulativeEntryMass_eq_terminal_add_exit law w hw x i T
    _ = _ := by rw [Finset.sum_add_distrib]

/-- (9/9) Weighted-entry upper bound for the total finite-horizon time
outside the optimum. This is a truncated-time result, not the unproved
infinite-horizon identity or the sharp n-log-n theorem. -/
theorem firstZeroGlobalOccupation_horizon_le_weighted_entries {n : Nat}
    (law : StaticUnaryUnbiasedMutation n)
    (w : Fin n → Real) (hw : SuperincreasingLinearWeights w)
    (x : BitString n) (T : Nat) (hp1 : 0 < law.oneBitMass) :
    (∑ t ∈ Finset.range T, firstZeroGlobalOccupationMass law w x t) ≤
      ∑ i : Fin n,
        firstZeroCumulativeEntryMass law w x i T /
          law.maskEventMass (lowestMaskEvent i) := by
  classical
  have hswap :
      (∑ t ∈ Finset.range T, firstZeroGlobalOccupationMass law w x t) =
        ∑ i : Fin n, ∑ t ∈ Finset.range T,
          firstZeroOccupationMass law w x i t := by
    change (∑ t ∈ Finset.range T, ∑ i : Fin n,
      firstZeroOccupationMass law w x i t) = _
    rw [Finset.sum_comm]
  rw [hswap]
  exact Finset.sum_le_sum (fun i _ =>
    firstZeroOccupationMass_horizon_le_entry_div_hazard law w hw x i T hp1)

end WeightedVisitsDecidability
end StaticUnaryUnbiasedMutation
end ECRuntime
