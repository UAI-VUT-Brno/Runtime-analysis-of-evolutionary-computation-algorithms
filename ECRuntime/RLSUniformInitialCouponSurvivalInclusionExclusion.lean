import ECRuntime.RLSUniformInitialCouponTail
import ECRuntime.RLSOneBitSupport
import ECRuntime.RLSOneBitExpectationSupport
import ECRuntime.StaticUnaryUnbiasedMomentFamilies
import ECRuntime.LevelExitTail
import Mathlib

open scoped BigOperators
namespace ECRuntime

/-!
Stage 166 -- PROVISIONAL PUBLIC INTEGRATION FOR ROUND 54.
The entire statement and proof compiled independently with Lean 4.32.1 in the
user's successful Round 53 check. Public compilation, transitive axiom audit,
non-vacuity test, and eight-gate promotion verification remain pending. The intended route to a random-stake coupon-
collector limit distribution runs through an exact finite survival formula.
This formula is stronger than the Stage 165 capped union bound and is
not implied by the expectation-only theorems.

Mathematical route to investigate:
  (1) For any fixed j-subset of zero coordinates, the joint event that all
      j remain initially zero and unselected after t one-bit updates has
      probability 2^(-j) * (1-j/n)^t.
  (2) Apply finite inclusion-exclusion over the events that a given
      coordinate remains a zero.
  (3) Transport to finiteLevelSurvival for the elitist one-bit kernel.
  (4) Later use this exact formula to study the centered runtime CDF.
No distributional limit is asserted by this statement.
-/

/-! ## Reusable nonpublic reductions for the exact distributional formula

The supporting lemmas are private implementation details; the approved
headline interface is unchanged. This provisional public module is subject to
the Round 54 promotion checks before certification. -/

/-- Positive weights affect neither the one-bit RLS transition kernel nor
its finite-horizon survival probabilities. All subsequent probability
calculations may therefore be performed for OneMax. -/
private theorem stage166_reduce_to_oneMax
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (t : Nat) :
    (Finset.univ.sum (fun x : BitString n =>
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w))
        ({allOnes n} : Set (BitString n))ᶜ t x)) / (2 : Real) ^ n =
    (Finset.univ.sum (fun x : BitString n =>
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          oneMaxReal)
        ({allOnes n} : Set (BitString n))ᶜ t x)) / (2 : Real) ^ n := by
  rw [candidate_rls_linear_transition_eq_oneMax hn w hw]

/-- A one-bit OneMax update turns a selected zero into a one and rejects
an attempted one-to-zero flip. This is the deterministic process behind
the coupon-collector coupling. -/
private theorem stage166_selected_oneBit
    {n : Nat} (x : BitString n) (i : Fin n) :
    selectedAfterMask oneMaxReal x ({i} : MutationMask n) =
      if x i = false then mutateWithMask x ({i} : MutationMask n) else x := by
  by_cases hxi : x i = false
  · have hacc : Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      exact_mod_cast Nat.le_of_lt (oneMax_single_zero_flip_improves x i hxi)
    rw [if_pos hxi]
    exact elitistSelect_of_accepts oneMaxReal x
      (mutateWithMask x ({i} : MutationMask n)) hacc
  · have htrue : x i = true := by cases h : x i <;> simp_all
    have hdrop : oneCount (mutateWithMask x ({i} : MutationMask n)) <
        oneCount x := by
      have hcount := oneCount_mutate_single_of_true x i htrue
      omega
    have hrej : ¬ Accepts oneMaxReal x
        (mutateWithMask x ({i} : MutationMask n)) := by
      unfold Accepts oneMaxReal
      exact not_le_of_gt (by exact_mod_cast hdrop :
        (oneCount (mutateWithMask x ({i} : MutationMask n)) : Real) <
          (oneCount x : Real))
    rw [if_neg hxi]
    exact elitistSelect_of_rejects oneMaxReal x
      (mutateWithMask x ({i} : MutationMask n)) hrej

/-- Event indicator that all coordinates in a fixed subset still carry
zero bits. For the empty subset the indicator is identically one. -/
private noncomputable def stage166_jointZeroIndicator
    {n : Nat} (S : Finset (Fin n)) (x : BitString n) : Real :=
  if ∀ j ∈ S, x j = false then 1 else 0

/-- Fixed-set zero events are simply containment events for the set of
initial zero coordinates. This is the bridge from Markov eigenfunctions
to uniform-start counting over the powerset of `Fin n`.
This helper remains nonpublic until Stage 166 is completely certified. -/
private theorem stage166_jointZeroIndicator_eq_if_subset
    {n : Nat} (S : Finset (Fin n)) (x : BitString n) :
    stage166_jointZeroIndicator S x =
      if S ⊆ zeroPositions x then (1 : Real) else 0 := by
  classical
  have hiff : (∀ j ∈ S, x j = false) ↔ S ⊆ zeroPositions x := by
    constructor
    · intro h j hj
      exact (mem_zeroPositions x j).2 (h j hj)
    · intro h j hj
      exact (mem_zeroPositions x j).1 (h hj)
  simp only [stage166_jointZeroIndicator, hiff]

/-! ### Uniform-start counting for a fixed joint-zero event

This finite combinatorial calculation is independent of the transition
kernel.  Its later use in inclusion--exclusion supplies the factor
`2^(-|S|)` for each fixed subset of zero coordinates.  The proof below
is a new nonpublic Lean proof attempt, pending the Round 50 compiler run. -/

/-- Exactly `2^(n-|S|)` initial strings have a zero at every coordinate
of `S`.  We count the free zero coordinates in the complement of `S`
through an explicit bijection with its powerset. -/
private theorem stage166_jointZeroInitials_card
    {n : Nat} (S : Finset (Fin n)) :
    (Finset.univ.filter (fun x : BitString n =>
      S ⊆ zeroPositions x)).card = 2 ^ (n - S.card) := by
  classical
  let rest : Finset (Fin n) := Finset.univ \ S
  let decode : Finset (Fin n) → BitString n :=
    fun T i => if i ∈ T then false else true
  have hdecode (T : Finset (Fin n)) :
      zeroPositions (decode T) = T := by
    ext i
    by_cases hi : i ∈ T <;> simp [decode, zeroPositions, hi]
  have hbij :
      (Finset.univ.filter (fun x : BitString n =>
        S ⊆ zeroPositions x)).card =
      (Finset.powerset rest).card := by
    refine Finset.card_bij (fun x _ => zeroPositions x \ S) ?_ ?_ ?_
    · intro x hx
      apply Finset.mem_powerset.mpr
      intro i hi
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩
    · intro x hx y hy heq
      have hxS : S ⊆ zeroPositions x := (Finset.mem_filter.mp hx).2
      have hyS : S ⊆ zeroPositions y := (Finset.mem_filter.mp hy).2
      have hzero : zeroPositions x = zeroPositions y := by
        ext i
        by_cases hi : i ∈ S
        · simp [hxS hi, hyS hi]
        · have hdiff := congrArg (fun T : Finset (Fin n) => i ∈ T) heq
          simpa [Finset.mem_sdiff, hi] using hdiff
      funext i
      have hiff : x i = false ↔ y i = false := by
        have hi := congrArg (fun T : Finset (Fin n) => i ∈ T) hzero
        simpa [mem_zeroPositions] using hi
      cases hxi : x i <;> cases hyi : y i <;> simp_all
    · intro T hT
      have hTsub : T ⊆ rest := Finset.mem_powerset.mp hT
      have hnotS (i : Fin n) (hi : i ∈ T) : i ∉ S :=
        (Finset.mem_sdiff.mp (hTsub hi)).2
      refine ⟨decode (S ∪ T), ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ _
        · rw [hdecode]
          exact Finset.subset_union_left
      · rw [hdecode]
        ext i
        constructor
        · intro hi
          have hi_union : i ∈ S ∪ T := (Finset.mem_sdiff.mp hi).1
          have hi_not : i ∉ S := (Finset.mem_sdiff.mp hi).2
          exact (Finset.mem_union.mp hi_union).resolve_left hi_not
        · intro hi
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_union_right S hi, hnotS i hi⟩
  have hrest : rest.card = n - S.card := by
    have hdecomp : rest.card + S.card = n := by
      simpa [rest] using
        (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S))
    omega
  calc
    _ = (Finset.powerset rest).card := hbij
    _ = 2 ^ rest.card := by simp
    _ = 2 ^ (n - S.card) := by rw [hrest]

/-- The exact uniform-start mass of a prescribed joint-zero event.
This is a candidate-only bridge from Boolean-state enumeration to the
Markov-eigenfunction argument; it needs compiler verification. -/
private theorem stage166_jointZeroIndicator_uniform_sum
    {n : Nat} (S : Finset (Fin n)) :
    (∑ x : BitString n, stage166_jointZeroIndicator S x) =
      (2 : Real) ^ (n - S.card) := by
  classical
  calc
    (∑ x : BitString n, stage166_jointZeroIndicator S x) =
      ∑ x ∈ Finset.univ.filter (fun x : BitString n =>
        S ⊆ zeroPositions x), (1 : Real) := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x _
          exact stage166_jointZeroIndicator_eq_if_subset S x
    _ = ((Finset.univ.filter (fun x : BitString n =>
      S ⊆ zeroPositions x)).card : Real) := by simp
    _ = (2 : Real) ^ (n - S.card) := by
      exact_mod_cast stage166_jointZeroInitials_card S

/-! ### Finite Boolean inclusion--exclusion, prior to Markov transport

The identity below is a purely finite algebraic sieve, independent of
probabilities and of the RLS transition.  It is a new candidate-only proof
attempt.  Establishing it isolates the *pointwise* inclusion--exclusion
step from the Markov and uniform-initialization calculations. -/

/-- Alternating signed mass of the powerset.  For nonempty `Z` the
binomial expansion of `(1-1)^|Z|` vanishes. -/
private theorem stage166_alternating_powerset
    {n : Nat} (Z : Finset (Fin n)) :
    (∑ S ∈ Z.powerset, (-1 : Real) ^ S.card) =
      if Z = ∅ then 1 else 0 := by
  classical
  have hfixed (k : Nat) :
      (∑ S ∈ Z.powersetCard k, (-1 : Real) ^ S.card) =
        (Nat.choose Z.card k : Real) * (-1 : Real) ^ k := by
    calc
      _ = ∑ _S ∈ Z.powersetCard k, (-1 : Real) ^ k := by
        apply Finset.sum_congr rfl
        intro S hS
        rw [(Finset.mem_powersetCard.mp hS).2]
      _ = (Nat.choose Z.card k : Real) * (-1 : Real) ^ k := by
        simp [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
  have hgroup :
      (∑ S ∈ Z.powerset, (-1 : Real) ^ S.card) =
        ∑ k ∈ Finset.range (Z.card + 1),
          (Nat.choose Z.card k : Real) * (-1 : Real) ^ k := by
    calc
      _ = ∑ k ∈ Finset.range (Z.card + 1),
            ∑ S ∈ Z.powersetCard k, (-1 : Real) ^ S.card :=
              Finset.sum_powerset Z (fun S => (-1 : Real) ^ S.card)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        exact hfixed k
  have hbinomial :
      (∑ k ∈ Finset.range (Z.card + 1),
        (Nat.choose Z.card k : Real) * (-1 : Real) ^ k) =
          ((-1 : Real) + 1) ^ Z.card := by
    calc
      _ = ∑ k ∈ Finset.range (Z.card + 1),
            (-1 : Real) ^ k * (Nat.choose Z.card k : Real) := by
              apply Finset.sum_congr rfl
              intro k _
              ring
      _ = _ := by
        simpa using (add_pow (-1 : Real) (1 : Real) Z.card).symm
  rw [hgroup, hbinomial]
  by_cases hZ : Z = ∅
  · simp [hZ]
  · simp [hZ]

/-- All nonempty subsets of the coordinate set. -/
private def stage166_nonemptyCoordinateSubsets (n : Nat) :
    Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powerset.erase ∅

/-- A bitstring is not the optimum iff at least one of its joint-zero
events occurs.  The RHS is the alternating nonempty-subset sieve.
This does not assume independence of the coordinate events. -/
private theorem stage166_nonoptimum_inclusionExclusion_indicator
    {n : Nat} (x : BitString n) :
    (if x = allOnes n then (0 : Real) else 1) =
      ∑ S ∈ stage166_nonemptyCoordinateSubsets n,
        (-1 : Real) ^ (S.card + 1) * stage166_jointZeroIndicator S x := by
  classical
  let Z : Finset (Fin n) := zeroPositions x
  let allSubsets : Finset (Finset (Fin n)) :=
    (Finset.univ : Finset (Fin n)).powerset
  let f : Finset (Fin n) → Real :=
    fun S => (-1 : Real) ^ S.card * stage166_jointZeroIndicator S x
  have htotal : (∑ S ∈ allSubsets, f S) =
      if Z = ∅ then (1 : Real) else 0 := by
    have hfiltered :
        (∑ S ∈ allSubsets, f S) =
          ∑ S ∈ Z.powerset, (-1 : Real) ^ S.card := by
      calc
        _ = ∑ S ∈ allSubsets,
              if S ⊆ Z then (-1 : Real) ^ S.card else 0 := by
          apply Finset.sum_congr rfl
          intro S _
          change (-1 : Real) ^ S.card * stage166_jointZeroIndicator S x = _
          rw [stage166_jointZeroIndicator_eq_if_subset]
          by_cases hS : S ⊆ Z <;> simp [Z, hS]
        _ = ∑ S ∈ allSubsets.filter (fun S => S ⊆ Z),
              (-1 : Real) ^ S.card := by
          rw [Finset.sum_filter]
        _ = ∑ S ∈ Z.powerset, (-1 : Real) ^ S.card := by
          congr 1
          ext S
          simp [allSubsets, Finset.mem_powerset]
    rw [hfiltered, stage166_alternating_powerset]
  have hzero : f ∅ = 1 := by
    simp [f, stage166_jointZeroIndicator]
  have hempty : (∅ : Finset (Fin n)) ∈ allSubsets := by
    simp [allSubsets]
  have hsplit := Finset.sum_erase_add allSubsets f hempty
  rw [hzero, htotal] at hsplit
  have hsign :
      (∑ S ∈ allSubsets.erase ∅,
        (-1 : Real) ^ (S.card + 1) * stage166_jointZeroIndicator S x) =
          - (∑ S ∈ allSubsets.erase ∅, f S) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S _
    simp only [f, pow_succ]
    ring
  have hopt : x = allOnes n ↔ Z = ∅ := by
    constructor
    · intro hx
      change zeroPositions x = ∅
      rw [hx]
      simp [zeroPositions, allOnes]
    · intro hZ
      have hc : zeroCount x = 0 := by
        have hcard : (zeroPositions x).card = 0 := by
          change Z.card = 0
          rw [hZ]
          rfl
        simpa [zeroPositions_card] using hcard
      exact (zeroCount_eq_zero_iff_allOnes x).mp hc
  change (if x = allOnes n then (0 : Real) else 1) =
      ∑ S ∈ allSubsets.erase ∅,
        (-1 : Real) ^ (S.card + 1) * stage166_jointZeroIndicator S x
  rw [hsign]
  by_cases hx : x = allOnes n
  · have hz : Z = ∅ := hopt.mp hx
    simp only [if_pos hx, if_pos hz] at hsplit ⊢
    linarith
  · have hz : Z ≠ ∅ := fun h => hx (hopt.mpr h)
    simp only [if_neg hx, if_neg hz] at hsplit ⊢
    linarith

/-- Under a singleton update, the joint-zero event disappears exactly
when a coordinate of its defining set is selected. -/
private theorem stage166_jointZeroIndicator_singleton
    {n : Nat} (S : Finset (Fin n)) (x : BitString n) (i : Fin n) :
    stage166_jointZeroIndicator S
      (selectedAfterMask oneMaxReal x ({i} : MutationMask n)) =
        if i ∈ S then 0 else stage166_jointZeroIndicator S x := by
  classical
  rw [stage166_selected_oneBit]
  by_cases his : i ∈ S
  · rw [if_pos his]
    by_cases hxi : x i = false
    · rw [if_pos hxi]
      have hbad : ¬ (∀ j ∈ S, mutateWithMask x ({i} : MutationMask n) j = false) := by
        intro hall
        have hi := hall i his
        simp [hxi] at hi
      simp [stage166_jointZeroIndicator, hbad]
    · rw [if_neg hxi]
      have hbad : ¬ (∀ j ∈ S, x j = false) := by
        intro hall
        exact hxi (hall i his)
      simp [stage166_jointZeroIndicator, hbad]
  · rw [if_neg his]
    by_cases hxi : x i = false
    · rw [if_pos hxi]
      have hother (j : Fin n) (hj : j ∈ S) :
          mutateWithMask x ({i} : MutationMask n) j = x j := by
        apply mutateWithMask_single_other
        intro hji
        exact his (hji ▸ hj)
      have hiff :
          (∀ j ∈ S, mutateWithMask x ({i} : MutationMask n) j = false) ↔
            (∀ j ∈ S, x j = false) := by
        constructor
        · intro hall j hj
          rw [← hother j hj]
          exact hall j hj
        · intro hall j hj
          rw [hother j hj]
          exact hall j hj
      simp only [stage166_jointZeroIndicator, hiff]
    · rw [if_neg hxi]

/-- The joint-zero indicator is a one-step eigenfunction of the
one-bit RLS Markov operator, with eigenvalue `1 - |S|/n`. This is the
probabilistic factorization at the heart of Stage 166; importantly, it
uses *one-step conditional expectations*, not an unjustified assertion
of independence between successive optimization steps. -/
private theorem stage166_jointZeroIndicator_oneStep
    {n : Nat} (hn : 0 < n) (S : Finset (Fin n)) (x : BitString n) :
    expectedValueAfter
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      (stage166_jointZeroIndicator S) x =
        (1 - (S.card : Real) / (n : Real)) * stage166_jointZeroIndicator S x := by
  classical
  have hn0 : (n : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hcount :
      (∑ i : Fin n, if i ∈ S then (1 : Real) else 0) = (S.card : Real) := by
    calc
      _ = ∑ i ∈ S, (1 : Real) := Finset.sum_ite_mem_eq _ _
      _ = (S.card : Real) := by simp
  have hsum :
      (∑ i : Fin n,
          if i ∈ S then (0 : Real) else stage166_jointZeroIndicator S x) =
        ((n : Real) - (S.card : Real)) * stage166_jointZeroIndicator S x := by
    have hsub :
        (∑ i : Fin n,
          if i ∈ S then stage166_jointZeroIndicator S x else (0 : Real)) =
            (S.card : Real) * stage166_jointZeroIndicator S x := by
      calc
        _ = (∑ i : Fin n, if i ∈ S then (1 : Real) else 0) *
              stage166_jointZeroIndicator S x := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> ring
        _ = _ := by rw [hcount]
    calc
      _ = (∑ _i : Fin n, stage166_jointZeroIndicator S x) -
          (∑ i : Fin n,
            if i ∈ S then stage166_jointZeroIndicator S x else (0 : Real)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          split_ifs <;> ring
      _ = _ := by
        rw [hsub]
        -- `simp` reduces the constant sum to `n * J_S(x)`, but the
        -- subtraction/distributivity equality is a ring identity.
        simp; ring
  calc
    expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
        (stage166_jointZeroIndicator S) x =
      (n : Real)⁻¹ *
        (∑ i : Fin n,
          stage166_jointZeroIndicator S
            (selectedAfterMask oneMaxReal x ({i} : MutationMask n))) :=
        candidate_rls_expectedValueAfter_eq_singleton_average hn oneMaxReal
          (stage166_jointZeroIndicator S) x
    _ = (n : Real)⁻¹ *
        (∑ i : Fin n,
          if i ∈ S then (0 : Real) else stage166_jointZeroIndicator S x) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          rw [stage166_jointZeroIndicator_singleton]
    _ = (n : Real)⁻¹ *
        (((n : Real) - (S.card : Real)) * stage166_jointZeroIndicator S x) := by
          rw [hsum]
    _ = (1 - (S.card : Real) / (n : Real)) *
          stage166_jointZeroIndicator S x := by
          field_simp [hn0]

/-- A finite-horizon Markov recursion for the joint-zero event. It is
separate from `finiteLevelSurvival`, whose defining level is the union of
all nonempty joint-zero events. -/
private noncomputable def stage166_jointZeroIteration
    {n : Nat} (hn : 0 < n) (S : Finset (Fin n)) :
    Nat → BitString n → Real
  | 0, x => stage166_jointZeroIndicator S x
  | t + 1, x =>
      expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
        (stage166_jointZeroIteration hn S t) x

/-- The `t`-step joint-zero event factorizes exactly. Later inclusion-
exclusion must still combine these moments into the *union* event. -/
private theorem stage166_jointZeroIteration_formula
    {n : Nat} (hn : 0 < n) (S : Finset (Fin n)) (t : Nat) :
    ∀ x : BitString n,
      stage166_jointZeroIteration hn S t x =
        (1 - (S.card : Real) / (n : Real)) ^ t *
          stage166_jointZeroIndicator S x := by
  induction t with
  | zero =>
      intro x
      simp [stage166_jointZeroIteration]
  | succ t ih =>
      intro x
      let q : Real := 1 - (S.card : Real) / (n : Real)
      change expectedValueAfter
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
          (stage166_jointZeroIteration hn S t) x = _
      have hfun : stage166_jointZeroIteration hn S t =
          (fun y => q ^ t * stage166_jointZeroIndicator S y) := funext ih
      rw [hfun]
      have hconst :
          expectedValueAfter
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
            (fun y => q ^ t * stage166_jointZeroIndicator S y) x =
          q ^ t * expectedValueAfter
            ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
            (stage166_jointZeroIndicator S) x := by
        unfold expectedValueAfter
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [hconst, stage166_jointZeroIndicator_oneStep hn S x]
      change q ^ t * (q * stage166_jointZeroIndicator S x) =
        q ^ (t + 1) * stage166_jointZeroIndicator S x
      rw [pow_succ]
      ring

/-! ### Normalize fixed-subset moments and transport Markov recursions

These are independent pieces of the final formula. The first combines
the Round 50 compiler-checked powerset count with the fixed-set
Markov eigenfunction. The second is a generic bridge to the repository's
`finiteLevelSurvival` definition, avoiding any unproved independence
assumption about successive states. -/

/-- Average the time-`t` joint-zero observable over uniform initial
bitstrings. Every chosen coordinate contributes its initial `1/2` and
its common Markov survival factor. -/
private theorem stage166_jointZeroIteration_uniform_average
    {n : Nat} (hn : 0 < n) (S : Finset (Fin n)) (t : Nat) :
    (∑ x : BitString n, stage166_jointZeroIteration hn S t x) /
        (2 : Real) ^ n =
      (1 - (S.card : Real) / (n : Real)) ^ t /
        (2 : Real) ^ S.card := by
  classical
  have hcard : S.card ≤ n := by
    simpa using (Finset.card_le_card (Finset.subset_univ S))
  have hpow : (2 : Real) ^ n =
      (2 : Real) ^ (n - S.card) * (2 : Real) ^ S.card := by
    rw [← pow_add, Nat.sub_add_cancel hcard]
  have hden : (2 : Real) ^ (n - S.card) ≠ 0 := by positivity
  have hdenS : (2 : Real) ^ S.card ≠ 0 := by positivity
  have hsum :
      (∑ x : BitString n, stage166_jointZeroIteration hn S t x) =
        (1 - (S.card : Real) / (n : Real)) ^ t *
          (2 : Real) ^ (n - S.card) := by
    calc
      _ = ∑ x : BitString n,
            (1 - (S.card : Real) / (n : Real)) ^ t *
              stage166_jointZeroIndicator S x := by
          apply Finset.sum_congr rfl
          intro x _
          exact stage166_jointZeroIteration_formula hn S t x
      _ = (1 - (S.card : Real) / (n : Real)) ^ t *
            (∑ x : BitString n, stage166_jointZeroIndicator S x) := by
          rw [Finset.mul_sum]
      _ = _ := by rw [stage166_jointZeroIndicator_uniform_sum]
  rw [hsum, hpow]
  field_simp [hden, hdenS]

/-- Every finite-state Markov recursion with the right horizon-zero
indicator and which vanishes outside the level coincides with the
certified `finiteLevelSurvival` recursion. This is deliberately generic:
no absorbing-chain hypothesis is smuggled into the statement. -/
private theorem stage166_survival_of_markov_recursion
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    [DecidablePred (fun x => x ∈ level)]
    (F : Nat → α → Real)
    (hzero : ∀ x, F 0 x = if x ∈ level then 1 else 0)
    (hstep : ∀ t x, F (t + 1) x = expectedValueAfter P (F t) x)
    (houtside : ∀ t x, x ∉ level → F t x = 0)
    (t : Nat) (x : α) :
    finiteLevelSurvival P level t x = F t x := by
  induction t generalizing x with
  | zero =>
      exact (hzero x).symm
  | succ t ih =>
      by_cases hx : x ∈ level
      · rw [finiteLevelSurvival_succ_of_mem P level t x hx]
        simp_rw [ih]
        exact (hstep t x).symm
      · rw [finiteLevelSurvival_succ_of_not_mem P level t x hx]
        exact (houtside (t + 1) x hx).symm

/-! ### Alternating-sum Markov transport (candidate proof attempts)

The signed sum of the joint-zero recursions is the exact survival
observable if and only if its initial value is the nonoptimum indicator.
The finite sieve above establishes this initial-value equality. -/

/-- Expected value commutes with finite sums of observables. -/
private theorem stage166_expectedValueAfter_sum
    {α β : Type*} [Fintype α]
    (P : TransitionMatrix α) (s : Finset β)
    (F : β → α → Real) (x : α) :
    expectedValueAfter P (fun y => ∑ j ∈ s, F j y) x =
      ∑ j ∈ s, expectedValueAfter P (F j) x := by
  classical
  unfold expectedValueAfter
  calc
    (∑ y : α, P x y * (∑ j ∈ s, F j y)) =
        ∑ y : α, ∑ j ∈ s, P x y * F j y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.mul_sum]
    _ = ∑ j ∈ s, ∑ y : α, P x y * F j y := by
          rw [Finset.sum_comm]

/-- The signed sum of all nonempty-subset joint-zero observables. -/
private noncomputable def stage166_signedMoments
    {n : Nat} (hn : 0 < n) (t : Nat) (x : BitString n) : Real :=
  ∑ S ∈ stage166_nonemptyCoordinateSubsets n,
    (-1 : Real) ^ (S.card + 1) * stage166_jointZeroIteration hn S t x

/-- At time zero, the signed-moment representation is exactly the
indicator of a nonoptimal bitstring. -/
private theorem stage166_signedMoments_zero
    {n : Nat} (hn : 0 < n) (x : BitString n) :
    stage166_signedMoments hn 0 x =
      if x = allOnes n then (0 : Real) else 1 := by
  change (∑ S ∈ stage166_nonemptyCoordinateSubsets n,
    (-1 : Real) ^ (S.card + 1) * stage166_jointZeroIndicator S x) = _
  exact (stage166_nonoptimum_inclusionExclusion_indicator x).symm

/-- Every individual nonempty-subset moment is zero at the optimal
bitstring, independently of the time horizon. -/
private theorem stage166_signedMoments_allOnes
    {n : Nat} (hn : 0 < n) (t : Nat) :
    stage166_signedMoments hn t (allOnes n) = 0 := by
  unfold stage166_signedMoments
  apply Finset.sum_eq_zero
  intro S hS
  have hne : S ≠ ∅ := by
    have hh : S ∈ (Finset.univ : Finset (Fin n)).powerset.erase ∅ := by
      simpa [stage166_nonemptyCoordinateSubsets] using hS
    exact (Finset.mem_erase.mp hh).1
  rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨i, hi⟩
  have hbad : stage166_jointZeroIndicator S (allOnes n) = 0 := by
    have hnz : ¬ (∀ j ∈ S, (allOnes n) j = false) := by
      intro h
      have hval := h i hi
      simp [allOnes] at hval
    simp [stage166_jointZeroIndicator, hnz]
  rw [stage166_jointZeroIteration_formula hn S t (allOnes n), hbad]
  ring

/-- The signed-moment observable evolves by exactly one Markov step. -/
private theorem stage166_signedMoments_step
    {n : Nat} (hn : 0 < n) (t : Nat) (x : BitString n) :
    stage166_signedMoments hn (t + 1) x =
      expectedValueAfter
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
        (stage166_signedMoments hn t) x := by
  let P := (StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal
  change (∑ S ∈ stage166_nonemptyCoordinateSubsets n,
      (-1 : Real) ^ (S.card + 1) *
        expectedValueAfter P (stage166_jointZeroIteration hn S t) x) =
      expectedValueAfter P
        (fun y => ∑ S ∈ stage166_nonemptyCoordinateSubsets n,
          (-1 : Real) ^ (S.card + 1) *
            stage166_jointZeroIteration hn S t y) x
  rw [stage166_expectedValueAfter_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [expectedValueAfter_const_mul]

/-- The alternating joint-zero sum equals the public survival recursion.
All probabilistic dependence is handled through the Markov operator;
only the finite subset sieve enters as a combinatorial identity. -/
private theorem stage166_survival_eq_signedMoments
    {n : Nat} (hn : 0 < n) (t : Nat) (x : BitString n) :
    finiteLevelSurvival
      ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
      ({allOnes n} : Set (BitString n))ᶜ t x =
        stage166_signedMoments hn t x := by
  classical
  refine stage166_survival_of_markov_recursion
    ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
    ({allOnes n} : Set (BitString n))ᶜ
    (stage166_signedMoments hn) ?_ ?_ ?_ t x
  · intro x
    rw [stage166_signedMoments_zero]
    by_cases hx : x = allOnes n <;> simp [hx]
  · intro k y
    exact stage166_signedMoments_step hn k y
  · intro k y hy
    have heq : y = allOnes n := by
      simpa using hy
    subst y
    exact stage166_signedMoments_allOnes hn k

/-! ### Final finite cardinality grouping and survival formula

The hard stochastic calculations are contained in the preceding helpers.
This last finite grouping uses the number `Nat.choose n j` of subsets of
`Fin n` with cardinality `j`, and drops the empty subset on both sides.
The assembled proof is nonpublic until the pinned Lean compiler verifies it.
-/

/-- Group a sum over all *nonempty* subsets of `Fin n` by cardinality.
The zero-cardinality term is removed on both sides of `Finset.sum_powerset`.
This finite lemma does not assume anything about the runtime distribution. -/
private theorem stage166_nonemptySubsets_sum_by_card
    {n : Nat} (f : Nat → Real) :
    (∑ S ∈ stage166_nonemptyCoordinateSubsets n, f S.card) =
      ∑ j ∈ Finset.Icc (1 : Nat) n, (Nat.choose n j : Real) * f j := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have hgroup :
      (∑ S ∈ U.powerset, f S.card) =
        ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : Real) * f j := by
    calc
      _ = ∑ j ∈ Finset.range (n + 1),
            ∑ S ∈ U.powersetCard j, f S.card := by
              simpa [U] using
                (Finset.sum_powerset U (fun S => f S.card))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        calc
          _ = ∑ S ∈ U.powersetCard j, f j := by
                apply Finset.sum_congr rfl
                intro S hS
                rw [(Finset.mem_powersetCard.mp hS).2]
          _ = (Nat.choose n j : Real) * f j := by
                simp [U, Finset.card_powersetCard, nsmul_eq_mul]
  have hempty : (∅ : Finset (Fin n)) ∈ U.powerset := by
    simp [U]
  have hzero : (0 : Nat) ∈ Finset.range (n + 1) := by
    simp
  have hsplitS :
      (∑ S ∈ U.powerset.erase ∅, f S.card) + f 0 =
        ∑ S ∈ U.powerset, f S.card := by
    have h := Finset.sum_erase_add U.powerset (fun S => f S.card) hempty
    simp only [Finset.card_empty] at h
    exact h
  have hsplitK :
      (∑ j ∈ (Finset.range (n + 1)).erase 0,
          (Nat.choose n j : Real) * f j) + f 0 =
        ∑ j ∈ Finset.range (n + 1),
          (Nat.choose n j : Real) * f j := by
    have h := Finset.sum_erase_add (Finset.range (n + 1))
      (fun j => (Nat.choose n j : Real) * f j) hzero
    have hchoose : (Nat.choose n 0 : Real) = 1 := by simp
    rw [hchoose, one_mul] at h
    exact h
  have heq :
      (∑ S ∈ U.powerset.erase ∅, f S.card) =
        ∑ j ∈ (Finset.range (n + 1)).erase 0,
          (Nat.choose n j : Real) * f j := by
    rw [hgroup] at hsplitS
    linarith [hsplitS, hsplitK]
  have hIcc : (Finset.range (n + 1)).erase 0 =
      Finset.Icc (1 : Nat) n := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  change (∑ S ∈ U.powerset.erase ∅, f S.card) =
    ∑ j ∈ Finset.Icc (1 : Nat) n, (Nat.choose n j : Real) * f j
  rw [← hIcc]
  exact heq

/-- The averaged signed Markov observable is the alternating sum of its
individual fixed-subset moments. All sums are finite, so no exchange of
limits or independence argument is required. -/
private theorem stage166_averagedSignedMoments
    {n : Nat} (hn : 0 < n) (t : Nat) :
    (∑ x : BitString n, stage166_signedMoments hn t x) / (2 : Real) ^ n =
      ∑ S ∈ stage166_nonemptyCoordinateSubsets n,
        (-1 : Real) ^ (S.card + 1) *
          ((1 - (S.card : Real) / (n : Real)) ^ t / (2 : Real) ^ S.card) := by
  classical
  unfold stage166_signedMoments
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.mul_sum]
  -- The coefficient multiplies the *whole* state sum. First move it
  -- outside the uniform-start normalization; only then does the
  -- fixed-subset moment lemma match the expression syntactically.
  calc
    ((-1 : Real) ^ (S.card + 1) *
        ∑ i : BitString n, stage166_jointZeroIteration hn S t i) /
          (2 : Real) ^ n =
        (-1 : Real) ^ (S.card + 1) *
          ((∑ i : BitString n, stage166_jointZeroIteration hn S t i) /
            (2 : Real) ^ n) := by ring
    _ = _ := by rw [stage166_jointZeroIteration_uniform_average hn S t]

/-- Exact finite-time survival probability, averaged over all initial
bitstrings, for one-bit RLS on any strictly positive linear function.
The alternating subset sum is the finite inclusion-exclusion identity.
Statement approved in the Round 45 follow-up. The proof passed independent
Lean compilation in Round 53; this public integration is not yet promoted
until its complete verification gates pass. -/
theorem proposed_rlsLinear_uniformInitial_couponSurvival_inclusionExclusion
    {n : Nat} (hn : 0 < n) (w : Fin n → Real)
    (hw : PositiveLinearWeights w) (t : Nat) :
    (Finset.univ.sum (fun x : BitString n =>
      finiteLevelSurvival
        ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition
          (linearFitness w))
        ({allOnes n} : Set (BitString n))ᶜ t x)) / (2 : Real) ^ n =
      (Finset.Icc (1 : Nat) n).sum (fun j =>
        (-1 : Real) ^ (j + 1) * (Nat.choose n j : Real) /
          (2 : Real) ^ j *
          (1 - (j : Real) / (n : Real)) ^ t) := by
  classical
  rw [stage166_reduce_to_oneMax hn w hw t]
  let f : Nat → Real := fun j =>
    (-1 : Real) ^ (j + 1) *
      ((1 - (j : Real) / (n : Real)) ^ t / (2 : Real) ^ j)
  calc
    (∑ x : BitString n,
        finiteLevelSurvival
          ((StaticUnaryUnbiasedMutation.uniformOneBitLaw hn).transition oneMaxReal)
          ({allOnes n} : Set (BitString n))ᶜ t x) / (2 : Real) ^ n =
        (∑ x : BitString n, stage166_signedMoments hn t x) /
          (2 : Real) ^ n := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            exact stage166_survival_eq_signedMoments hn t x
    _ = ∑ S ∈ stage166_nonemptyCoordinateSubsets n, f S.card := by
          simpa only [f] using stage166_averagedSignedMoments hn t
    _ = ∑ j ∈ Finset.Icc (1 : Nat) n,
          (Nat.choose n j : Real) * f j :=
            stage166_nonemptySubsets_sum_by_card f
    _ = ∑ j ∈ Finset.Icc (1 : Nat) n,
          (-1 : Real) ^ (j + 1) * (Nat.choose n j : Real) /
            (2 : Real) ^ j * (1 - (j : Real) / (n : Real)) ^ t := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp [f]
          ring

end ECRuntime
