import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.UnrestrictedRuntime
import ECRuntime.FitnessLevel
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime
namespace StaticUnaryUnbiasedMutation

/-!
Candidate 117 (A9): objective-independent runtime bound from positive
probability of every nonempty mutation mask. The explicit a>0 lower bound
avoids a fragile global finite-minimum interface until it is proved.
Source context: Doerr (2019; 2021), full-support runtime bounds.
-/

/-- Positive mass of EVERY positive radius yields a uniform positive lower
bound on the probability of EVERY nonempty mask. -/
theorem fullSupport_exists_positiveMaskFloor
    {n : Nat} (law : StaticUnaryUnbiasedMutation n) (hn : 0 < n)
    (hradius : ∀ k : Nat, 1 ≤ k → k ≤ n → 0 < law.radiusMass k) :
    ∃ a : Real, 0 < a ∧
      (∀ mask : MutationMask n, mask ≠ (∅ : MutationMask n) →
        a ≤ law.weight mask) := by
  classical
  -- The supplied positive-dimension hypothesis is part of the approved
  -- interface.  Positivity of a particular nonempty mask already implies
  -- positive dimension, but referring to `hn` avoids an unused-binder warning.
  have _hpositiveDimension : 0 < n := hn
  have hpositive (mask : MutationMask n)
      (hm : mask ≠ (∅ : MutationMask n)) : 0 < law.weight mask := by
    have hk : 1 ≤ mask.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hm)
    have hkn : mask.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ mask)
    have hrad := hradius mask.card hk hkn
    have hnonneg := law.weight_nonneg mask
    by_contra hnot
    have hzero : law.weight mask = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    have hradzero : law.radiusMass mask.card = 0 := by
      unfold radiusMass
      apply Finset.sum_eq_zero
      intro other hother
      have hc : other.card = mask.card :=
        (Finset.mem_powersetCard.mp hother).2
      rw [law.card_invariant hc, hzero]
    exact (ne_of_gt hrad) hradzero
  -- Finite minimum lemma, proved here to avoid introducing a new global
  -- probability abstraction or a noncomputable infinite infimum.
  have hfloor : ∀ s : Finset (MutationMask n),
      (∀ mask ∈ s, 0 < law.weight mask) →
      ∃ a : Real, 0 < a ∧ ∀ mask ∈ s, a ≤ law.weight mask := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨1, by norm_num, by simp⟩
    | @insert mask s hnot ih =>
        intro hs
        have hpos : 0 < law.weight mask :=
          hs mask (Finset.mem_insert_self mask s)
        obtain ⟨a, ha, hmin⟩ := ih (by
          intro other ho
          exact hs other (Finset.mem_insert_of_mem ho))
        refine ⟨min (law.weight mask) a, lt_min hpos ha, ?_⟩
        intro other ho
        rcases Finset.mem_insert.mp ho with heq | ho
        · subst other
          exact min_le_left _ _
        · exact (min_le_right _ _).trans (hmin other ho)
  let s : Finset (MutationMask n) := Finset.univ.erase ∅
  have hs : ∀ mask ∈ s, 0 < law.weight mask := by
    intro mask hm
    exact hpositive mask (Finset.mem_erase.mp hm).1
  obtain ⟨a, ha, hmin⟩ := hfloor s hs
  refine ⟨a, ha, ?_⟩
  intro mask hm
  exact hmin mask (Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩)

/-- Any elitist optimization process with a designated global optimum and
uniform minimum probability a of every nonempty mask has E[T] ≤ 1/a.
This also covers initial states that are already optimal (T=0). -/
theorem fullSupport_runtimeSup_le_invMaskFloor
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (fitness : BitString n → Real) (opt : BitString n)
    (hopt : ∀ y : BitString n, fitness y ≤ fitness opt)
    (a : Real) (ha : 0 < a)
    (hfloor : ∀ mask : MutationMask n,
      mask ≠ (∅ : MutationMask n) → a ≤ law.weight mask)
    (x : BitString n) :
    runtimeSup (law.transition fitness)
      ({opt} : Set (BitString n)) x ≤ ENNReal.ofReal (1 / a) := by
  classical
  -- A constant certificate off the target works even if the (elitist)
  -- transition is not absorbing at a tied global maximizer.
  let B : BitString n → Real := fun y => if y = opt then 0 else 1 / a
  have hBpos : 0 < (1 : Real) / a := div_pos (by norm_num) ha
  have hBnonneg : ∀ y : BitString n, 0 ≤ B y := by
    intro y
    by_cases hy : y = opt
    · simp [B, hy]
    · simpa [B, hy] using hBpos.le
  have hsuper : IsRuntimeSuperSolution (law.transition fitness)
      ({opt} : Set (BitString n)) B := by
    constructor
    · intro y hy
      have hyopt : y = opt := Set.mem_singleton_iff.mp hy
      simp [B, hyopt]
    · intro y hy
      have hyne : y ≠ opt := by simpa using hy
      -- The unique mask that flips exactly the positions where y and opt
      -- differ is nonempty and always produces opt.
      let diffMask : MutationMask n :=
        Finset.univ.filter (fun i => y i ≠ opt i)
      have hflip : mutateWithMask y diffMask = opt := by
        funext i
        by_cases heq : y i = opt i
        · simp [mutateWithMask, diffMask, heq]
        · cases hiy : y i <;> cases hio : opt i <;>
            simp_all [mutateWithMask, diffMask]
      have hnonempty : diffMask ≠ (∅ : MutationMask n) := by
        intro he
        apply hyne
        simpa [he, mutateWithMask] using hflip
      have haccept : Accepts fitness y opt := by
        change fitness y ≤ fitness opt
        exact hopt y
      have hselected : selectedAfterMask fitness y diffMask = opt := by
        unfold selectedAfterMask
        rw [hflip]
        exact elitistSelect_of_accepts fitness y opt haccept
      let event : MutationMask n → Prop := fun mask =>
        selectedAfterMask fitness y mask = opt
      have hmass : a ≤ finiteEventMass law.weight event := by
        have hsub := sum_le_finiteEventMass_of_subset
          law.weight event ({diffMask} : Finset (MutationMask n))
          law.weight_nonneg (by
            intro mask hmem
            have he : mask = diffMask := Finset.mem_singleton.mp hmem
            subst mask
            exact hselected)
        calc
          a ≤ law.weight diffMask := hfloor diffMask hnonempty
          _ = ∑ mask ∈ ({diffMask} : Finset (MutationMask n)), law.weight mask := by simp
          _ ≤ finiteEventMass law.weight event := hsub
      have hwithin (mask : MutationMask n) :
          B (selectedAfterMask fitness y mask) ≤ 1 / a := by
        by_cases he : selectedAfterMask fitness y mask = opt
        · simpa [B, he] using hBpos.le
        · simp [B, he]
      have hsuccess (mask : MutationMask n) (he : event mask) :
          B (selectedAfterMask fitness y mask) + 1 / a ≤ 1 / a := by
        simp [B, event, he]
      have hweighted := weightedExpectation_add_eventMass_mul_le
        law.weight event (fun mask => B (selectedAfterMask fitness y mask))
        (1 / a) (1 / a)
        law.weight_nonneg law.weight_sum hwithin hsuccess
      have hEV : expectedValueAfter (law.transition fitness) B y =
          ∑ mask : MutationMask n,
            law.weight mask * B (selectedAfterMask fitness y mask) := by
        unfold expectedValueAfter StaticUnaryUnbiasedMutation.transition
          finiteRandomTransition
        exact pushforwardWeight_expectation law.weight
          (selectedAfterMask fitness y) B
      have hfactor : (1 / a : Real) * a = 1 := by
        field_simp [ne_of_gt ha]
      have hmass_scaled : 1 ≤ (1 / a : Real) * finiteEventMass law.weight event := by
        calc
          1 = (1 / a : Real) * a := hfactor.symm
          _ ≤ (1 / a : Real) * finiteEventMass law.weight event :=
            mul_le_mul_of_nonneg_left hmass hBpos.le
      have hBy : B y = 1 / a := by simp [B, hyne]
      rw [hBy, hEV]
      linarith
  have hcert := runtimeSup_le_of_superSolution
    (law.transition fitness) ({opt} : Set (BitString n))
    (law.transition_stochastic fitness) B hBnonneg hsuper x
  have hBx : B x ≤ 1 / a := by
    by_cases hx : x = opt
    · simpa only [B, if_pos hx] using hBpos.le
    · simp [B, hx]
  exact hcert.trans (ENNReal.ofReal_le_ofReal hBx)

end StaticUnaryUnbiasedMutation
end ECRuntime
