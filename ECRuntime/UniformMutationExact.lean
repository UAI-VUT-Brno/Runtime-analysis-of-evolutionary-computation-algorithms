import ECRuntime.ConstantExitRuntime
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.UnrestrictedRuntime
import ECRuntime.Transition
import ECRuntime.LeadingOnesResidence
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

section CandidateDecidability
attribute [local instance] Classical.propDecidable

/-!
Stage 116 promotion candidate (A8): independent bit mutation at p=1/2 generates a
uniform offspring, for EVERY objective. Only nonoptimal initial states have
the geometric expectation 2^n/m, since optimal initial states have cost 0.
Source context: Droste--Jansen--Wegener (2002); Doerr (2019).
-/

/-- Set of global maximizers of a finite pseudo-Boolean fitness function. -/
def finiteGlobalMaximizers {n : Nat}
    (fitness : BitString n → Real) : Set (BitString n) :=
  {x | ∀ y : BitString n, fitness y ≤ fitness x}

/-- Number m of global maximizers, a positive natural number. -/
noncomputable def finiteGlobalMaximizerCount {n : Nat}
    (fitness : BitString n → Real) : Nat := by
  classical
  exact (Finset.univ.filter (fun x : BitString n =>
    x ∈ finiteGlobalMaximizers fitness)).card

/-- With p=1/2, the offspring of every parent is uniform on bitstrings. -/
theorem halfMutation_uniformOffspring
    {n : Nat} (parent y : BitString n) :
    (Finset.univ.sum (fun mask : MutationMask n =>
      if mutateWithMask parent mask = y then
        mutationMaskWeight (n := n) (1 / 2 : Real) mask
      else 0)) = (1 : Real) / (2 : Real) ^ n := by
  classical
  let targetMask : MutationMask n :=
    Finset.univ.filter (fun i => parent i ≠ y i)
  have hflip (mask : MutationMask n) (i : Fin n) :
      i ∈ mask ↔ parent i ≠ mutateWithMask parent mask i := by
    by_cases hi : i ∈ mask
    · cases hpi : parent i <;> simp [mutateWithMask, hi, hpi]
    · simp [mutateWithMask, hi]
  have htarget : mutateWithMask parent targetMask = y := by
    funext i
    by_cases heq : parent i = y i
    · simp [mutateWithMask, targetMask, heq]
    · cases hp : parent i <;> cases hy : y i <;>
        simp_all [mutateWithMask, targetMask]
  have hunique (mask : MutationMask n)
      (heq : mutateWithMask parent mask = y) : mask = targetMask := by
    ext i
    rw [hflip]
    rw [heq]
    simp [targetMask]
  have hiff (mask : MutationMask n) :
      mutateWithMask parent mask = y ↔ mask = targetMask := by
    exact ⟨hunique mask, fun h => h ▸ htarget⟩
  have hweight (mask : MutationMask n) :
      mutationMaskWeight (n := n) (1 / 2 : Real) mask =
        (1 / 2 : Real) ^ n := by
    have hcard : mask.card ≤ n := by
      simpa using Finset.card_le_card (Finset.subset_univ mask)
    unfold mutationMaskWeight
    have hhalf : (1 : Real) - 1 / 2 = 1 / 2 := by norm_num
    rw [hhalf, ← pow_add, Nat.add_sub_of_le hcard]
  simp_rw [hweight, hiff]
  simp

/-- From a nonoptimal state, the chance of hitting the set of global optima
in the next elitist step is exactly m/2^n. -/
theorem halfMutation_nonoptimal_successMass
    {n : Nat} (fitness : BitString n → Real)
    (x : BitString n) (hx : x ∉ finiteGlobalMaximizers fitness) :
    finiteEventMass (mutationMaskWeight (n := n) (1 / 2 : Real))
      (fun mask : MutationMask n =>
        selectedAfterMask fitness x mask ∈ finiteGlobalMaximizers fitness) =
      (finiteGlobalMaximizerCount fitness : Real) / (2 : Real) ^ n := by
  classical
  have hsel (mask : MutationMask n) :
      (selectedAfterMask fitness x mask ∈ finiteGlobalMaximizers fitness) ↔
        (mutateWithMask x mask ∈ finiteGlobalMaximizers fitness) := by
    by_cases hacc : fitness x ≤ fitness (mutateWithMask x mask)
    · simp [selectedAfterMask, elitistSelect, hacc]
    · have hnot : mutateWithMask x mask ∉ finiteGlobalMaximizers fitness := by
        intro hm
        exact hacc (hm x)
      simp [selectedAfterMask, elitistSelect, hacc, hx, hnot]
  have hevents :
      (fun mask : MutationMask n =>
        selectedAfterMask fitness x mask ∈ finiteGlobalMaximizers fitness) =
      (fun mask : MutationMask n =>
        mutateWithMask x mask ∈ finiteGlobalMaximizers fitness) := by
    funext mask
    exact propext (hsel mask)
  rw [hevents, ← finiteEventMass_pushforwardWeight]
  have hunif :
      pushforwardWeight
        (mutationMaskWeight (n := n) (1 / 2 : Real))
        (mutateWithMask x) = fun _ => (1 : Real) / (2 : Real) ^ n := by
    funext y
    exact halfMutation_uniformOffspring x y
  rw [hunif]
  let s : Finset (BitString n) :=
    Finset.univ.filter (fun y => y ∈ finiteGlobalMaximizers fitness)
  have hsum :
      finiteEventMass (fun _ : BitString n => (1 : Real) / (2 : Real) ^ n)
        (fun y => y ∈ finiteGlobalMaximizers fitness) =
      ∑ y ∈ s, (1 : Real) / (2 : Real) ^ n := by
    unfold finiteEventMass
    calc
      (∑ y : BitString n,
          ({y | y ∈ finiteGlobalMaximizers fitness} : Set (BitString n)).indicator
            (fun _ => (1 : Real) / (2 : Real) ^ n) y) =
          ∑ y : BitString n,
            if y ∈ s then (1 : Real) / (2 : Real) ^ n else 0 := by
              apply Finset.sum_congr rfl
              intro y _
              by_cases hy : y ∈ finiteGlobalMaximizers fitness
              · have hmem : y ∈
                    ({z : BitString n |
                      z ∈ finiteGlobalMaximizers fitness} : Set (BitString n)) := hy
                rw [Set.indicator_of_mem hmem (fun _ => (1 : Real) / (2 : Real) ^ n)]
                simp [s, hy]
              · have hnotmem : y ∉
                    ({z : BitString n |
                      z ∈ finiteGlobalMaximizers fitness} : Set (BitString n)) := hy
                rw [Set.indicator_of_notMem hnotmem (fun _ => (1 : Real) / (2 : Real) ^ n)]
                simp [s, hy]
      _ = ∑ y ∈ s, (1 : Real) / (2 : Real) ^ n :=
        Finset.sum_ite_mem_eq _ _
  rw [hsum, Finset.sum_const, nsmul_eq_mul]
  change (finiteGlobalMaximizerCount fitness : Real) *
    ((1 : Real) / (2 : Real) ^ n) = _
  ring

/-- A finite-horizon analogue of the uniform-search runtime theorem.  The
nonoptimal region has constant probability `m / 2^n` of being left at each
step, independently of which nonoptimal search point is currently visited. -/
private theorem halfMutation_nonoptimal_finiteSurvival_exact
    {n : Nat} (fitness : BitString n → Real)
    (x : BitString n) (hx : x ∉ finiteGlobalMaximizers fitness)
    (t : Nat) :
    finiteLevelSurvival (onePlusOneTransition (1 / 2 : Real) fitness)
      ({y : BitString n | y ∉ finiteGlobalMaximizers fitness} : Set (BitString n))
      t x =
    (1 - (finiteGlobalMaximizerCount fitness : Real) / (2 : Real) ^ n) ^ t := by
  classical
  let nonoptimal : Set (BitString n) :=
    {y | y ∉ finiteGlobalMaximizers fitness}
  have hexit : ∀ y : BitString n, y ∈ nonoptimal →
      finiteEventMass (onePlusOneTransition (1 / 2 : Real) fitness y)
        (fun z => z ∉ nonoptimal) =
      (finiteGlobalMaximizerCount fitness : Real) / (2 : Real) ^ n := by
    intro y hy
    have hy' : y ∉ finiteGlobalMaximizers fitness := hy
    have hevent : (fun z : BitString n => z ∉ nonoptimal) =
        (fun z : BitString n => z ∈ finiteGlobalMaximizers fitness) := by
      funext z
      apply propext
      simp [nonoptimal]
    rw [hevent]
    unfold onePlusOneTransition
    rw [finiteEventMass_pushforwardWeight]
    exact halfMutation_nonoptimal_successMass fitness y hy'
  have hP : IsStochastic (onePlusOneTransition (1 / 2 : Real) fitness) :=
    onePlusOneTransition_stochastic (by norm_num) (by norm_num) fitness
  exact finiteLevelSurvival_eq_geometric_of_exact_exit_mass
    (onePlusOneTransition (1 / 2 : Real) fitness) nonoptimal hP
    ((finiteGlobalMaximizerCount fitness : Real) / (2 : Real) ^ n)
    hexit t x hx

/-- Every fitness on a nonempty finite bitstring space attains a maximum. -/
private theorem candidate_finiteGlobalMaximizerCount_pos
    {n : Nat} (fitness : BitString n → Real) :
    0 < finiteGlobalMaximizerCount fitness := by
  classical
  let s : Finset Real := (Finset.univ : Finset (BitString n)).image fitness
  have hnonempty : (Finset.univ : Finset (BitString n)).Nonempty :=
    ⟨allOnes n, Finset.mem_univ _⟩
  have hs : s.Nonempty := hnonempty.image fitness
  obtain ⟨x, _hx, hfx⟩ := Finset.mem_image.mp (Finset.max'_mem s hs)
  have hopt : x ∈ finiteGlobalMaximizers fitness := by
    intro y
    have hy : fitness y ∈ s := Finset.mem_image.mpr
      ⟨y, Finset.mem_univ _, rfl⟩
    calc
      fitness y ≤ s.max' hs := Finset.le_max' s (fitness y) hy
      _ = fitness x := hfx.symm
  unfold finiteGlobalMaximizerCount
  exact Finset.card_pos.mpr
    ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopt⟩⟩

/-- A global optimum set contains at most `2^n` states. -/
private theorem candidate_finiteGlobalMaximizerCount_le
    {n : Nat} (fitness : BitString n → Real) :
    finiteGlobalMaximizerCount fitness ≤ 2 ^ n := by
  classical
  have hsub : (Finset.univ.filter (fun x : BitString n =>
      x ∈ finiteGlobalMaximizers fitness)).card ≤
        (Finset.univ : Finset (BitString n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [finiteGlobalMaximizerCount, BitString] using hsub

/-- Exact unrestricted expectation from a nonoptimal initial state, with
initial evaluation excluded. -/
theorem halfMutation_nonoptimal_runtimeSup_eq
    {n : Nat} (fitness : BitString n → Real)
    (x : BitString n) (hx : x ∉ finiteGlobalMaximizers fitness) :
    runtimeSup (onePlusOneTransition (1 / 2 : Real) fitness)
      (finiteGlobalMaximizers fitness) x =
      ENNReal.ofReal
        ((2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real)) := by
  classical
  let P : TransitionMatrix (BitString n) :=
    onePlusOneTransition (1 / 2 : Real) fitness
  let q : Real := (finiteGlobalMaximizerCount fitness : Real) / (2 : Real) ^ n
  have hP : IsStochastic P :=
    onePlusOneTransition_stochastic (by norm_num) (by norm_num) fitness
  have hmpos : 0 < (finiteGlobalMaximizerCount fitness : Real) := by
    exact_mod_cast candidate_finiteGlobalMaximizerCount_pos fitness
  have hdenpos : (0 : Real) < 2 ^ n := by positivity
  have hqpos : 0 < q := div_pos hmpos hdenpos
  have hqle : q ≤ 1 := by
    apply (div_le_one hdenpos).2
    exact_mod_cast candidate_finiteGlobalMaximizerCount_le fitness
  have heq : (finiteGlobalMaximizers fitness)ᶜ =
      ({y : BitString n | y ∉ finiteGlobalMaximizers fitness} : Set (BitString n)) := by
    ext y
    rfl
  have hsurvival : ∀ t : Nat,
      finiteLevelSurvival P (finiteGlobalMaximizers fitness)ᶜ t x = (1 - q) ^ t := by
    intro t
    simpa only [heq] using
      (halfMutation_nonoptimal_finiteSurvival_exact fitness x hx t)
  have hexact := candidate_runtimeSup_eq_inv_of_geometric_survival
    P (finiteGlobalMaximizers fitness) hP q hqpos hqle x hsurvival
  calc
    runtimeSup (onePlusOneTransition (1 / 2 : Real) fitness)
        (finiteGlobalMaximizers fitness) x = ENNReal.ofReal q⁻¹ := hexact
    _ = ENNReal.ofReal
          ((2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real)) := by
      congr 1
      simp only [q, inv_div]

/-- Uniform initial states give average real-valued optimization time
(2^n-m)/m. The expected time here averages the deterministic-start
expectations: an already optimal initial string contributes zero. -/
theorem halfMutation_uniformInitial_average
    {n : Nat} (fitness : BitString n → Real) :
    (Finset.univ.sum (fun x : BitString n =>
      if x ∈ finiteGlobalMaximizers fitness then (0 : Real)
      else (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real))) /
        (2 : Real) ^ n =
      ((2 : Real) ^ n - (finiteGlobalMaximizerCount fitness : Real)) /
        (finiteGlobalMaximizerCount fitness : Real) := by
  classical
  let s : Finset (BitString n) :=
    Finset.univ.filter (fun x => x ∈ finiteGlobalMaximizers fitness)
  have hcard : s.card = finiteGlobalMaximizerCount fitness := by rfl
  have hsize : (Finset.univ : Finset (BitString n)).card = 2 ^ n := by
    simp [BitString]
  have hdecomp : ((Finset.univ : Finset (BitString n)) \ s).card + s.card =
      (Finset.univ : Finset (BitString n)).card :=
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ s)
  have hcomp :
      (((Finset.univ : Finset (BitString n)) \ s).card : Real) =
        (2 : Real) ^ n - (finiteGlobalMaximizerCount fitness : Real) := by
    rw [hsize] at hdecomp
    have hreal :
        (((Finset.univ : Finset (BitString n)) \ s).card : Real) +
          (s.card : Real) = (2 : Real) ^ n := by exact_mod_cast hdecomp
    rw [hcard] at hreal
    linarith
  have hsum :
      (∑ x : BitString n,
        if x ∈ finiteGlobalMaximizers fitness then (0 : Real)
        else (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real)) =
      ∑ x ∈ ((Finset.univ : Finset (BitString n)) \ s),
        (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real) := by
    calc
      (∑ x : BitString n,
          if x ∈ finiteGlobalMaximizers fitness then (0 : Real)
          else (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real)) =
        ∑ x : BitString n,
          if x ∈ ((Finset.univ : Finset (BitString n)) \ s) then
            (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real) else 0 := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : x ∈ finiteGlobalMaximizers fitness <;>
                simp [s, hx]
      _ = ∑ x ∈ ((Finset.univ : Finset (BitString n)) \ s),
            (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real) :=
        Finset.sum_ite_mem_eq _ _
  have hb : (2 : Real) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    (∑ x : BitString n,
        if x ∈ finiteGlobalMaximizers fitness then (0 : Real)
        else (2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real)) /
        (2 : Real) ^ n =
      ((((Finset.univ : Finset (BitString n)) \ s).card : Real) *
        ((2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real))) /
          (2 : Real) ^ n := by
        rw [hsum, Finset.sum_const, nsmul_eq_mul]
    _ = (((2 : Real) ^ n - (finiteGlobalMaximizerCount fitness : Real)) *
        ((2 : Real) ^ n / (finiteGlobalMaximizerCount fitness : Real))) /
          (2 : Real) ^ n := by rw [hcomp]
    _ = ((2 : Real) ^ n - (finiteGlobalMaximizerCount fitness : Real)) /
          (finiteGlobalMaximizerCount fitness : Real) := by
        simp only [div_eq_mul_inv]
        calc
          _ = (((2 : Real) ^ n - (finiteGlobalMaximizerCount fitness : Real)) *
                (finiteGlobalMaximizerCount fitness : Real)⁻¹) *
              ((2 : Real) ^ n * ((2 : Real) ^ n)⁻¹) := by ring
          _ = _ := by rw [mul_inv_cancel₀ hb, mul_one]

end CandidateDecidability
end ECRuntime
