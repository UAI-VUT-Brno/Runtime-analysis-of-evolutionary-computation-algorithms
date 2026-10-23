import ECRuntime.ConstantExitRuntime
import ECRuntime.LevelExitTrajectory
import ECRuntime.MultiplicativeDriftTail
import ECRuntime.StaticUnaryUnbiasedMutation
import ECRuntime.OneMax
import ECRuntime.StaticUnaryUnbiasedAcceptedEventBridge
import ECRuntime.UnrestrictedRuntime
import ECRuntime.TrajectoryFirstHittingTime
import ECRuntime.GeometricTail
import ECRuntime.LeadingOnesResidence
import Mathlib

open scoped BigOperators ENNReal
open MeasureTheory

namespace ECRuntime

/-!
Candidate 113 (A5): exactly geometric escape from the Jump_k LOCAL optimum
layer. Does not prove the total runtime from a random initial search point.
This is Jump_k with a SINGLE Hamming-weight local optimum layer, NOT Plateau_k.
Source context: Doerr--Le--Makhmara--Nguyen (2017), Fast Genetic Algorithms.
Provisional public integration pending the full pinned promotion gate.
-/

/-- A standard maximization Jump_k objective with the local optimum layer
zeroCount=k, the valley 0<zeroCount<k, and the unique all-ones optimum. -/
def jumpFitness {n : Nat} (k : Nat) (x : BitString n) : Real :=
  if zeroCount x = 0 then (n + k : Nat)
  else if k ≤ zeroCount x then (oneCount x + k : Nat)
  else (zeroCount x : Nat)

/-- The local optimum layer is closed under non-successful elitist steps;
neutral moves within that same layer are allowed. -/
theorem jump_plateau_closed_under_selection
    {n : Nat} (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (x : BitString n) (hx : zeroCount x = k) (mask : MutationMask n) :
    zeroCount (selectedAfterMask (jumpFitness k) x mask) = k ∨
      selectedAfterMask (jumpFitness k) x mask = allOnes n := by
  -- Retain the approved local-optimum precondition in the source proof.
  have _hminimumJump : 2 ≤ k := hk
  have hxcount : oneCount x + k = n := by
    have h := oneCount_add_zeroCount x
    omega
  have hxfit : jumpFitness k x = (n : Real) := by
    simp [jumpFitness, hx, hxcount]
  have hplateau (y : BitString n)
      (hy : (n : Real) ≤ jumpFitness k y) :
      zeroCount y = k ∨ y = allOnes n := by
    by_cases hz0 : zeroCount y = 0
    · right
      exact (oneMaxPotential_eq_zero_iff y).mp hz0
    · by_cases hkz : k ≤ zeroCount y
      · left
        have hfit : jumpFitness k y = ((oneCount y + k : Nat) : Real) := by
          simp [jumpFitness, hz0, hkz]
        have hnle : n ≤ oneCount y + k := by
          have hnleR : (n : Real) ≤ ((oneCount y + k : Nat) : Real) := by
            simpa [hfit] using hy
          exact_mod_cast hnleR
        have hncount := oneCount_add_zeroCount y
        omega
      · have hfit : jumpFitness k y = (zeroCount y : Real) := by
          simp [jumpFitness, hz0, hkz]
        have hzlt : zeroCount y < n := by omega
        have hzltR : (zeroCount y : Real) < (n : Real) := by
          exact_mod_cast hzlt
        exact False.elim ((not_le_of_gt hzltR) (by simpa [hfit] using hy))
  by_cases hacc : Accepts (jumpFitness k) x (mutateWithMask x mask)
  · have hle : (n : Real) ≤ jumpFitness k (mutateWithMask x mask) := by
      rw [← hxfit]
      exact hacc
    have hclass := hplateau (mutateWithMask x mask) hle
    simpa [selectedAfterMask, elitistSelect_of_accepts _ _ _ hacc] using hclass
  · simp [selectedAfterMask, elitistSelect_of_rejects _ _ _ hacc, hx]

/-- The exact one-step probability of hitting the all-one optimum from
any Jump_k local optimum equals p_k / choose(n,k). -/
theorem jump_plateau_oneStepSuccessMass
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (x : BitString n) (hx : zeroCount x = k) :
    finiteEventMass law.weight
      (fun mask : MutationMask n =>
        selectedAfterMask (jumpFitness k) x mask = allOnes n) =
      law.radiusMass k / (Nat.choose n k : Real) := by
  classical
  have hxcount : oneCount x + k = n := by
    have h := oneCount_add_zeroCount x
    omega
  have hxfit : jumpFitness k x = (n : Real) := by
    simp [jumpFitness, hx, hxcount]
  have hxne : x ≠ allOnes n := by
    intro he
    have hz := zeroCount_allOnes n
    rw [he] at hx
    omega
  have hiff (mask : MutationMask n) :
      mutateWithMask x mask = allOnes n ↔ mask = zeroPositions x := by
    constructor
    · intro heq
      ext i
      have hi := congrArg (fun y : BitString n => y i) heq
      cases hxi : x i <;> by_cases him : i ∈ mask <;>
        simp_all [mutateWithMask, allOnes, mem_zeroPositions]
    · intro heq
      subst mask
      funext i
      cases hxi : x i <;>
        simp [mutateWithMask, allOnes, mem_zeroPositions, hxi]
  have hselected (mask : MutationMask n) :
      selectedAfterMask (jumpFitness k) x mask = allOnes n ↔
        mutateWithMask x mask = allOnes n := by
    constructor
    · intro heq
      by_cases hacc : Accepts (jumpFitness k) x (mutateWithMask x mask)
      · simpa [selectedAfterMask,
          elitistSelect_of_accepts _ _ _ hacc] using heq
      · have hreject : selectedAfterMask (jumpFitness k) x mask = x := by
          simp [selectedAfterMask, elitistSelect_of_rejects _ _ _ hacc]
        exact False.elim (hxne (hreject.symm.trans heq))
    · intro heq
      have hacc : Accepts (jumpFitness k) x (mutateWithMask x mask) := by
        unfold Accepts
        rw [hxfit, heq]
        have hfit : jumpFitness k (allOnes n) = ((n + k : Nat) : Real) := by
          simp [jumpFitness]
        rw [hfit]
        exact_mod_cast Nat.le_add_right n k
      simpa [selectedAfterMask,
        elitistSelect_of_accepts _ _ _ hacc] using heq
  have hprob :
      finiteEventMass law.weight (fun mask : MutationMask n =>
        selectedAfterMask (jumpFitness k) x mask = allOnes n) =
      law.weight (zeroPositions x) := by
    unfold finiteEventMass
    calc
      (∑ mask : MutationMask n,
          ({mask | selectedAfterMask (jumpFitness k) x mask = allOnes n} :
            Set (MutationMask n)).indicator law.weight mask) =
          ∑ mask : MutationMask n,
            if mask = zeroPositions x then law.weight mask else 0 := by
              apply Finset.sum_congr rfl
              intro mask _
              by_cases hm : mask = zeroPositions x
              · have he : mask ∈
                    ({m : MutationMask n |
                      selectedAfterMask (jumpFitness k) x m = allOnes n} :
                      Set (MutationMask n)) :=
                  (hselected mask).2 ((hiff mask).2 hm)
                rw [Set.indicator_of_mem he law.weight]
                simp [hm]
              · have he : mask ∉
                    ({m : MutationMask n |
                      selectedAfterMask (jumpFitness k) x m = allOnes n} :
                      Set (MutationMask n)) := by
                  intro h
                  exact hm ((hiff mask).1 ((hselected mask).1 h))
                rw [Set.indicator_of_notMem he law.weight]
                simp [hm]
      _ = law.weight (zeroPositions x) := by simp
  have hmaskcard : (zeroPositions x).card = k := by
    simpa [zeroPositions_card] using hx
  have hsum : law.radiusMass k =
      (Nat.choose n k : Real) * law.weight (zeroPositions x) := by
    unfold StaticUnaryUnbiasedMutation.radiusMass
    calc
      (∑ mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
          law.weight mask) =
          ∑ _mask ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)),
            law.weight (zeroPositions x) := by
              apply Finset.sum_congr rfl
              intro mask hm
              have hcard : mask.card = k :=
                (Finset.mem_powersetCard.mp hm).2
              exact law.card_invariant (hcard.trans hmaskcard.symm)
      _ = (Nat.choose n k : Real) * law.weight (zeroPositions x) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
          simp
  have hchoose : (Nat.choose n k : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : k ≤ n)))
  rw [hprob]
  apply (eq_div_iff hchoose).2
  simpa [mul_comm] using hsum.symm

/-- A supporting finite-horizon geometric-survival lemma.  From the local
optimum layer, an elitist step exits that layer exactly when it finds the
unique global optimum.  This is not yet the infinite-horizon runtime theorem. -/
private theorem jump_plateau_finiteSurvival_exact
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (x : BitString n) (hx : zeroCount x = k) (t : Nat) :
    finiteLevelSurvival (law.transition (jumpFitness k))
      ({y : BitString n | zeroCount y = k} : Set (BitString n)) t x =
      (1 - law.radiusMass k / (Nat.choose n k : Real)) ^ t := by
  classical
  let layer : Set (BitString n) := {y | zeroCount y = k}
  let P := law.transition (jumpFitness k)
  have hexit : ∀ z : BitString n, z ∈ layer →
      finiteEventMass (P z) (fun y => y ∉ layer) =
        law.radiusMass k / (Nat.choose n k : Real) := by
    intro z hz
    have hzcount : zeroCount z = k := hz
    have hiff (mask : MutationMask n) :
        selectedAfterMask (jumpFitness k) z mask ∉ layer ↔
          selectedAfterMask (jumpFitness k) z mask = allOnes n := by
      rcases jump_plateau_closed_under_selection k hk hkn z hzcount mask with
        hstay | hsuccess
      · constructor
        · intro hnot
          exact False.elim (hnot hstay)
        · intro hopt
          rw [hopt] at hstay
          have hstayCount : zeroCount (allOnes n) = k := hstay
          rw [zeroCount_allOnes] at hstayCount
          omega
      · constructor
        · intro _
          exact hsuccess
        · intro _ hmem
          rw [hsuccess] at hmem
          have hmemCount : zeroCount (allOnes n) = k := hmem
          rw [zeroCount_allOnes] at hmemCount
          omega
    calc
      finiteEventMass (P z) (fun y => y ∉ layer) =
          finiteEventMass law.weight (fun mask : MutationMask n =>
            selectedAfterMask (jumpFitness k) z mask ∉ layer) := by
        unfold P StaticUnaryUnbiasedMutation.transition finiteRandomTransition
        exact finiteEventMass_pushforwardWeight law.weight
          (selectedAfterMask (jumpFitness k) z) (fun y => y ∉ layer)
      _ = finiteEventMass law.weight (fun mask : MutationMask n =>
            selectedAfterMask (jumpFitness k) z mask = allOnes n) := by
        apply congrArg (finiteEventMass law.weight)
        funext mask
        exact propext (hiff mask)
      _ = law.radiusMass k / (Nat.choose n k : Real) :=
        jump_plateau_oneStepSuccessMass law k hk hkn z hzcount
  exact finiteLevelSurvival_eq_geometric_of_exact_exit_mass
    P layer (law.transition_stochastic (jumpFitness k))
    (law.radiusMass k / (Nat.choose n k : Real)) hexit t x hx

/-- A nonzero transition from the Jump local optimum has support only
on the plateau and at the unique optimum. -/
private theorem jump_plateau_transition_zero_off_layer
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (z : BitString n) (hz : zeroCount z = k)
    (y : BitString n) (hy : zeroCount y ≠ k)
    (hyopt : y ≠ allOnes n) :
    (law.transition (jumpFitness k)) z y = 0 := by
  classical
  unfold StaticUnaryUnbiasedMutation.transition
    finiteRandomTransition pushforwardWeight
  apply Finset.sum_eq_zero
  intro mask _
  have hs := jump_plateau_closed_under_selection k hk hkn z hz mask
  have hne : selectedAfterMask (jumpFitness k) z mask ≠ y := by
    intro he
    rcases hs with hstay | hopt
    · exact hy (he ▸ hstay)
    · exact hyopt (he ▸ hopt)
  simp [hne]

/-- Along paths starting on the plateau, not hitting the global optimum
and remaining on the plateau have the same survival probability. -/
private theorem jump_plateau_survival_target_compl_eq_layer
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n) :
    ∀ t : Nat, ∀ z : BitString n, zeroCount z = k →
      finiteLevelSurvival (law.transition (jumpFitness k))
        ({allOnes n} : Set (BitString n))ᶜ t z =
      finiteLevelSurvival (law.transition (jumpFitness k))
        ({y : BitString n | zeroCount y = k} : Set (BitString n)) t z := by
  classical
  let P := law.transition (jumpFitness k)
  let target : Set (BitString n) := {allOnes n}
  let layer : Set (BitString n) := {y | zeroCount y = k}
  intro t
  induction t with
  | zero =>
      intro z hz
      have hzopt : z ≠ allOnes n := by
        intro he
        rw [he, zeroCount_allOnes] at hz
        omega
      have hzc : z ∈ targetᶜ := by simpa [target] using hzopt
      have hzl : z ∈ layer := hz
      rw [finiteLevelSurvival_zero_of_mem P targetᶜ z hzc,
        finiteLevelSurvival_zero_of_mem P layer z hzl]
  | succ t ih =>
      intro z hz
      have hzopt : z ≠ allOnes n := by
        intro he
        rw [he, zeroCount_allOnes] at hz
        omega
      have hzc : z ∈ targetᶜ := by simpa [target] using hzopt
      have hzl : z ∈ layer := hz
      rw [finiteLevelSurvival_succ_of_mem P targetᶜ t z hzc,
        finiteLevelSurvival_succ_of_mem P layer t z hzl]
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : zeroCount y = k
      · rw [ih y hy]
      · by_cases hyopt : y = allOnes n
        · have hyc : y ∉ targetᶜ := by simp [target, hyopt]
          have hyl : y ∉ layer := by simpa [layer] using hy
          rw [finiteLevelSurvival_eq_zero_of_not_mem P targetᶜ t y hyc,
            finiteLevelSurvival_eq_zero_of_not_mem P layer t y hyl]
        · have hzero : P z y = 0 :=
            jump_plateau_transition_zero_off_layer law k hk hkn z hz y hy hyopt
          simp [hzero]

/-- Exact geometric survival outside the *true target*, not just inside
the local optimum layer. -/
private theorem jump_plateau_finiteSurvival_trueTarget
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (x : BitString n) (hx : zeroCount x = k) (t : Nat) :
    finiteLevelSurvival (law.transition (jumpFitness k))
      ({allOnes n} : Set (BitString n))ᶜ t x =
      (1 - law.radiusMass k / (Nat.choose n k : Real)) ^ t := by
  rw [jump_plateau_survival_target_compl_eq_layer law k hk hkn t x hx]
  exact jump_plateau_finiteSurvival_exact law k hk hkn x hx t

/-- The plateau escape probability is in `(0,1]`. -/
private theorem jump_plateau_escapeRate_mem_Ioc
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (_hk : 2 ≤ k) (hkn : k < n)
    (hp : 0 < law.radiusMass k) :
    0 < law.radiusMass k / (Nat.choose n k : Real) ∧
      law.radiusMass k / (Nat.choose n k : Real) ≤ 1 := by
  have hknle : k ≤ n := by omega
  have hchoosePos : 0 < Nat.choose n k := Nat.choose_pos hknle
  have hden : (0 : Real) < Nat.choose n k := by exact_mod_cast hchoosePos
  have hchooseOne : (1 : Real) ≤ Nat.choose n k := by
    exact_mod_cast hchoosePos
  have hmass : law.radiusMass k ≤ 1 := by
    have hkMem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hle := Finset.single_le_sum
      (fun j _ => law.radiusMass_nonneg j) hkMem
    rw [law.sum_radiusMass_eq_one] at hle
    exact hle
  refine ⟨div_pos hp hden, ?_⟩
  exact (div_le_one hden).mpr (hmass.trans hchooseOne)

/-- Exact expected number of iterations for escape FROM the local-optimum
layer, regardless of neutral movement within the layer. -/
theorem jump_plateau_runtimeSup_eq_geometricMean
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (hp : 0 < law.radiusMass k)
    (x : BitString n) (hx : zeroCount x = k) :
    runtimeSup (law.transition (jumpFitness k))
      ({allOnes n} : Set (BitString n)) x =
      ENNReal.ofReal ((Nat.choose n k : Real) / law.radiusMass k) := by
  classical
  let P := law.transition (jumpFitness k)
  let q : Real := law.radiusMass k / (Nat.choose n k : Real)
  obtain ⟨hq0, hq1⟩ := jump_plateau_escapeRate_mem_Ioc law k hk hkn hp
  have hP : IsStochastic P := law.transition_stochastic (jumpFitness k)
  have hsurvival : ∀ t : Nat,
      finiteLevelSurvival P ({allOnes n} : Set (BitString n))ᶜ t x =
        (1 - q) ^ t := by
    intro t
    exact jump_plateau_finiteSurvival_trueTarget law k hk hkn x hx t
  have h := candidate_runtimeSup_eq_inv_of_geometric_survival
    P ({allOnes n} : Set (BitString n)) hP q hq0 hq1 x hsurvival
  calc
    runtimeSup (law.transition (jumpFitness k))
        ({allOnes n} : Set (BitString n)) x = ENNReal.ofReal q⁻¹ := h
    _ = ENNReal.ofReal ((Nat.choose n k : Real) / law.radiusMass k) := by
      congr 1
      simp only [q, inv_div]

/-- Exact geometric survival tail conditional on the initial state being
in the local-optimum layer. -/
theorem jump_plateau_runtimeTail_eq_geometric
    {n : Nat} (law : StaticUnaryUnbiasedMutation n)
    (k : Nat) (hk : 2 ≤ k) (hkn : k < n)
    (hp : 0 < law.radiusMass k)
    [MeasurableSpace (BitString n)]
    [MeasurableSingletonClass (BitString n)]
    (x : BitString n) (hx : zeroCount x = k) (t : Nat) :
    runtimeTailMass
      (transitionTrajectoryMeasure
        (law.transition (jumpFitness k))
        (law.transition_stochastic (jumpFitness k)) x)
      (transitionTrajectoryFirstHittingTime
        ({allOnes n} : Set (BitString n)) x) (t : ENNReal) =
      ENNReal.ofReal
        ((1 - law.radiusMass k / (Nat.choose n k : Real)) ^ t) := by
  classical
  have _ : 0 < law.radiusMass k := hp
  let P := law.transition (jumpFitness k)
  have hP : IsStochastic P := law.transition_stochastic (jumpFitness k)
  have htail := transitionTrajectoryLevelExit_tailMass_eq_finiteLevelSurvival
    P (({allOnes n} : Set (BitString n))ᶜ) hP x t
  have htarget :
      (({allOnes n} : Set (BitString n))ᶜ)ᶜ =
        ({allOnes n} : Set (BitString n)) := by
    ext z
    simp
  have hhit := transitionTrajectoryFirstHittingTime_congr_set
    (({allOnes n} : Set (BitString n))ᶜ)ᶜ
    ({allOnes n} : Set (BitString n)) htarget x
  have htail' :
      runtimeTailMass
        (transitionTrajectoryMeasure P hP x)
        (transitionTrajectoryFirstHittingTime
          ({allOnes n} : Set (BitString n)) x) (t : ENNReal) =
      ENNReal.ofReal
        (finiteLevelSurvival P
          (({allOnes n} : Set (BitString n))ᶜ) t x) := by
    rw [← hhit]
    exact htail
  rw [jump_plateau_finiteSurvival_trueTarget law k hk hkn x hx t] at htail'
  exact htail' 

end ECRuntime
