import ECRuntime.AdditiveDrift
import ECRuntime.HittingTime
import Mathlib

namespace ECRuntime

/-! P07 general additive-drift lower bound frontier. Finite-horizon
stopping-time bounds require a residual-potential term; directly
reversing the existing upper-drift Bellman certificate is invalid. -/

/-- Residual potential after a finite number of transitions, frozen at
first entry to the target. This is a finite recursive expectation. -/
noncomputable def finiteStoppedPotential {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (target : Set α)
    [DecidablePred (fun y : α => y ∈ target)]
    (potential : α → Real) : Nat → α → Real
  | 0, y => potential y
  | t + 1, y =>
      if y ∈ target then potential y
      else ∑ z : α, P y z * finiteStoppedPotential P target potential t z

/-- Explicit finite-horizon drift inequality with the nonnegative residual
potential retained. This is the finite stopped-process ingredient of
Stage 352, and does not assume a zero residual at a finite horizon. -/
theorem proposed_genericDriftLower_finiteHorizon_withResidual
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (target : Set α) [DecidablePred (fun y : α => y ∈ target)]
    (potential : α → Real)
    (hpot : ∀ y, 0 ≤ potential y)
    (hzero : ∀ y ∈ target, potential y = 0)
    (δ : Real) (hδ : 0 < δ)
    (hstep : ∀ y ∉ target,
      (∑ z : α, P y z * (potential y - potential z)) ≤ δ)
    (x : α) (t : Nat) :
    potential x ≤ δ * finiteHorizonRuntime P target t x +
      finiteStoppedPotential P target potential t x := by
  classical
  -- The finite-horizon inequality does not need a positive lower bound on
  -- the residual: it is deliberately retained on the right-hand side.
  have hdiff (y : α) :
      (∑ z : α, P y z * (potential y - potential z)) =
        potential y - expectedValueAfter P potential y := by
    calc
      (∑ z : α, P y z * (potential y - potential z)) =
          (∑ z : α, P y z * potential y) -
            (∑ z : α, P y z * potential z) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro z hz
          ring
      _ = potential y - expectedValueAfter P potential y := by
          rw [← Finset.sum_mul, hP.2 y, one_mul]
          rfl
  induction t generalizing x with
  | zero =>
      have hstart_nonneg : 0 ≤ potential x := hpot x
      have hdelta_nonneg : 0 ≤ δ := hδ.le
      have _ : 0 ≤ potential x + δ := add_nonneg hstart_nonneg hdelta_nonneg
      simp [finiteHorizonRuntime, finiteStoppedPotential]
  | succ t ih =>
      by_cases hx : x ∈ target
      · simp [finiteStoppedPotential, hx, hzero x hx]
      · have hd : potential x ≤ δ + expectedValueAfter P potential x := by
          have h := hstep x hx
          rw [hdiff x] at h
          linarith
        have hrec : ∀ z : α,
            potential z ≤ δ * finiteHorizonRuntime P target t z +
              finiteStoppedPotential P target potential t z := ih
        have hev := expectedValueAfter_mono P hP potential
          (fun z => δ * finiteHorizonRuntime P target t z +
             finiteStoppedPotential P target potential t z) hrec x
        calc
          potential x ≤ δ + expectedValueAfter P potential x := hd
          _ ≤ δ + expectedValueAfter P
              (fun z => δ * finiteHorizonRuntime P target t z +
                finiteStoppedPotential P target potential t z) x := by
                  linarith
          _ = δ * finiteHorizonRuntime P target (t + 1) x +
              finiteStoppedPotential P target potential (t + 1) x := by
                rw [expectedValueAfter_add, expectedValueAfter_const_mul]
                rw [finiteHorizonRuntime_succ_of_not_mem P target t x hx]
                simp only [finiteStoppedPotential, if_neg hx]
                -- The remaining syntactic difference is the defining finite sum
                -- of `expectedValueAfter`, not a missing drift estimate.
                simp only [expectedValueAfter]
                ring

end ECRuntime
