import ECRuntime.LeadingOnesResidence
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-!
# Stage 168 candidate: state-dependent LeadingOnes mutation kernel

Source direction: Boettcher--Doerr--Neumann (2010), adaptive-rate LeadingOnes.
This stage builds only the exact stochastic semantics and local geometric
residence law; it does not assume independent suffix bits along the process.

A rate schedule is indexed by the natural-valued LeadingOnes score, including
score `n` at the absorbing optimum. This avoids an invalid `Fin n` lookup for
the optimum. Endpoints 0 and 1 are permitted here; optimization of the rate
and the positive-rate mean residence will require more specific conditions.

These three user-approved statement headers now have proof candidates. They
remain outside the public aggregator until compiler, axiom and promotion checks
have passed; source code alone is not a promotion certificate.
-/

/-- Elitist (1+1)-EA transition with mutation rate chosen from the current
LeadingOnes score. Only the current parent state determines the rate. -/
noncomputable def leadingOnesAdaptiveTransition
    {n : ℕ} (rate : ℕ → ℝ) : TransitionMatrix (BitString n) :=
  fun x y =>
    onePlusOneTransition (rate (leadingOnes x))
      (leadingOnesReal (n := n)) x y

/-- Non-vacuity witness for the rate-range hypothesis: a constant
half-mutation schedule is admissible in dimension one. -/
example : ∀ j : ℕ, j ≤ 1 →
    (0 : ℝ) ≤ (fun _ : ℕ => (1 / 2 : ℝ)) j ∧
      (fun _ : ℕ => (1 / 2 : ℝ)) j ≤ 1 := by
  intro j _hj
  norm_num

/-- The bounded schedule hypothesis suffices for stochasticity, even when the
state is the optimum and its LeadingOnes score equals `n`. -/
theorem proposed_leadingOnesAdaptive_transition_stochastic
    {n : ℕ} (rate : ℕ → ℝ)
    (hrate : ∀ j : ℕ, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1) :
    IsStochastic (leadingOnesAdaptiveTransition (n := n) rate) := by
  constructor
  · intro x y
    change 0 ≤ onePlusOneTransition (rate (leadingOnes x))
      (leadingOnesReal (n := n)) x y
    have h := hrate (leadingOnes x) (leadingOnes_le x)
    exact (onePlusOneTransition_stochastic h.1 h.2
      (leadingOnesReal (n := n))).1 x y
  · intro x
    change (∑ y : BitString n,
      onePlusOneTransition (rate (leadingOnes x))
        (leadingOnesReal (n := n)) x y) = 1
    have h := hrate (leadingOnes x) (leadingOnes_le x)
    exact (onePlusOneTransition_stochastic h.1 h.2
      (leadingOnesReal (n := n))).2 x

/-- Exact one-step exit mass from a nonterminal LeadingOnes level. The
probability depends on the scheduled rate at that level and not on the suffix
of the particular state. No positivity assumption is required for this
algebraic identity. -/
theorem proposed_leadingOnesAdaptive_exactLevel_exitMass
    {n : ℕ} (rate : ℕ → ℝ) (i : Fin n) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    finiteEventMass ((leadingOnesAdaptiveTransition rate) x)
        (fun y => leadingOnes y ≠ i.val) =
      rate i.val * (1 - rate i.val) ^ i.val := by
  change finiteEventMass
      (onePlusOneTransition (rate (leadingOnes x))
        (leadingOnesReal (n := n)) x)
      (fun y => leadingOnes y ≠ i.val) =
        rate i.val * (1 - rate i.val) ^ i.val
  rw [hlevel]
  exact onePlusOneTransition_leadingOnes_exactLevel_exitMass_eq
    (rate i.val) x i hlevel

/-- Exact survival law for remaining at a visited LeadingOnes level during
`t` consecutive transitions. No independence between successive suffix
configurations is asserted or required. -/
theorem proposed_leadingOnesAdaptive_exactLevel_survival
    {n : ℕ} (rate : ℕ → ℝ)
    (hrate : ∀ j : ℕ, j ≤ n → 0 ≤ rate j ∧ rate j ≤ 1)
    (i : Fin n) (t : ℕ) (x : BitString n)
    (hlevel : leadingOnes x = i.val) :
    finiteLevelSurvival (leadingOnesAdaptiveTransition rate)
        ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
        t x =
      (1 - rate i.val * (1 - rate i.val) ^ i.val) ^ t := by
  classical
  have hP : IsStochastic (leadingOnesAdaptiveTransition rate) :=
    proposed_leadingOnesAdaptive_transition_stochastic rate hrate
  have hexit : ∀ z : BitString n,
      z ∈ ({y : BitString n | leadingOnes y = i.val} : Set (BitString n)) →
      finiteEventMass ((leadingOnesAdaptiveTransition rate) z)
        (fun y => y ∉ ({u : BitString n | leadingOnes u = i.val} :
          Set (BitString n))) =
        rate i.val * (1 - rate i.val) ^ i.val := by
    intro z hz
    change leadingOnes z = i.val at hz
    change finiteEventMass ((leadingOnesAdaptiveTransition rate) z)
      (fun y => leadingOnes y ≠ i.val) =
        rate i.val * (1 - rate i.val) ^ i.val
    exact proposed_leadingOnesAdaptive_exactLevel_exitMass rate i z hz
  have hx : x ∈ ({y : BitString n | leadingOnes y = i.val} :
      Set (BitString n)) := hlevel
  exact finiteLevelSurvival_eq_geometric_of_exact_exit_mass
    (leadingOnesAdaptiveTransition rate)
    ({y : BitString n | leadingOnes y = i.val} : Set (BitString n))
    hP (rate i.val * (1 - rate i.val) ^ i.val) hexit t x hx

end ECRuntime
