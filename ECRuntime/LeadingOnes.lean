import ECRuntime.Transition
import Mathlib

namespace ECRuntime

/-!
# Stage 27 fix 1: LeadingOnes foundations

Stage 26 closes the generic distributional fitness-level endpoint.  The first
independent validation problem is LeadingOnes.  This file deliberately starts with
the deterministic state semantics needed by every later probability calculation:

* a recursive definition of the LeadingOnes value on `BitString n`;
* the bound `leadingOnes x ≤ n` and exact characterization of the optimum;
* the corresponding real objective, natural-valued distance potential, and target;
* monotonicity of LeadingOnes under the repository's elitist `(1+1)`-EA selection.

The next Stage-27 slice can use these facts to characterize the exact level-exit
mutation event and sum its mask mass to `p * (1-p)^i`.
-/

/-- Remove coordinate zero from a nonempty bit string. -/
def bitStringTail {n : ℕ} (x : BitString (n + 1)) : BitString n :=
  fun i => x i.succ

/-- Number of consecutive one-bits from coordinate zero. -/
def leadingOnes : {n : ℕ} → BitString n → ℕ
  | 0, _ => 0
  | n + 1, x =>
      if x 0 = true then
        1 + leadingOnes (bitStringTail (n := n) x)
      else
        0

@[simp] theorem leadingOnes_zero (x : BitString 0) :
    leadingOnes x = 0 := by
  rfl

@[simp] theorem leadingOnes_succ {n : ℕ} (x : BitString (n + 1)) :
    leadingOnes x =
      if x 0 = true then 1 + leadingOnes (bitStringTail x) else 0 := by
  rfl

@[simp] theorem bitStringTail_allOnes (n : ℕ) :
    bitStringTail (allOnes (n + 1)) = allOnes n := by
  rfl

@[simp] theorem leadingOnes_allOnes (n : ℕ) :
    leadingOnes (allOnes n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [leadingOnes_succ, allOnes, ih, Nat.add_comm]

@[simp] theorem leadingOnes_allZeros (n : ℕ) :
    leadingOnes (allZeros n) = 0 := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      simp [leadingOnes_succ, allZeros]

/-- LeadingOnes never exceeds the bit-string dimension. -/
theorem leadingOnes_le :
    ∀ {n : ℕ} (x : BitString n), leadingOnes x ≤ n := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      rw [leadingOnes_succ]
      by_cases h0 : x 0 = true
      · rw [if_pos h0]
        have htail := ih (bitStringTail x)
        omega
      · rw [if_neg h0]
        omega

/-- Every coordinate strictly inside the LeadingOnes prefix is one. -/
theorem bit_eq_true_of_lt_leadingOnes :
    ∀ {n : ℕ} (x : BitString n) (i : Fin n),
      i.val < leadingOnes x → x i = true := by
  intro n
  induction n with
  | zero =>
      intro x i
      exact Fin.elim0 i
  | succ n ih =>
      intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hi
        have h0 : x 0 = true := by
          by_contra hnot
          have hz : leadingOnes x = 0 := by
            rw [leadingOnes_succ, if_neg hnot]
          omega
        exact h0
      · intro jhi
        have h0 : x 0 = true := by
          by_contra hnot
          have hz : leadingOnes x = 0 := by
            rw [leadingOnes_succ, if_neg hnot]
          omega
        rw [leadingOnes_succ, if_pos h0] at jhi
        apply ih (bitStringTail x) j
        change j.val + 1 < 1 + leadingOnes (bitStringTail x) at jhi
        omega

/-- Achieving value `n` is equivalent to being the all-one string. -/
theorem leadingOnes_eq_dim_iff :
    ∀ {n : ℕ} (x : BitString n),
      leadingOnes x = n ↔ x = allOnes n := by
  intro n
  induction n with
  | zero =>
      intro x
      constructor
      · intro _
        funext i
        exact Fin.elim0 i
      · intro hx
        subst x
        exact leadingOnes_allOnes 0
  | succ n ih =>
      intro x
      constructor
      · intro hdim
        have h0 : x 0 = true := by
          by_contra hnot
          have hz : leadingOnes x = 0 := by
            rw [leadingOnes_succ, if_neg hnot]
          rw [hz] at hdim
          omega
        have htail : leadingOnes (bitStringTail x) = n := by
          rw [leadingOnes_succ, if_pos h0] at hdim
          omega
        have htailOnes : bitStringTail x = allOnes n :=
          (ih (bitStringTail x)).1 htail
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa [allOnes] using h0
        · have hj := congrFun htailOnes j
          simpa [bitStringTail, allOnes] using hj
      · intro hx
        subst x
        exact leadingOnes_allOnes (n + 1)

/-- LeadingOnes as a real-valued maximization objective. -/
def leadingOnesReal {n : ℕ} (x : BitString n) : ℝ :=
  (leadingOnes x : ℝ)

/-- Distance from the optimum measured in missing LeadingOnes prefix length. -/
def leadingOnesPotential {n : ℕ} (x : BitString n) : ℕ :=
  n - leadingOnes x

/-- Canonical optimum target for LeadingOnes. -/
def leadingOnesTarget (n : ℕ) : Set (BitString n) :=
  {x | x = allOnes n}

/-- The LeadingOnes distance potential has zero level exactly at the optimum. -/
theorem leadingOnesPotential_isTarget (n : ℕ) :
    IsTargetPotential (leadingOnesPotential (n := n)) (leadingOnesTarget n) := by
  intro x
  constructor
  · intro hx
    change x = allOnes n at hx
    subst x
    simp [leadingOnesPotential]
  · intro hz
    change n - leadingOnes x = 0 at hz
    change x = allOnes n
    have hbound := leadingOnes_le x
    have heq : leadingOnes x = n := by
      omega
    exact (leadingOnes_eq_dim_iff x).1 heq

/-- Elitist LeadingOnes selection never decreases the LeadingOnes value. -/
theorem leadingOnes_selectedAfterMask_mono
    {n : ℕ} (x : BitString n) (mask : MutationMask n) :
    leadingOnes x ≤
      leadingOnes (selectedAfterMask (leadingOnesReal (n := n)) x mask) := by
  unfold selectedAfterMask elitistSelect
  by_cases hacc :
      leadingOnesReal x ≤ leadingOnesReal (mutateWithMask x mask)
  · rw [if_pos hacc]
    unfold leadingOnesReal at hacc
    exact_mod_cast hacc
  · rw [if_neg hacc]

/-- Consequently the natural LeadingOnes distance potential never increases after selection. -/
theorem leadingOnesPotential_selectedAfterMask_le
    {n : ℕ} (x : BitString n) (mask : MutationMask n) :
    leadingOnesPotential
        (selectedAfterMask (leadingOnesReal (n := n)) x mask) ≤
      leadingOnesPotential x := by
  have hmono := leadingOnes_selectedAfterMask_mono x mask
  unfold leadingOnesPotential
  omega

end ECRuntime
