import ECRuntime.BitString
import Mathlib

open scoped BigOperators

namespace ECRuntime

/-- Real-valued numerical value of a bit. -/
def bitValueReal (b : Bool) : ℝ :=
  if b = true then 1 else 0

@[simp] theorem bitValueReal_false : bitValueReal false = 0 := by
  simp [bitValueReal]

@[simp] theorem bitValueReal_true : bitValueReal true = 1 := by
  simp [bitValueReal]

/-- A linear pseudo-Boolean objective, interpreted as a maximization objective. -/
def linearFitness {n : ℕ} (w : Fin n → ℝ) (x : BitString n) : ℝ :=
  ∑ i, w i * bitValueReal (x i)

/-- OneMax, interpreted as a maximization objective. -/
def oneMax {n : ℕ} (x : BitString n) : ℕ :=
  oneCount x

@[simp] theorem oneMax_allOnes (n : ℕ) : oneMax (allOnes n) = n := by
  simp [oneMax]

/-- Positive linear functions are maximized by the all-one search point. -/
theorem linearFitness_le_allOnes
    {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (x : BitString n) :
    linearFitness w x ≤ linearFitness w (allOnes n) := by
  unfold linearFitness
  apply Finset.sum_le_sum
  intro i hi
  by_cases hxi : x i = true
  · simp [bitValueReal, hxi, allOnes]
  · simp [bitValueReal, hxi, allOnes, hw i]

end ECRuntime
