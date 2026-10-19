import ECRuntime.FiniteCoupledTrajectory
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 26 fix 26: multi-level Bernoulli-vector coupled prefixes

Stage 26 fix 25 proves a generic finite-prefix theorem for labelled transition rows and
specializes it to one fixed level.  The final fitness-level coupling, however, must change
which level is active as the real trajectory improves.  This file inserts the missing
finite-dimensional interface before that adaptive recursion.

At every real transition we emit an entire Boolean vector indexed by the positive levels.
Exactly one coordinate -- the coordinate of the current positive potential value -- is
coupled to the real transition by the verified exit/Bernoulli split.  Every other coordinate
is sampled independently with its prescribed Bernoulli weight.  At potential zero all
coordinates are independent of the real transition.

The key point is that the complete Boolean vector has the same product-Bernoulli marginal
at every current state.  Thus changing the active coordinate with the history does not alter
the comparison marginal.  Applying the generic fix-25 finite labelled-path theorem then
shows that finite comparison-vector prefixes are i.i.d. while the state-path marginal remains
exactly the original Markov trajectory law.

This is still a finite-dimensional statement.  A later slice will turn the coordinatewise
Bernoulli streams into first-success/geometric coordinates and prove the almost-everywhere
residence-time inequalities required by `CouplingDomination.lean`.
-/

/-- Product Bernoulli weight of one Boolean vector, with one parameter per positive level. -/
def bernoulliLevelVectorWeight {m : ℕ}
    (p : Fin m → ℝ) (bits : Fin m → Bool) : ℝ :=
  ∏ i : Fin m, bernoulliBoolWeight (p i) (bits i)

/-- The product Bernoulli vector weights have total mass one. -/
theorem sum_bernoulliLevelVectorWeight {m : ℕ} (p : Fin m → ℝ) :
    (∑ bits : Fin m → Bool, bernoulliLevelVectorWeight p bits) = 1 := by
  classical
  calc
    (∑ bits : Fin m → Bool, bernoulliLevelVectorWeight p bits) =
        ∏ i : Fin m, ∑ b : Bool, bernoulliBoolWeight (p i) b := by
      symm
      simpa [bernoulliLevelVectorWeight] using
        (Fintype.prod_sum (fun i : Fin m => fun b : Bool => bernoulliBoolWeight (p i) b))
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i _hi
      exact sum_bernoulliBoolWeight (p i)

/-- Exact positive potential level represented by coordinate `i : Fin m`. -/
def exactPositivePotentialLevel {α : Type*} {m : ℕ}
    (V : α → ℕ) (i : Fin m) : Set α :=
  {x | V x = i.1 + 1}

@[simp] theorem mem_exactPositivePotentialLevel
    {α : Type*} {m : ℕ} (V : α → ℕ) (i : Fin m) (x : α) :
    x ∈ exactPositivePotentialLevel V i ↔ V x = i.1 + 1 := by
  rfl

/-- The unique positive-level coordinate selected by a nonzero bounded potential value. -/
def activePositivePotentialLevelIndex
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (x : α) (hx : V x ≠ 0) : Fin m :=
  ⟨V x - 1, by
    have hxpos : 0 < V x := Nat.pos_of_ne_zero hx
    have hxm := hbound x
    omega⟩

/-- The selected coordinate represents exactly the current positive potential value. -/
theorem activePositivePotentialLevelIndex_value
    {α : Type*} {m : ℕ}
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (x : α) (hx : V x ≠ 0) :
    V x = (activePositivePotentialLevelIndex V hbound x hx).1 + 1 := by
  have hxpos : 0 < V x := Nat.pos_of_ne_zero hx
  unfold activePositivePotentialLevelIndex
  dsimp
  omega

/-- Product of all Bernoulli vector coordinates except `i`. -/
def bernoulliLevelVectorComplementWeight {m : ℕ}
    (p : Fin m → ℝ) (i : Fin m) (bits : Fin m → Bool) : ℝ :=
  ∏ j ∈ ({i}ᶜ : Finset (Fin m)), bernoulliBoolWeight (p j) (bits j)

/-- Split the product Bernoulli vector into coordinate `i` and its complement. -/
theorem bernoulliLevelVectorWeight_eq_active_mul_complement
    {m : ℕ} (p : Fin m → ℝ) (i : Fin m) (bits : Fin m → Bool) :
    bernoulliLevelVectorWeight p bits =
      bernoulliBoolWeight (p i) (bits i) *
        bernoulliLevelVectorComplementWeight p i bits := by
  classical
  unfold bernoulliLevelVectorWeight bernoulliLevelVectorComplementWeight
  exact Fintype.prod_eq_mul_prod_compl i
    (fun j : Fin m => bernoulliBoolWeight (p j) (bits j))

/-- One real transition coupled to a full Bernoulli vector when coordinate `i` is active.
The active coordinate uses the verified fixed-level split; every other coordinate is an
independent Bernoulli factor. -/
noncomputable def levelBernoulliVectorCoupledStepWeight
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool) : ℝ :=
  ∏ j : Fin m,
    if j = i then
      levelBernoulliCoupledStepWeight P level (p i) x y (bits j)
    else
      bernoulliBoolWeight (p j) (bits j)

/-- The active-vector step factors into the fixed-level coupled coordinate and the
independent complement coordinates. -/
theorem levelBernoulliVectorCoupledStepWeight_eq_active_mul_complement
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) (bits : Fin m → Bool) :
    levelBernoulliVectorCoupledStepWeight P level p i x y bits =
      levelBernoulliCoupledStepWeight P level (p i) x y (bits i) *
        bernoulliLevelVectorComplementWeight p i bits := by
  classical
  unfold levelBernoulliVectorCoupledStepWeight bernoulliLevelVectorComplementWeight
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [if_pos]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    simpa using hj
  simp [hji]

/-- Summing out the whole Boolean vector recovers the original transition row, even
though one coordinate has been coupled to the level exit. -/
theorem levelBernoulliVectorCoupledStepWeight_state_marginal
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (p : Fin m → ℝ) (i : Fin m)
    (x y : α) :
    (∑ bits : Fin m → Bool,
      levelBernoulliVectorCoupledStepWeight P level p i x y bits) = P x y := by
  classical
  let f : (j : Fin m) → Bool → ℝ := fun j b =>
    if j = i then
      levelBernoulliCoupledStepWeight P level (p i) x y b
    else
      bernoulliBoolWeight (p j) b
  have hprodSum :
      (∑ bits : Fin m → Bool, ∏ j : Fin m, f j (bits j)) =
        ∏ j : Fin m, ∑ b : Bool, f j b := by
    symm
    exact Fintype.prod_sum f
  have hother : ∀ j : Fin m, j ≠ i → (∑ b : Bool, f j b) = 1 := by
    intro j hji
    simp [f, hji]
  have hactive : (∑ b : Bool, f i b) = P x y := by
    simp only [f, if_pos]
    exact levelBernoulliCoupledStepWeight_state_marginal P level (p i) x y
  calc
    (∑ bits : Fin m → Bool,
        levelBernoulliVectorCoupledStepWeight P level p i x y bits) =
        ∑ bits : Fin m → Bool, ∏ j : Fin m, f j (bits j) := by
      rfl
    _ = ∏ j : Fin m, ∑ b : Bool, f j b := hprodSum
    _ = ∑ b : Bool, f i b := by
      apply Finset.prod_eq_single i
      · intro j _hj hji
        exact hother j hji
      · intro hi
        simp at hi
    _ = P x y := hactive

/-- Summing out the next state gives exactly the product Bernoulli vector marginal.
The active coordinate uses the substantive exit split; the complement factors are
independent of the next state. -/
theorem levelBernoulliVectorCoupledStepWeight_label_marginal
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (level : Set α)
    (hP : IsStochastic P)
    (p : Fin m → ℝ) (i : Fin m)
    (hp : 0 < p i)
    (hexit : ∀ z, z ∈ level →
      p i ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (bits : Fin m → Bool) :
    (∑ y : α, levelBernoulliVectorCoupledStepWeight P level p i x y bits) =
      bernoulliLevelVectorWeight p bits := by
  classical
  simp_rw [levelBernoulliVectorCoupledStepWeight_eq_active_mul_complement]
  rw [← Finset.sum_mul]
  rw [levelBernoulliCoupledStepWeight_label_marginal
    P level hP (p i) hp hexit x (bits i)]
  rw [bernoulliLevelVectorWeight_eq_active_mul_complement]

/-- Global one-step coupling selected by the current bounded potential value.  At positive
potential the corresponding exact level coordinate is active.  At potential zero the real
transition is tensored with a fully independent Bernoulli vector. -/
noncomputable def multiLevelBernoulliCoupledStepWeight
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ)
    (x y : α) (bits : Fin m → Bool) : ℝ := by
  classical
  by_cases hx : V x = 0
  · exact P x y * bernoulliLevelVectorWeight p bits
  · let i := activePositivePotentialLevelIndex V hbound x hx
    exact levelBernoulliVectorCoupledStepWeight
      P (exactPositivePotentialLevel V i) p i x y bits

/-- The global adaptive one-step coupling preserves the original state-transition marginal. -/
theorem multiLevelBernoulliCoupledStepWeight_state_marginal
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ)
    (x y : α) :
    (∑ bits : Fin m → Bool,
      multiLevelBernoulliCoupledStepWeight P V hbound p x y bits) = P x y := by
  classical
  by_cases hx : V x = 0
  · calc
      (∑ bits : Fin m → Bool,
          multiLevelBernoulliCoupledStepWeight P V hbound p x y bits) =
          ∑ bits : Fin m → Bool,
            P x y * bernoulliLevelVectorWeight p bits := by
        apply Finset.sum_congr rfl
        intro bits _hbits
        simp [multiLevelBernoulliCoupledStepWeight, hx]
      _ = P x y * (∑ bits : Fin m → Bool, bernoulliLevelVectorWeight p bits) := by
        rw [Finset.mul_sum]
      _ = P x y := by rw [sum_bernoulliLevelVectorWeight]; ring
  · let i : Fin m := activePositivePotentialLevelIndex V hbound x hx
    calc
      (∑ bits : Fin m → Bool,
          multiLevelBernoulliCoupledStepWeight P V hbound p x y bits) =
          ∑ bits : Fin m → Bool,
            levelBernoulliVectorCoupledStepWeight
              P (exactPositivePotentialLevel V i) p i x y bits := by
        apply Finset.sum_congr rfl
        intro bits _hbits
        simp [multiLevelBernoulliCoupledStepWeight, hx, i]
      _ = P x y :=
        levelBernoulliVectorCoupledStepWeight_state_marginal
          P (exactPositivePotentialLevel V i) p i x y

/-- A uniform lower exit bound for every exact positive potential level. -/
def HasUniformExactLevelExitBounds
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (V : α → ℕ)
    (p : Fin m → ℝ) : Prop :=
  ∀ i : Fin m, ∀ z : α, z ∈ exactPositivePotentialLevel V i →
    p i ≤ finiteEventMass (P z)
      (fun y => y ∉ exactPositivePotentialLevel V i)

/-- Despite the history-dependent active coordinate, summing out the next state always
produces the same product Bernoulli vector law. -/
theorem multiLevelBernoulliCoupledStepWeight_label_marginal
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (x : α) (bits : Fin m → Bool) :
    (∑ y : α,
      multiLevelBernoulliCoupledStepWeight P V hbound p x y bits) =
      bernoulliLevelVectorWeight p bits := by
  classical
  by_cases hx : V x = 0
  · calc
      (∑ y : α,
          multiLevelBernoulliCoupledStepWeight P V hbound p x y bits) =
          ∑ y : α, P x y * bernoulliLevelVectorWeight p bits := by
        apply Finset.sum_congr rfl
        intro y _hy
        simp [multiLevelBernoulliCoupledStepWeight, hx]
      _ = (∑ y : α, P x y) * bernoulliLevelVectorWeight p bits := by
        rw [Finset.sum_mul]
      _ = bernoulliLevelVectorWeight p bits := by rw [hP.2 x]; ring
  · let i : Fin m := activePositivePotentialLevelIndex V hbound x hx
    have hexit_i : ∀ z, z ∈ exactPositivePotentialLevel V i →
        p i ≤ finiteEventMass (P z)
          (fun y => y ∉ exactPositivePotentialLevel V i) := by
      intro z hz
      exact hexit i z hz
    calc
      (∑ y : α,
          multiLevelBernoulliCoupledStepWeight P V hbound p x y bits) =
          ∑ y : α,
            levelBernoulliVectorCoupledStepWeight
              P (exactPositivePotentialLevel V i) p i x y bits := by
        apply Finset.sum_congr rfl
        intro y _hy
        simp [multiLevelBernoulliCoupledStepWeight, hx, i]
      _ = bernoulliLevelVectorWeight p bits :=
        levelBernoulliVectorCoupledStepWeight_label_marginal
          P (exactPositivePotentialLevel V i) hP p i (hp i) hexit_i x bits

/-- Finite coupled state/vector-label path weight for the adaptive potential-selected step. -/
noncomputable def finiteMultiLevelBernoulliCoupledWeight
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ)
    (t : ℕ) (x : α)
    (path : FiniteTrajectory (α × (Fin m → Bool)) t) : ℝ :=
  finiteLabeledTrajectoryWeight
    (multiLevelBernoulliCoupledStepWeight P V hbound p) t x path

/-- Exact finite state-path marginal of the adaptive multi-level coupled law. -/
theorem finiteMultiLevelBernoulliCoupledWeight_state_marginal
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ)
    (t : ℕ) (x : α) (states : FiniteTrajectory α t) :
    (∑ labels : FiniteTrajectory (Fin m → Bool) t,
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x (zipFiniteTrajectories states labels)) =
      finiteTrajectoryWeight P t x states := by
  unfold finiteMultiLevelBernoulliCoupledWeight
  exact finiteLabeledTrajectoryWeight_state_marginal
    (multiLevelBernoulliCoupledStepWeight P V hbound p) P
    (multiLevelBernoulliCoupledStepWeight_state_marginal P V hbound p)
    t x states

/-- Exact finite i.i.d. product-Bernoulli vector-label marginal.  This is the finite
independence statement needed before extracting one geometric coordinate per level. -/
theorem finiteMultiLevelBernoulliCoupledWeight_label_marginal
    {α : Type*} [Fintype α] {m : ℕ}
    (P : TransitionMatrix α) (hP : IsStochastic P)
    (V : α → ℕ) (hbound : ∀ x, V x ≤ m)
    (p : Fin m → ℝ) (hp : ∀ i, 0 < p i)
    (hexit : HasUniformExactLevelExitBounds P V p)
    (t : ℕ) (x : α)
    (labels : FiniteTrajectory (Fin m → Bool) t) :
    (∑ states : FiniteTrajectory α t,
      finiteMultiLevelBernoulliCoupledWeight
        P V hbound p t x (zipFiniteTrajectories states labels)) =
      finiteIIDLabelWeight (bernoulliLevelVectorWeight p) t labels := by
  unfold finiteMultiLevelBernoulliCoupledWeight
  exact finiteLabeledTrajectoryWeight_label_marginal
    (multiLevelBernoulliCoupledStepWeight P V hbound p)
    (bernoulliLevelVectorWeight p)
    (multiLevelBernoulliCoupledStepWeight_label_marginal
      P hP V hbound p hp hexit)
    t x labels

end ECRuntime
