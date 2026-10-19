import ECRuntime.LevelResidence
import Mathlib

open scoped BigOperators ENNReal

namespace ECRuntime

/-!
# Stage 26 fix 23: finite exit/Bernoulli splitting

The one-level tail theorem already shows that a level residence time is dominated in
law by a geometric waiting time.  To assemble several history-dependent residence
times while preserving an independent geometric comparison marginal, the next step is
constructive rather than purely marginal.

For a finite nonnegative transition row `w`, an exit event `event`, and a comparison
success probability `p` with

  `0 < p <= finiteEventMass w event`,

this file splits each row weight into two parts, labelled by a Boolean comparison coin.
The success part is the event-restricted row rescaled by `p / q`, where
`q = finiteEventMass w event`; the failure part is the residual row weight.

The resulting finite joint row has the properties needed for the adaptive coupling:

* every joint weight is nonnegative;
* summing the two Boolean labels recovers the original state-transition weight;
* the success label has total mass exactly `p` and the failure label `1-p` for a
  normalized row;
* success has zero mass outside the actual exit event.

Thus a fresh Bernoulli-`p` comparison success can be coupled to one real transition in
such a way that comparison success forces an actual exit, while the state marginal is
unchanged.  A later stage can iterate this row split through the history-dependent
level-residence process and identify the first comparison success with a geometric
coordinate.
-/


/-- Real-valued Bernoulli row on `Bool`, with `true` denoting success. -/
def bernoulliBoolWeight (p : ℝ) (b : Bool) : ℝ :=
  match b with
  | true => p
  | false => 1 - p

@[simp] theorem bernoulliBoolWeight_true (p : ℝ) :
    bernoulliBoolWeight p true = p := by
  rfl

@[simp] theorem bernoulliBoolWeight_false (p : ℝ) :
    bernoulliBoolWeight p false = 1 - p := by
  rfl

/-- The part of a finite weight function carried by an event. -/
noncomputable def eventRestrictedWeight
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (y : α) : ℝ :=
  ({z | event z} : Set α).indicator w y

@[simp] theorem eventRestrictedWeight_of_event
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (y : α) (hy : event y) :
    eventRestrictedWeight w event y = w y := by
  classical
  simp [eventRestrictedWeight, hy]

@[simp] theorem eventRestrictedWeight_of_not_event
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (y : α) (hy : ¬ event y) :
    eventRestrictedWeight w event y = 0 := by
  classical
  simp [eventRestrictedWeight, hy]

/-- Summing the restricted row is exactly `finiteEventMass`. -/
theorem sum_eventRestrictedWeight_eq_finiteEventMass
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) :
    (∑ y, eventRestrictedWeight w event y) = finiteEventMass w event := by
  rfl

/-- Event restriction preserves nonnegativity pointwise. -/
theorem eventRestrictedWeight_nonneg
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop)
    (hw : ∀ y, 0 ≤ w y) (y : α) :
    0 ≤ eventRestrictedWeight w event y := by
  classical
  by_cases hy : event y
  · simp [eventRestrictedWeight, hy, hw y]
  · simp [eventRestrictedWeight, hy]

/-- For a nonnegative row, event restriction never increases a point weight. -/
theorem eventRestrictedWeight_le
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop)
    (hw : ∀ y, 0 ≤ w y) (y : α) :
    eventRestrictedWeight w event y ≤ w y := by
  classical
  by_cases hy : event y
  · simp [eventRestrictedWeight, hy]
  · simp [eventRestrictedWeight, hy, hw y]

/-- Success-labelled part of the exit/Bernoulli split. -/
noncomputable def exitSplitSuccessWeight
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ) (y : α) : ℝ :=
  eventRestrictedWeight w event y *
    (p / finiteEventMass w event)

/-- Failure-labelled residual part of the exit/Bernoulli split. -/
noncomputable def exitSplitFailureWeight
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ) (y : α) : ℝ :=
  w y - exitSplitSuccessWeight w event p y

/-- Joint row weight, labelled by a Boolean comparison coin.  `true` is comparison
success. -/
noncomputable def exitBernoulliSplitWeight
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (y : α) (b : Bool) : ℝ :=
  match b with
  | true => exitSplitSuccessWeight w event p y
  | false => exitSplitFailureWeight w event p y

@[simp] theorem exitBernoulliSplitWeight_true
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ) (y : α) :
    exitBernoulliSplitWeight w event p y true =
      exitSplitSuccessWeight w event p y := by
  rfl

@[simp] theorem exitBernoulliSplitWeight_false
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ) (y : α) :
    exitBernoulliSplitWeight w event p y false =
      exitSplitFailureWeight w event p y := by
  rfl

/-- The two Boolean pieces recover the original state-transition weight pointwise. -/
theorem exitSplit_state_marginal
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ) (y : α) :
    exitBernoulliSplitWeight w event p y true +
        exitBernoulliSplitWeight w event p y false = w y := by
  simp only [exitBernoulliSplitWeight_true, exitBernoulliSplitWeight_false]
  unfold exitSplitFailureWeight
  ring

/-- Comparison success has zero weight at every state outside the actual exit event. -/
theorem exitSplit_success_eq_zero_of_not_event
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (y : α) (hy : ¬ event y) :
    exitBernoulliSplitWeight w event p y true = 0 := by
  classical
  simp [exitSplitSuccessWeight, eventRestrictedWeight, hy]

/-- The rescaling factor used by the success split lies in `[0,1]`. -/
theorem exitSplit_ratio_mem_unitInterval
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event) :
    0 ≤ p / finiteEventMass w event ∧
      p / finiteEventMass w event ≤ 1 := by
  have hqpos : 0 < finiteEventMass w event := lt_of_lt_of_le hp hpq
  constructor
  · exact div_nonneg (le_of_lt hp) (le_of_lt hqpos)
  · exact (div_le_one hqpos).2 hpq

/-- The success-labelled joint row is pointwise nonnegative. -/
theorem exitSplitSuccessWeight_nonneg
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hw : ∀ y, 0 ≤ w y)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event)
    (y : α) :
    0 ≤ exitSplitSuccessWeight w event p y := by
  unfold exitSplitSuccessWeight
  exact mul_nonneg
    (eventRestrictedWeight_nonneg w event hw y)
    (exitSplit_ratio_mem_unitInterval w event p hp hpq).1

/-- The success-labelled weight is at most the original point weight. -/
theorem exitSplitSuccessWeight_le
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hw : ∀ y, 0 ≤ w y)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event)
    (y : α) :
    exitSplitSuccessWeight w event p y ≤ w y := by
  have hr := exitSplit_ratio_mem_unitInterval w event p hp hpq
  have hrestricted_nonneg := eventRestrictedWeight_nonneg w event hw y
  have hrestricted_le := eventRestrictedWeight_le w event hw y
  unfold exitSplitSuccessWeight
  calc
    eventRestrictedWeight w event y *
        (p / finiteEventMass w event) ≤
      eventRestrictedWeight w event y * 1 :=
        mul_le_mul_of_nonneg_left hr.2 hrestricted_nonneg
    _ = eventRestrictedWeight w event y := by ring
    _ ≤ w y := hrestricted_le

/-- The failure-labelled residual joint row is pointwise nonnegative. -/
theorem exitSplitFailureWeight_nonneg
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hw : ∀ y, 0 ≤ w y)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event)
    (y : α) :
    0 ≤ exitSplitFailureWeight w event p y := by
  unfold exitSplitFailureWeight
  exact sub_nonneg.mpr
    (exitSplitSuccessWeight_le w event p hw hp hpq y)

/-- Every joint split weight is nonnegative. -/
theorem exitBernoulliSplitWeight_nonneg
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hw : ∀ y, 0 ≤ w y)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event)
    (y : α) (b : Bool) :
    0 ≤ exitBernoulliSplitWeight w event p y b := by
  cases b with
  | false =>
      exact exitSplitFailureWeight_nonneg w event p hw hp hpq y
  | true =>
      exact exitSplitSuccessWeight_nonneg w event p hw hp hpq y

/-- The success-labelled marginal has total mass exactly `p`. -/
theorem sum_exitSplitSuccessWeight
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event) :
    (∑ y, exitSplitSuccessWeight w event p y) = p := by
  have hqpos : 0 < finiteEventMass w event := lt_of_lt_of_le hp hpq
  have hqne : finiteEventMass w event ≠ 0 := ne_of_gt hqpos
  unfold exitSplitSuccessWeight
  rw [← Finset.sum_mul]
  rw [sum_eventRestrictedWeight_eq_finiteEventMass]
  field_simp [hqne]

/-- The `true` comparison-coin marginal has mass exactly `p`. -/
theorem sum_exitBernoulliSplitWeight_true
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event) :
    (∑ y, exitBernoulliSplitWeight w event p y true) = p := by
  simpa using sum_exitSplitSuccessWeight w event p hp hpq

/-- For a normalized original row, the `false` comparison-coin marginal is `1-p`. -/
theorem sum_exitBernoulliSplitWeight_false
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hsum : (∑ y, w y) = 1)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event) :
    (∑ y, exitBernoulliSplitWeight w event p y false) = 1 - p := by
  simp only [exitBernoulliSplitWeight_false]
  unfold exitSplitFailureWeight
  rw [Finset.sum_sub_distrib, hsum,
    sum_exitSplitSuccessWeight w event p hp hpq]

/-- For a normalized original row, the two labelled marginals have total mass one. -/
theorem exitBernoulliSplitWeight_total_mass
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hsum : (∑ y, w y) = 1)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event) :
    (∑ y, exitBernoulliSplitWeight w event p y true) +
        (∑ y, exitBernoulliSplitWeight w event p y false) = 1 := by
  rw [sum_exitBernoulliSplitWeight_true w event p hp hpq]
  rw [sum_exitBernoulliSplitWeight_false w event p hsum hp hpq]
  ring

/-- Summing out the state coordinate gives exactly the Bernoulli-`p` comparison row. -/
theorem sum_exitBernoulliSplitWeight_eq_bernoulliBoolWeight
    {α : Type*} [Fintype α]
    (w : α → ℝ) (event : α → Prop) (p : ℝ)
    (hsum : (∑ y, w y) = 1)
    (hp : 0 < p)
    (hpq : p ≤ finiteEventMass w event)
    (b : Bool) :
    (∑ y, exitBernoulliSplitWeight w event p y b) =
      bernoulliBoolWeight p b := by
  cases b with
  | false =>
      simpa using sum_exitBernoulliSplitWeight_false w event p hsum hp hpq
  | true =>
      simpa using sum_exitBernoulliSplitWeight_true w event p hp hpq

/-- Specialization of the split to exits from a fixed level under one transition row. -/
noncomputable def transitionLevelExitBernoulliSplitWeight
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α) (p : ℝ)
    (x y : α) (b : Bool) : ℝ :=
  exitBernoulliSplitWeight (P x) (fun z => z ∉ level) p y b

/-- The split transition row has the original Markov row as its state marginal. -/
theorem transitionLevelExitBernoulliSplit_state_marginal
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α) (p : ℝ)
    (x y : α) :
    transitionLevelExitBernoulliSplitWeight P level p x y true +
        transitionLevelExitBernoulliSplitWeight P level p x y false = P x y := by
  unfold transitionLevelExitBernoulliSplitWeight
  exact exitSplit_state_marginal (P x) (fun z => z ∉ level) p y

/-- Under a stochastic row and a positive lower exit bound, all split transition
weights are nonnegative. -/
theorem transitionLevelExitBernoulliSplit_nonneg
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    (hP : IsStochastic P) (p : ℝ) (hp : 0 < p)
    (hexit : ∀ z, z ∈ level →
      p ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) (y : α) (b : Bool) :
    0 ≤ transitionLevelExitBernoulliSplitWeight P level p x y b := by
  unfold transitionLevelExitBernoulliSplitWeight
  exact exitBernoulliSplitWeight_nonneg
    (P x) (fun z => z ∉ level) p (hP.1 x) hp (hexit x hx) y b

/-- Conditional on any current state in the level, the comparison-success marginal is
exactly `p`, independent of which state was reached from the earlier history. -/
theorem transitionLevelExitBernoulliSplit_success_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    (p : ℝ) (hp : 0 < p)
    (hexit : ∀ z, z ∈ level →
      p ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) :
    (∑ y, transitionLevelExitBernoulliSplitWeight P level p x y true) = p := by
  unfold transitionLevelExitBernoulliSplitWeight
  exact sum_exitBernoulliSplitWeight_true
    (P x) (fun z => z ∉ level) p hp (hexit x hx)

/-- Conditional on any current state in the level, the comparison-failure marginal is
exactly `1-p`. -/
theorem transitionLevelExitBernoulliSplit_failure_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    (hP : IsStochastic P) (p : ℝ) (hp : 0 < p)
    (hexit : ∀ z, z ∈ level →
      p ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) :
    (∑ y, transitionLevelExitBernoulliSplitWeight P level p x y false) = 1 - p := by
  unfold transitionLevelExitBernoulliSplitWeight
  exact sum_exitBernoulliSplitWeight_false
    (P x) (fun z => z ∉ level) p (hP.2 x) hp (hexit x hx)

/-- Each in-level split transition row is normalized across the two comparison labels. -/
theorem transitionLevelExitBernoulliSplit_total_mass
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    (hP : IsStochastic P) (p : ℝ) (hp : 0 < p)
    (hexit : ∀ z, z ∈ level →
      p ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) :
    (∑ y, transitionLevelExitBernoulliSplitWeight P level p x y true) +
        (∑ y, transitionLevelExitBernoulliSplitWeight P level p x y false) = 1 := by
  unfold transitionLevelExitBernoulliSplitWeight
  exact exitBernoulliSplitWeight_total_mass
    (P x) (fun z => z ∉ level) p (hP.2 x) hp (hexit x hx)

/-- Comparison success has no mass on transitions that remain in the level.  This is
the support statement that will imply `actual residence <= comparison waiting time`
after sequential iteration. -/
theorem transitionLevelExitBernoulliSplit_success_eq_zero_of_stay
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α) (p : ℝ)
    (x y : α) (hy : y ∈ level) :
    transitionLevelExitBernoulliSplitWeight P level p x y true = 0 := by
  unfold transitionLevelExitBernoulliSplitWeight
  apply exitSplit_success_eq_zero_of_not_event
  intro hnot
  exact hnot hy

/-- Positive comparison-success weight can occur only on a genuine level exit. -/
theorem transitionLevelExitBernoulliSplit_success_forces_exit
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α) (p : ℝ)
    (x y : α)
    (hpositive : 0 < transitionLevelExitBernoulliSplitWeight
      P level p x y true) :
    y ∉ level := by
  intro hy
  have hzero := transitionLevelExitBernoulliSplit_success_eq_zero_of_stay
    P level p x y hy
  rw [hzero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- For every current state in the level, summing out the state coordinate gives the
same Bernoulli-`p` comparison row.  This history-uniform marginal is the key input for
constructing fresh comparison randomness sequentially. -/
theorem transitionLevelExitBernoulliSplit_comparison_marginal
    {α : Type*} [Fintype α]
    (P : TransitionMatrix α) (level : Set α)
    (hP : IsStochastic P) (p : ℝ) (hp : 0 < p)
    (hexit : ∀ z, z ∈ level →
      p ≤ finiteEventMass (P z) (fun y => y ∉ level))
    (x : α) (hx : x ∈ level) (b : Bool) :
    (∑ y, transitionLevelExitBernoulliSplitWeight P level p x y b) =
      bernoulliBoolWeight p b := by
  unfold transitionLevelExitBernoulliSplitWeight
  exact sum_exitBernoulliSplitWeight_eq_bernoulliBoolWeight
    (P x) (fun z => z ∉ level) p (hP.2 x) hp (hexit x hx) b

end ECRuntime
