import ECRuntime.LeadingOnesSymmetry
import ECRuntime.FiniteTrajectory
import Mathlib

namespace ECRuntime

/-!
# Stage 27 fix 4: finite first-crossing symmetry for LeadingOnes

Stage 27 fix 3 fix 1 compiler-verifies the state-level coordinate-flip involution and
its conjugacy for the `(1+1)`-EA LeadingOnes transition matrix below a fixed boundary
coordinate `i`.  This file lifts that symmetry to explicit finite trajectories.

For a finite path of `t` transitions, `leadingOnesPreCrossing i t x path` means that
every state which serves as a transition parent is still strictly below level `i`.
The terminal state may already lie on or above the boundary.  Toggling coordinate `i`
in the initial state and every stored trajectory state

* preserves the pre-crossing condition;
* preserves the complete finite trajectory weight;
* is an involution on finite histories; and
* exchanges first crossing at exact level `i` with first crossing strictly above `i`.

The next slice can sum this weight-preserving involution over all uniformly weighted
initial states and finite first-crossing histories.  That finite mass equality is the
core step toward the classical `1/2` visit probability.
-/

/-- Toggle coordinate `i` in every state stored by a finite trajectory. -/
def leadingOnesFiniteTrajectoryFlip {n t : ℕ}
    (i : Fin n) (path : FiniteTrajectory (BitString n) t) :
    FiniteTrajectory (BitString n) t :=
  fun k => leadingOnesCoordinateFlip i (path k)

@[simp] theorem leadingOnesFiniteTrajectoryFlip_apply
    {n t : ℕ} (i : Fin n) (path : FiniteTrajectory (BitString n) t) (k : Fin t) :
    leadingOnesFiniteTrajectoryFlip i path k =
      leadingOnesCoordinateFlip i (path k) := by
  rfl

@[simp] theorem leadingOnesFiniteTrajectoryFlip_involutive
    {n t : ℕ} (i : Fin n) (path : FiniteTrajectory (BitString n) t) :
    leadingOnesFiniteTrajectoryFlip i (leadingOnesFiniteTrajectoryFlip i path) = path := by
  funext k
  simp [leadingOnesFiniteTrajectoryFlip]

@[simp] theorem leadingOnesFiniteTrajectoryFlip_tail
    {n t : ℕ} (i : Fin n) (path : FiniteTrajectory (BitString n) (t + 1)) :
    Fin.tail (leadingOnesFiniteTrajectoryFlip i path) =
      leadingOnesFiniteTrajectoryFlip i (Fin.tail path) := by
  funext k
  rfl

/-- Being strictly below the boundary is itself invariant under the coordinate flip. -/
theorem leadingOnes_coordinateFlip_lt_iff
    {n : ℕ} (x : BitString n) (i : Fin n) :
    leadingOnes (leadingOnesCoordinateFlip i x) < i.val ↔
      leadingOnes x < i.val := by
  constructor
  · intro hflip
    have hback :=
      leadingOnes_coordinateFlip_eq_of_lt
        (leadingOnesCoordinateFlip i x) i hflip
    have heq :
        leadingOnes x = leadingOnes (leadingOnesCoordinateFlip i x) := by
      simpa using hback
    rw [heq]
    exact hflip
  · intro hx
    rw [leadingOnes_coordinateFlip_eq_of_lt x i hx]
    exact hx

/-- Every state used as a transition parent remains below boundary `i`.

For horizon zero there is no transition parent.  At horizon `t+1`, the supplied
initial state is below `i`, and the same condition holds recursively from the first
stored state onward.  Thus the terminal state is unconstrained and may be the first
state on or above the boundary. -/
def leadingOnesPreCrossing {n : ℕ} (i : Fin n) :
    (t : ℕ) → BitString n → FiniteTrajectory (BitString n) t → Prop
  | 0, _x, _path => True
  | t + 1, x, path =>
      leadingOnes x < i.val ∧
        leadingOnesPreCrossing i t (path 0) (Fin.tail path)

/-- The pre-crossing predicate is preserved exactly by flipping coordinate `i` in the
whole finite history. -/
theorem leadingOnesPreCrossing_flip_iff
    {n : ℕ} (i : Fin n) :
    ∀ (t : ℕ) (x : BitString n) (path : FiniteTrajectory (BitString n) t),
      leadingOnesPreCrossing i t
          (leadingOnesCoordinateFlip i x)
          (leadingOnesFiniteTrajectoryFlip i path) ↔
        leadingOnesPreCrossing i t x path := by
  intro t
  induction t with
  | zero =>
      intro x path
      simp [leadingOnesPreCrossing]
  | succ t ih =>
      intro x path
      constructor
      · intro h
        rcases h with ⟨hx, htail⟩
        have hx' := (leadingOnes_coordinateFlip_lt_iff x i).1 hx
        have htail' :
            leadingOnesPreCrossing i t
              (leadingOnesCoordinateFlip i (path 0))
              (leadingOnesFiniteTrajectoryFlip i (Fin.tail path)) := by
          simpa using htail
        exact ⟨hx', (ih (path 0) (Fin.tail path)).1 htail'⟩
      · intro h
        rcases h with ⟨hx, htail⟩
        have hx' := (leadingOnes_coordinateFlip_lt_iff x i).2 hx
        have htail' := (ih (path 0) (Fin.tail path)).2 htail
        constructor
        · exact hx'
        · simpa using htail'

/-- Finite trajectory weights are preserved by the coordinate-flip involution up to
(and including) the first transition which reaches or crosses boundary `i`. -/
theorem finiteTrajectoryWeight_leadingOnesCoordinateFlip
    {n : ℕ} (p : ℝ) (i : Fin n) :
    ∀ (t : ℕ) (x : BitString n) (path : FiniteTrajectory (BitString n) t),
      leadingOnesPreCrossing i t x path →
        finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t
            (leadingOnesCoordinateFlip i x)
            (leadingOnesFiniteTrajectoryFlip i path) =
          finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t x path := by
  intro t
  induction t with
  | zero =>
      intro x path _h
      rfl
  | succ t ih =>
      intro x path hpre
      rcases hpre with ⟨hx, htail⟩
      change
        onePlusOneTransition p leadingOnesReal
              (leadingOnesCoordinateFlip i x)
              (leadingOnesCoordinateFlip i (path 0)) *
            finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t
              (leadingOnesCoordinateFlip i (path 0))
              (Fin.tail (leadingOnesFiniteTrajectoryFlip i path)) =
          onePlusOneTransition p leadingOnesReal x (path 0) *
            finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t
              (path 0) (Fin.tail path)
      rw [onePlusOneTransition_leadingOnes_coordinateFlip p x (path 0) i hx]
      rw [leadingOnesFiniteTrajectoryFlip_tail]
      rw [ih (path 0) (Fin.tail path) htail]

/-- Last state of the finite history consisting of an initial state and `t` stored
post-transition states. -/
def finiteTrajectoryTerminal {α : Type*} :
    (t : ℕ) → α → FiniteTrajectory α t → α
  | 0, x, _path => x
  | t + 1, _x, path => path ⟨t, Nat.lt_succ_self t⟩

@[simp] theorem finiteTrajectoryTerminal_leadingOnesCoordinateFlip
    {n t : ℕ} (i : Fin n) (x : BitString n)
    (path : FiniteTrajectory (BitString n) t) :
    finiteTrajectoryTerminal t
        (leadingOnesCoordinateFlip i x)
        (leadingOnesFiniteTrajectoryFlip i path) =
      leadingOnesCoordinateFlip i (finiteTrajectoryTerminal t x path) := by
  cases t <;> rfl

/-- A finite history packages the initial state with its next `t` states. -/
abbrev LeadingOnesFiniteHistory (n t : ℕ) :=
  BitString n × FiniteTrajectory (BitString n) t

/-- Coordinate flip on a complete finite history. -/
def leadingOnesFiniteHistoryFlip {n t : ℕ}
    (i : Fin n) (h : LeadingOnesFiniteHistory n t) :
    LeadingOnesFiniteHistory n t :=
  (leadingOnesCoordinateFlip i h.1, leadingOnesFiniteTrajectoryFlip i h.2)

@[simp] theorem leadingOnesFiniteHistoryFlip_involutive
    {n t : ℕ} (i : Fin n) (h : LeadingOnesFiniteHistory n t) :
    leadingOnesFiniteHistoryFlip i (leadingOnesFiniteHistoryFlip i h) = h := by
  rcases h with ⟨x, path⟩
  simp [leadingOnesFiniteHistoryFlip]

/-- History flip is injective because it is an involution. -/
theorem leadingOnesFiniteHistoryFlip_injective
    {n t : ℕ} (i : Fin n) :
    Function.Injective (leadingOnesFiniteHistoryFlip (t := t) i) := by
  intro h₁ h₂ heq
  have h := congrArg (leadingOnesFiniteHistoryFlip (t := t) i) heq
  simpa using h

/-- The whole-history version of the pre-crossing predicate. -/
def leadingOnesHistoryPreCrossing {n t : ℕ}
    (i : Fin n) (h : LeadingOnesFiniteHistory n t) : Prop :=
  leadingOnesPreCrossing i t h.1 h.2

/-- A first crossing which lands exactly at level `i`. -/
def leadingOnesFirstCrossingExact {n t : ℕ}
    (i : Fin n) (h : LeadingOnesFiniteHistory n t) : Prop :=
  leadingOnesHistoryPreCrossing i h ∧
    leadingOnes (finiteTrajectoryTerminal t h.1 h.2) = i.val

/-- A first crossing which skips strictly above level `i`. -/
def leadingOnesFirstCrossingSkip {n t : ℕ}
    (i : Fin n) (h : LeadingOnesFiniteHistory n t) : Prop :=
  leadingOnesHistoryPreCrossing i h ∧
    i.val < leadingOnes (finiteTrajectoryTerminal t h.1 h.2)

/-- Whole-history pre-crossing is invariant under the history involution. -/
theorem leadingOnesHistoryPreCrossing_flip_iff
    {n t : ℕ} (i : Fin n) (h : LeadingOnesFiniteHistory n t) :
    leadingOnesHistoryPreCrossing i (leadingOnesFiniteHistoryFlip i h) ↔
      leadingOnesHistoryPreCrossing i h := by
  rcases h with ⟨x, path⟩
  change
    leadingOnesPreCrossing i t
        (leadingOnesCoordinateFlip i x)
        (leadingOnesFiniteTrajectoryFlip i path) ↔
      leadingOnesPreCrossing i t x path
  exact leadingOnesPreCrossing_flip_iff i t x path

/-- History flip exchanges exact first crossing with strict skip first crossing. -/
theorem leadingOnesFirstCrossingExact_flip_iff_skip
    {n t : ℕ} (i : Fin n) (h : LeadingOnesFiniteHistory n t) :
    leadingOnesFirstCrossingExact i (leadingOnesFiniteHistoryFlip i h) ↔
      leadingOnesFirstCrossingSkip i h := by
  rcases h with ⟨x, path⟩
  change
    (leadingOnesPreCrossing i t
        (leadingOnesCoordinateFlip i x)
        (leadingOnesFiniteTrajectoryFlip i path) ∧
      leadingOnes
          (finiteTrajectoryTerminal t
            (leadingOnesCoordinateFlip i x)
            (leadingOnesFiniteTrajectoryFlip i path)) = i.val) ↔
    (leadingOnesPreCrossing i t x path ∧
      i.val < leadingOnes (finiteTrajectoryTerminal t x path))
  constructor
  · intro hexact
    rcases hexact with ⟨hpreFlip, htermFlip⟩
    have hpre : leadingOnesPreCrossing i t x path :=
      (leadingOnesPreCrossing_flip_iff i t x path).1 hpreFlip
    have htermFlip' :
        leadingOnes
            (leadingOnesCoordinateFlip i (finiteTrajectoryTerminal t x path)) = i.val := by
      simpa using htermFlip
    have hstrict :=
      leadingOnes_coordinateFlip_gt_of_eq
        (leadingOnesCoordinateFlip i (finiteTrajectoryTerminal t x path)) i htermFlip'
    have hskip : i.val < leadingOnes (finiteTrajectoryTerminal t x path) := by
      simpa using hstrict
    exact ⟨hpre, hskip⟩
  · intro hskip
    rcases hskip with ⟨hpre, hterm⟩
    have hpreFlip :
        leadingOnesPreCrossing i t
          (leadingOnesCoordinateFlip i x)
          (leadingOnesFiniteTrajectoryFlip i path) :=
      (leadingOnesPreCrossing_flip_iff i t x path).2 hpre
    have htermExact :=
      leadingOnes_coordinateFlip_eq_of_gt (finiteTrajectoryTerminal t x path) i hterm
    constructor
    · exact hpreFlip
    · simpa using htermExact

/-- The dual exchange: a strict skip after flipping is exact entry before flipping. -/
theorem leadingOnesFirstCrossingSkip_flip_iff_exact
    {n t : ℕ} (i : Fin n) (h : LeadingOnesFiniteHistory n t) :
    leadingOnesFirstCrossingSkip i (leadingOnesFiniteHistoryFlip i h) ↔
      leadingOnesFirstCrossingExact i h := by
  rcases h with ⟨x, path⟩
  change
    (leadingOnesPreCrossing i t
        (leadingOnesCoordinateFlip i x)
        (leadingOnesFiniteTrajectoryFlip i path) ∧
      i.val <
        leadingOnes
          (finiteTrajectoryTerminal t
            (leadingOnesCoordinateFlip i x)
            (leadingOnesFiniteTrajectoryFlip i path))) ↔
    (leadingOnesPreCrossing i t x path ∧
      leadingOnes (finiteTrajectoryTerminal t x path) = i.val)
  constructor
  · intro hskip
    rcases hskip with ⟨hpreFlip, htermFlip⟩
    have hpre : leadingOnesPreCrossing i t x path :=
      (leadingOnesPreCrossing_flip_iff i t x path).1 hpreFlip
    have htermFlip' :
        i.val <
          leadingOnes
            (leadingOnesCoordinateFlip i (finiteTrajectoryTerminal t x path)) := by
      simpa using htermFlip
    have htermExact :=
      leadingOnes_coordinateFlip_eq_of_gt
        (leadingOnesCoordinateFlip i (finiteTrajectoryTerminal t x path)) i htermFlip'
    have hexact : leadingOnes (finiteTrajectoryTerminal t x path) = i.val := by
      simpa using htermExact
    exact ⟨hpre, hexact⟩
  · intro hexact
    rcases hexact with ⟨hpre, hterm⟩
    have hpreFlip :
        leadingOnesPreCrossing i t
          (leadingOnesCoordinateFlip i x)
          (leadingOnesFiniteTrajectoryFlip i path) :=
      (leadingOnesPreCrossing_flip_iff i t x path).2 hpre
    have htermSkip :=
      leadingOnes_coordinateFlip_gt_of_eq (finiteTrajectoryTerminal t x path) i hterm
    exact ⟨hpreFlip, by simpa using htermSkip⟩

/-- Uniform-initialization finite-history weight.  The exact value of the constant
initial weight is intentionally left as `1 / card`: the next mass-summing slice can
normalize it without needing a separate `2^n` cardinality lemma first. -/
noncomputable def leadingOnesUniformFiniteHistoryWeight
    {n t : ℕ} (p : ℝ) (h : LeadingOnesFiniteHistory n t) : ℝ :=
  ((Fintype.card (BitString n) : ℝ)⁻¹) *
    finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t h.1 h.2

/-- On pre-crossing histories, the uniform-initialization finite-history weight is
preserved by the coordinate-flip involution. -/
theorem leadingOnesUniformFiniteHistoryWeight_flip
    {n t : ℕ} (p : ℝ) (i : Fin n) (h : LeadingOnesFiniteHistory n t)
    (hpre : leadingOnesHistoryPreCrossing i h) :
    leadingOnesUniformFiniteHistoryWeight p (leadingOnesFiniteHistoryFlip i h) =
      leadingOnesUniformFiniteHistoryWeight p h := by
  rcases h with ⟨x, path⟩
  change leadingOnesPreCrossing i t x path at hpre
  unfold leadingOnesUniformFiniteHistoryWeight
  change
    ((Fintype.card (BitString n) : ℝ)⁻¹) *
        finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t
          (leadingOnesCoordinateFlip i x)
          (leadingOnesFiniteTrajectoryFlip i path) =
      ((Fintype.card (BitString n) : ℝ)⁻¹) *
        finiteTrajectoryWeight (onePlusOneTransition p leadingOnesReal) t x path
  rw [finiteTrajectoryWeight_leadingOnesCoordinateFlip p i t x path hpre]

end ECRuntime
