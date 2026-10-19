import ECRuntime.LeadingOnesExit
import Mathlib

namespace ECRuntime

/-!
# Stage 27 fix 3: coordinate-flip symmetry for LeadingOnes

The exact exit probability from a visited LeadingOnes level is already isolated in
`LeadingOnesExit.lean`.  The remaining benchmark-specific ingredient for the classical
runtime formula is the fact that, under symmetric initialization, every nonterminal
level is visited with probability one half.

The key deterministic/probabilistic symmetry is local to the first not-yet-relevant
coordinate.  Fix `i : Fin n`.  As long as the current LeadingOnes value is strictly
below `i`, toggling coordinate `i`

* leaves the LeadingOnes value unchanged;
* commutes with every mutation mask;
* preserves the accept/reject decision of elitist LeadingOnes selection; and therefore
* conjugates the `(1+1)`-EA transition kernel by the same coordinate flip.

Once the prefix reaches coordinate `i`, the same involution exchanges the two boundary
branches: exact level `i` and a strict skip above `i`.  A later finite-trajectory slice
can therefore pair first-crossing histories with equal weight and obtain the desired
`1/2` visit mass under a flip-invariant initial law.
-/

/-- Toggle one specified search-point coordinate. -/
def leadingOnesCoordinateFlip {n : ℕ} (i : Fin n) (x : BitString n) : BitString n :=
  fun j => if j = i then flipBit (x j) else x j

@[simp] theorem leadingOnesCoordinateFlip_self
    {n : ℕ} (i : Fin n) (x : BitString n) :
    leadingOnesCoordinateFlip i x i = flipBit (x i) := by
  simp [leadingOnesCoordinateFlip]

@[simp] theorem leadingOnesCoordinateFlip_of_ne
    {n : ℕ} (i j : Fin n) (x : BitString n) (hji : j ≠ i) :
    leadingOnesCoordinateFlip i x j = x j := by
  simp [leadingOnesCoordinateFlip, hji]

/-- Toggling one coordinate twice is the identity. -/
@[simp] theorem leadingOnesCoordinateFlip_involutive
    {n : ℕ} (i : Fin n) (x : BitString n) :
    leadingOnesCoordinateFlip i (leadingOnesCoordinateFlip i x) = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [leadingOnesCoordinateFlip, hji]

/-- Coordinate flip is injective, as expected from involutivity. -/
theorem leadingOnesCoordinateFlip_injective
    {n : ℕ} (i : Fin n) :
    Function.Injective (leadingOnesCoordinateFlip i) := by
  intro x y hxy
  have h := congrArg (leadingOnesCoordinateFlip i) hxy
  rw [leadingOnesCoordinateFlip_involutive,
      leadingOnesCoordinateFlip_involutive] at h
  exact h

/-- Removing the head coordinate commutes with toggling a positive coordinate. -/
@[simp] theorem bitStringTail_leadingOnesCoordinateFlip_succ
    {n : ℕ} (i : Fin n) (x : BitString (n + 1)) :
    bitStringTail (leadingOnesCoordinateFlip i.succ x) =
      leadingOnesCoordinateFlip i (bitStringTail x) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [bitStringTail, leadingOnesCoordinateFlip]
  · have hsucc : j.succ ≠ i.succ := by
      intro h
      apply hji
      apply Fin.ext
      have hval := congrArg Fin.val h
      change j.val + 1 = i.val + 1 at hval
      omega
    simp [bitStringTail, leadingOnesCoordinateFlip, hji, hsucc]

/-- A coordinate strictly after the current LeadingOnes prefix is irrelevant to the value. -/
theorem leadingOnes_coordinateFlip_eq_of_lt :
    ∀ {n : ℕ} (x : BitString n) (i : Fin n),
      leadingOnes x < i.val →
        leadingOnes (leadingOnesCoordinateFlip i x) = leadingOnes x := by
  intro n
  induction n with
  | zero =>
      intro x i
      exact Fin.elim0 i
  | succ n ih =>
      intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · intro hbelow
        simp at hbelow
      · intro hbelow
        have hzeroNe : (0 : Fin (n + 1)) ≠ j.succ := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
        by_cases h0 : x 0 = true
        · have hflip0 : leadingOnesCoordinateFlip j.succ x 0 = true := by
            rw [leadingOnesCoordinateFlip_of_ne j.succ 0 x hzeroNe]
            exact h0
          have htailBelow : leadingOnes (bitStringTail x) < j.val := by
            rw [leadingOnes_succ, if_pos h0] at hbelow
            change 1 + leadingOnes (bitStringTail x) < j.val + 1 at hbelow
            omega
          have htail :
              leadingOnes (leadingOnesCoordinateFlip j (bitStringTail x)) =
                leadingOnes (bitStringTail x) :=
            ih (bitStringTail x) j htailBelow
          calc
            leadingOnes (leadingOnesCoordinateFlip j.succ x) =
                1 + leadingOnes (bitStringTail (leadingOnesCoordinateFlip j.succ x)) := by
              rw [leadingOnes_succ, if_pos hflip0]
            _ = 1 + leadingOnes (leadingOnesCoordinateFlip j (bitStringTail x)) := by
              rw [bitStringTail_leadingOnesCoordinateFlip_succ]
            _ = 1 + leadingOnes (bitStringTail x) := by
              rw [htail]
            _ = leadingOnes x := by
              symm
              rw [leadingOnes_succ, if_pos h0]
        · have hflip0 : leadingOnesCoordinateFlip j.succ x 0 ≠ true := by
            rw [leadingOnesCoordinateFlip_of_ne j.succ 0 x hzeroNe]
            exact h0
          calc
            leadingOnes (leadingOnesCoordinateFlip j.succ x) = 0 := by
              rw [leadingOnes_succ, if_neg hflip0]
            _ = leadingOnes x := by
              symm
              rw [leadingOnes_succ, if_neg h0]

/-- A true prefix of length `k` forces at least `k` leading ones. -/
theorem leadingOnes_ge_of_prefix_true
    {n k : ℕ} (x : BitString n) (hk : k ≤ n)
    (hprefix : ∀ j : Fin n, j.val < k → x j = true) :
    k ≤ leadingOnes x := by
  by_cases hk0 : k = 0
  · subst k
    exact Nat.zero_le _
  · have hidxLt : k - 1 < n := by omega
    let i : Fin n := ⟨k - 1, hidxLt⟩
    have hthrough : ∀ j : Fin n, j.val ≤ i.val → x j = true := by
      intro j hj
      apply hprefix j
      dsimp [i] at hj
      omega
    have hgt := leadingOnes_gt_of_prefix_true x i hthrough
    dsimp [i] at hgt
    omega

/-- A true prefix followed by a false coordinate characterizes an exact LeadingOnes level. -/
theorem leadingOnes_eq_of_prefix_true_bit_false
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hprefix : ∀ j : Fin n, j.val < i.val → x j = true)
    (hfalse : x i = false) :
    leadingOnes x = i.val := by
  have hge : i.val ≤ leadingOnes x := by
    apply leadingOnes_ge_of_prefix_true x (Nat.le_of_lt i.isLt)
    exact hprefix
  have hle : leadingOnes x ≤ i.val := by
    by_contra hnot
    have hgt : i.val < leadingOnes x := by omega
    have htrue := bit_eq_true_of_lt_leadingOnes x i hgt
    rw [hfalse] at htrue
    simp at htrue
  omega

/-- Toggling the first zero of an exact level turns it into a strict skip above that level. -/
theorem leadingOnes_coordinateFlip_gt_of_eq
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hlevel : leadingOnes x = i.val) :
    i.val < leadingOnes (leadingOnesCoordinateFlip i x) := by
  apply leadingOnes_gt_of_prefix_true (leadingOnesCoordinateFlip i x) i
  intro j hj
  rcases lt_or_eq_of_le hj with hlt | heq
  · have hji : j ≠ i := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hxj : x j = true := by
      apply bit_eq_true_of_lt_leadingOnes x j
      rw [hlevel]
      exact hlt
    simp [leadingOnesCoordinateFlip, hji, hxj]
  · have hji : j = i := Fin.ext heq
    subst j
    have hfalse := bit_eq_false_of_leadingOnes_eq x i hlevel
    simp [leadingOnesCoordinateFlip, hfalse]

/-- If coordinate `i` lies inside the LeadingOnes prefix, toggling it creates exact level `i`. -/
theorem leadingOnes_coordinateFlip_eq_of_gt
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hgt : i.val < leadingOnes x) :
    leadingOnes (leadingOnesCoordinateFlip i x) = i.val := by
  apply leadingOnes_eq_of_prefix_true_bit_false
  · intro j hj
    have hji : j ≠ i := by
      intro h
      have hval := congrArg Fin.val h
      omega
    have hxj : x j = true := by
      apply bit_eq_true_of_lt_leadingOnes x j
      exact lt_trans hj hgt
    simp [leadingOnesCoordinateFlip, hji, hxj]
  · have hxi := bit_eq_true_of_lt_leadingOnes x i hgt
    simp [leadingOnesCoordinateFlip, hxi]

/-- On or above the boundary, a coordinate flip stays on or above the same boundary. -/
theorem leadingOnes_coordinateFlip_ge_of_ge
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hge : i.val ≤ leadingOnes x) :
    i.val ≤ leadingOnes (leadingOnesCoordinateFlip i x) := by
  rcases eq_or_lt_of_le hge with heq | hgt
  · have hstrict := leadingOnes_coordinateFlip_gt_of_eq x i heq.symm
    omega
  · rw [leadingOnes_coordinateFlip_eq_of_gt x i hgt]

/-- At the boundary, coordinate flip exchanges exact-level and strict-skip states. -/
theorem leadingOnes_coordinateFlip_eq_level_iff_gt
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hge : i.val ≤ leadingOnes x) :
    leadingOnes (leadingOnesCoordinateFlip i x) = i.val ↔
      i.val < leadingOnes x := by
  constructor
  · intro hflip
    by_contra hnot
    have heq : leadingOnes x = i.val := by omega
    have hstrict := leadingOnes_coordinateFlip_gt_of_eq x i heq
    rw [hflip] at hstrict
    omega
  · intro hgt
    exact leadingOnes_coordinateFlip_eq_of_gt x i hgt

/-- Dually, a strict skip after toggling is equivalent to exact level `i` before toggling. -/
theorem leadingOnes_coordinateFlip_gt_iff_eq_level
    {n : ℕ} (x : BitString n) (i : Fin n)
    (hge : i.val ≤ leadingOnes x) :
    i.val < leadingOnes (leadingOnesCoordinateFlip i x) ↔
      leadingOnes x = i.val := by
  constructor
  · intro hflip
    by_contra hne
    have hgt : i.val < leadingOnes x := by omega
    rw [leadingOnes_coordinateFlip_eq_of_gt x i hgt] at hflip
    omega
  · intro heq
    exact leadingOnes_coordinateFlip_gt_of_eq x i heq

/-- Mutation by an arbitrary mask commutes with toggling one coordinate. -/
theorem mutateWithMask_leadingOnesCoordinateFlip_commute
    {n : ℕ} (x : BitString n) (i : Fin n) (mask : MutationMask n) :
    mutateWithMask (leadingOnesCoordinateFlip i x) mask =
      leadingOnesCoordinateFlip i (mutateWithMask x mask) := by
  funext j
  by_cases hji : j = i
  · subst j
    by_cases him : i ∈ mask
    · simp [mutateWithMask, leadingOnesCoordinateFlip, him]
    · simp [mutateWithMask, leadingOnesCoordinateFlip, him]
  · by_cases hjm : j ∈ mask
    · simp [mutateWithMask, leadingOnesCoordinateFlip, hji, hjm]
    · simp [mutateWithMask, leadingOnesCoordinateFlip, hji, hjm]

/-- Below boundary `i`, the LeadingOnes acceptance comparison is invariant under flipping `i`. -/
theorem leadingOnes_acceptance_coordinateFlip_iff
    {n : ℕ} (parent child : BitString n) (i : Fin n)
    (hparent : leadingOnes parent < i.val) :
    leadingOnes parent ≤ leadingOnes child ↔
      leadingOnes (leadingOnesCoordinateFlip i parent) ≤
        leadingOnes (leadingOnesCoordinateFlip i child) := by
  have hparentFlip := leadingOnes_coordinateFlip_eq_of_lt parent i hparent
  rw [hparentFlip]
  by_cases hchild : leadingOnes child < i.val
  · rw [leadingOnes_coordinateFlip_eq_of_lt child i hchild]
  · have hchildGe : i.val ≤ leadingOnes child := by omega
    have hflipGe := leadingOnes_coordinateFlip_ge_of_ge child i hchildGe
    constructor <;> intro _ <;> omega

/-- Real-objective acceptance has the same coordinate-flip symmetry. -/
theorem leadingOnesReal_acceptance_coordinateFlip_iff
    {n : ℕ} (parent child : BitString n) (i : Fin n)
    (hparent : leadingOnes parent < i.val) :
    leadingOnesReal parent ≤ leadingOnesReal child ↔
      leadingOnesReal (leadingOnesCoordinateFlip i parent) ≤
        leadingOnesReal (leadingOnesCoordinateFlip i child) := by
  unfold leadingOnesReal
  constructor
  · intro h
    have hnat : leadingOnes parent ≤ leadingOnes child := by
      exact_mod_cast h
    have hflipNat :=
      (leadingOnes_acceptance_coordinateFlip_iff parent child i hparent).1 hnat
    exact_mod_cast hflipNat
  · intro h
    have hflipNat :
        leadingOnes (leadingOnesCoordinateFlip i parent) ≤
          leadingOnes (leadingOnesCoordinateFlip i child) := by
      exact_mod_cast h
    have hnat :=
      (leadingOnes_acceptance_coordinateFlip_iff parent child i hparent).2 hflipNat
    exact_mod_cast hnat

/-- Below boundary `i`, elitist selection commutes with coordinate flip for every mask. -/
theorem selectedAfterMask_leadingOnes_coordinateFlip
    {n : ℕ} (parent : BitString n) (i : Fin n) (mask : MutationMask n)
    (hparent : leadingOnes parent < i.val) :
    selectedAfterMask leadingOnesReal (leadingOnesCoordinateFlip i parent) mask =
      leadingOnesCoordinateFlip i
        (selectedAfterMask leadingOnesReal parent mask) := by
  have hmut := mutateWithMask_leadingOnesCoordinateFlip_commute parent i mask
  have hacc := leadingOnesReal_acceptance_coordinateFlip_iff
    parent (mutateWithMask parent mask) i hparent
  unfold selectedAfterMask elitistSelect
  rw [hmut]
  by_cases ha : leadingOnesReal parent ≤ leadingOnesReal (mutateWithMask parent mask)
  · have haFlip := hacc.1 ha
    simp [ha, haFlip]
  · have haFlip :
        ¬ leadingOnesReal (leadingOnesCoordinateFlip i parent) ≤
          leadingOnesReal
            (leadingOnesCoordinateFlip i (mutateWithMask parent mask)) := by
      intro h
      exact ha (hacc.2 h)
    simp [ha, haFlip]

/-- The `(1+1)`-EA LeadingOnes kernel is conjugate under coordinate flip below the boundary. -/
theorem onePlusOneTransition_leadingOnes_coordinateFlip
    {n : ℕ} (p : ℝ) (parent next : BitString n) (i : Fin n)
    (hparent : leadingOnes parent < i.val) :
    onePlusOneTransition p leadingOnesReal
        (leadingOnesCoordinateFlip i parent)
        (leadingOnesCoordinateFlip i next) =
      onePlusOneTransition p leadingOnesReal parent next := by
  classical
  unfold onePlusOneTransition pushforwardWeight
  apply Finset.sum_congr rfl
  intro mask _hmask
  have hsel := selectedAfterMask_leadingOnes_coordinateFlip parent i mask hparent
  rw [hsel]
  by_cases hnext : selectedAfterMask leadingOnesReal parent mask = next
  · simp [hnext]
  · have hflipNe :
        leadingOnesCoordinateFlip i
            (selectedAfterMask leadingOnesReal parent mask) ≠
          leadingOnesCoordinateFlip i next := by
      intro h
      apply hnext
      exact leadingOnesCoordinateFlip_injective i h
    simp [hnext, hflipNe]

end ECRuntime
