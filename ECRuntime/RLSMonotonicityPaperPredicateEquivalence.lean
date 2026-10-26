import ECRuntime.StrictMonotoneRLSKernelSupport
import Mathlib

namespace ECRuntime

/-! P02 audit obligation. The paper uses the global Boolean product-order
strict monotonicity definition, whereas the current Lean theorem requires
strict improvement under every single 0->1 coordinate flip. These are
mathematically equivalent on a finite cube, but the repository should
make that correspondence explicit instead of relying on prose. -/

/-- Global strict coordinate order monotonicity implies the singleton
improvement predicate used by the certified one-bit RLS theorems. -/
theorem proposed_P02_globalStrictMonotone_implies_singleton
    {n : Nat} (fitness : BitString n → Real)
    (hglobal : ∀ x y : BitString n,
      (∀ i : Fin n, x i = true → y i = true) → x ≠ y →
       fitness x < fitness y) :
    CandidateCoordinateStrictMonotonicity fitness := by
  intro x i hx
  apply hglobal x (mutateWithMask x ({i} : MutationMask n))
  · intro j hj
    by_cases hji : j = i
    · subst j
      simp_all
    · simpa [mutateWithMask, hji] using hj
  · intro heq
    have hi := congrArg (fun y : BitString n => y i) heq
    simp [hx] at hi

end ECRuntime
