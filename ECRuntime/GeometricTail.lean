import ECRuntime.GeometricRuntime
import Mathlib

open MeasureTheory

namespace ECRuntime

/--
For the one-based waiting-time convention, the strict tail above the natural threshold
`k` is exactly the set of failure counts at least `k`.
-/
@[simp] theorem runtimeTailEvent_geometricWaitingTime_nat (k : ℕ) :
    runtimeTailEvent geometricWaitingTime (k : ENNReal) = Set.Ici k := by
  ext n
  change ((k : ENNReal) < (((n + 1 : ℕ) : ENNReal))) ↔ k ≤ n
  norm_cast
  omega

/--
The real geometric mass shifted by `k` has total mass `(1-p)^k`.  This is the
analytic core of the geometric survival identity; it is obtained by multiplying
Mathlib's normalized geometric series by the shift factor.
-/
theorem hasSum_geometricFailure_tail
    {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    HasSum
      (fun n : ℕ => (1 - (p : ℝ)) ^ (k + n) * (p : ℝ))
      ((1 - (p : ℝ)) ^ k) := by
  simpa [pow_add, mul_assoc] using
    (ProbabilityTheory.hasSum_one_geometricMeasure hp).mul_left
      ((1 - (p : ℝ)) ^ k)

/-- The corresponding shifted geometric series after embedding into `ENNReal`. -/
theorem tsum_geometricFailure_tail
    {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    (∑' n : ℕ,
        ENNReal.ofReal
          ((1 - (p : ℝ)) ^ (k + n) * (p : ℝ))) =
      ENNReal.ofReal ((1 - (p : ℝ)) ^ k) := by
  have hsum := hasSum_geometricFailure_tail hp k
  rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun n => ProbabilityTheory.geometricMeasure_nonneg p (k + n))
        hsum.summable,
      hsum.tsum_eq]

/-- Natural numbers at least `k` are the disjoint union of the singletons `{k+n}`. -/
theorem iUnion_singleton_nat_add_eq_Ici (k : ℕ) :
    (⋃ n : ℕ, ({k + n} : Set ℕ)) = Set.Ici k := by
  ext m
  constructor
  · intro hm
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hm
    rcases hm with ⟨n, rfl⟩
    simp
  · intro hm
    have hkm : k ≤ m := by
      simpa using hm
    refine Set.mem_iUnion.2 ⟨m - k, ?_⟩
    simp only [Set.mem_singleton_iff]
    omega

/-- The singleton family `{k+n}` is pairwise disjoint. -/
theorem pairwise_disjoint_singleton_nat_add (k : ℕ) :
    Pairwise (Function.onFun Disjoint (fun n : ℕ => ({k + n} : Set ℕ))) := by
  intro i j hij
  change Disjoint ({k + i} : Set ℕ) ({k + j} : Set ℕ)
  refine Set.disjoint_left.2 ?_
  intro x hxi hxj
  simp only [Set.mem_singleton_iff] at hxi hxj
  apply hij
  omega

/--
Exact upper-tail mass of Mathlib's geometric failure-count law.  The hypothesis
`p ≠ 0` is necessary because Mathlib deliberately defines `geometricMeasure 0`
as a Dirac mass at zero so that it remains a probability measure.
-/
theorem geometricFailureMeasure_Ici
    {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    geometricFailureMeasure p (Set.Ici k) = geometricSurvival p k := by
  rw [← iUnion_singleton_nat_add_eq_Ici k,
      measure_iUnion (pairwise_disjoint_singleton_nat_add k)
        (fun n => MeasurableSet.singleton (k + n))]
  simp_rw [geometricFailureMeasure_singleton hp]
  simpa [geometricSurvival] using tsum_geometricFailure_tail hp k

/--
Exact strict survival probability of the EC one-based geometric waiting time:
`P(G > k) = (1-p)^k`.
-/
theorem geometricWaitingTime_tail_exact
    {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    runtimeTailMass
        (geometricFailureMeasure p) geometricWaitingTime (k : ENNReal) =
      geometricSurvival p k := by
  unfold runtimeTailMass
  rw [runtimeTailEvent_geometricWaitingTime_nat]
  exact geometricFailureMeasure_Ici hp k

/-- The canonical geometric waiting time satisfies its geometric tail certificate with equality. -/
theorem hasGeometricTailBound_geometricWaitingTime
    {p : unitInterval} (hp : p ≠ 0) :
    HasGeometricTailBound
      (geometricFailureMeasure p) geometricWaitingTime p := by
  intro k
  exact (geometricWaitingTime_tail_exact hp k).le

/--
The same exact survival identity on the pushed-forward waiting-time law on `ENNReal`.
-/
theorem geometricWaitingMeasure_Ioi
    {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    geometricWaitingMeasure p (Set.Ioi (k : ENNReal)) =
      geometricSurvival p k := by
  rw [geometricWaitingMeasure,
      Measure.map_apply measurable_geometricWaitingTime measurableSet_Ioi]
  change geometricFailureMeasure p
      (runtimeTailEvent geometricWaitingTime (k : ENNReal)) = geometricSurvival p k
  exact geometricWaitingTime_tail_exact hp k

/-- Exact natural-threshold tail mass of the identity runtime under the waiting-time law. -/
theorem geometricWaitingMeasure_runtimeTailMass
    {p : unitInterval} (hp : p ≠ 0) (k : ℕ) :
    runtimeTailMass (geometricWaitingMeasure p) id (k : ENNReal) =
      geometricSurvival p k := by
  change geometricWaitingMeasure p (Set.Ioi (k : ENNReal)) = geometricSurvival p k
  exact geometricWaitingMeasure_Ioi hp k

end ECRuntime
