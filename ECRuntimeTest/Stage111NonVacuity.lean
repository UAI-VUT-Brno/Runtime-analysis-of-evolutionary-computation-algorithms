import ECRuntime.LeadingOnesOptimalRate

namespace ECRuntimeTest
open ECRuntime

/-- The fixed-rate theorem constructs a genuine optimizer in the real
interval (1,2), with all positive rates as competitors. -/
private theorem stage111_optimizer_witness :
    ∃ c : Real, 1 < c ∧ c < 2 ∧
      ∀ d : Real, 0 < d →
        leadingOnesFixedRateCoefficient c ≤
          leadingOnesFixedRateCoefficient d := by
  obtain ⟨c, hc1, hc2, _hroot, hmin, _huniq⟩ :=
    leadingOnes_fixedRate_unique_optimum
  exact ⟨c, hc1, hc2, hmin⟩

end ECRuntimeTest
