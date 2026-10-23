import ECRuntime.LeadingOnesStationaryRootExists
import ECRuntime.LeadingOnesStationaryAntitone
import Mathlib

namespace ECRuntime

/-!
Stage 157 — USER-APPROVED; individually compiler-clean in Round 36.
Provisional public promotion gate prepared in Round 37.
Böttcher--Doerr--Neumann (2010), fixed-rate LeadingOnes.

Existence (Stage 155) and strict antitonicity beyond rate 1 (Stage 152)
together imply that the stationary rate in (1,2) is unique. This packages
the reusable uniqueness statement independently of the global-minimum
proof under development in Stage 111.
-/

/-- Exactly one scaled fixed mutation rate in `(1,2)` solves the
LeadingOnes stationary equation. -/
theorem proposed_leadingOnes_uniqueStationaryRoot_Ioo :
    ∃! c : Real, 1 < c ∧ c < 2 ∧ (2 - c) * Real.exp c = 2 := by
  obtain ⟨r, hr1, hr2, hroot⟩ :=
    proposed_leadingOnes_stationaryRoot_exists
  refine ⟨r, ⟨hr1, hr2, hroot⟩, ?_⟩
  intro d hd
  rcases hd with ⟨hd1, _hd2, hdroot⟩
  rcases lt_trichotomy d r with hlt | heq | hgt
  · have hanti := proposed_leadingOnes_stationaryFactor_strictAntiOn
      (Set.mem_Ioi.mpr hd1) (Set.mem_Ioi.mpr hr1) hlt
    change (2 - r) * Real.exp r < (2 - d) * Real.exp d at hanti
    rw [hroot, hdroot] at hanti
    exact False.elim ((lt_irrefl (2 : Real)) hanti)
  · exact heq
  · have hanti := proposed_leadingOnes_stationaryFactor_strictAntiOn
      (Set.mem_Ioi.mpr hr1) (Set.mem_Ioi.mpr hd1) hgt
    change (2 - d) * Real.exp d < (2 - r) * Real.exp r at hanti
    rw [hdroot, hroot] at hanti
    exact False.elim ((lt_irrefl (2 : Real)) hanti)

end ECRuntime
