#!/usr/bin/env bash
# Parameterized verification of the consolidated certified library.
# Set ECRUNTIME_VERIFY_STAGE to choose an evidence label. A promoted theorem
# is checked through the public build, the official eight gates, a concrete
# witness, a frozen statement fingerprint and an independent axiom probe.
set -uo pipefail
if [ "$#" -lt 1 ] || [ "$#" -gt 2 ]; then
  echo 'Usage: run_verification.sh /absolute/repository [/absolute/results.zip]' >&2
  exit 2
fi
REPO="$(cd "$1" && pwd)" || exit 2
TAG="${ECRUNTIME_VERIFY_STAGE:-consolidated_release}"
case "$TAG" in
  *[!a-zA-Z0-9._-]*|'') echo 'Invalid verification label' >&2; exit 2;;
esac
OUT="${2:-$PWD/ECRuntime_verification_results.zip}"
case "$OUT" in /*) ;; *) OUT="$PWD/$OUT";; esac
cd "$REPO" || exit 2
D=".verify/${TAG}_audit"
G=".verify/stage-${TAG}"
mkdir -p "$D"
: > "$D/status.txt"
FAIL=0
runcheck() {
  local label="$1"; shift
  "$@" > "$D/$label.log" 2>&1
  local rc=$?
  printf '%s=%s\n' "$label" "$rc" >> "$D/status.txt"
  if [ "$rc" -ne 0 ]; then FAIL=1; fi
}
{
  date -u '+timestamp_utc=%Y-%m-%dT%H:%M:%SZ'
  echo "repo_root=$REPO"
  echo 'certified_checkpoint=Round56 passed full eight-gate check; 60 selected stages (107..166)'
  echo "verification_label=$TAG"
  echo 'candidate_scope=zero approved-open; Stage166 promoted with original header SHA256 protected'
  cat lean-toolchain
  lean --version
  lake --version
} > "$D/environment.txt" 2>&1
runcheck source_audit python3 scripts/consolidation_audit.py
runcheck library_and_regression_build lake build ECRuntime ECRuntimeTest
if [ -f "$D/library_and_regression_build.log" ] && grep -Eq '(^|[[:space:]])(error|warning):' "$D/library_and_regression_build.log"; then
  echo 'build_diagnostics=1' >> "$D/status.txt"; FAIL=1
else
  echo 'build_diagnostics=0' >> "$D/status.txt"
fi
if command -v pwsh >/dev/null 2>&1; then
  runcheck official_eight_gate pwsh -NoProfile -File scripts/verify.ps1 \
    -Stage "$TAG" -Focus ECRuntime.RLSUniformInitialCouponSurvivalInclusionExclusion
else
  echo 'MISSING: pwsh (official gate cannot run)' > "$D/official_eight_gate.log"
  echo 'official_eight_gate=125' >> "$D/status.txt"
  FAIL=1
fi
# An official gate may report zero but still fail expected hygiene baseline.
if [ -f "$G/hygiene.log" ]; then
  runcheck no_new_hygiene_warnings python3 scripts/compare_hygiene.py \
    "$G/hygiene.log" scripts/hygiene_baseline.txt
else
  echo 'no_new_hygiene_warnings=125' >> "$D/status.txt"
  echo 'SKIPPED: official hygiene log missing' > "$D/no_new_hygiene_warnings.log"
  FAIL=1
fi
# Probe representative theorem axioms in the *built public library*.
cat > "$D/axiom_probe.lean" <<'LEAN'
import ECRuntime.LeadingOnesOptimalRate
import ECRuntime.RLSUniformInitialRuntimeSecondOrder
import ECRuntime.RLSUniformInitialCouponSurvivalCapped
import ECRuntime.RLSUniformInitialCouponSurvivalInclusionExclusion
#print axioms ECRuntime.leadingOnes_fixedRate_unique_optimum
#print axioms ECRuntime.proposed_rlsLinear_uniformStart_runtime_secondOrder
#print axioms ECRuntime.proposed_rlsLinear_uniformInitial_couponSurvivalCapped
#print axioms ECRuntime.proposed_rlsLinear_uniformInitial_couponSurvival_inclusionExclusion
LEAN
runcheck main_theorem_axioms lake env lean "$D/axiom_probe.lean"
if grep -Eq 'sorryAx|Lean.ofReduceBool|error:|warning:' "$D/main_theorem_axioms.log" || \
   ! grep -Fq "proposed_rlsLinear_uniformInitial_couponSurvival_inclusionExclusion' depends on axioms" "$D/main_theorem_axioms.log"; then
  echo 'unapproved_axiom_probe_diagnostics=1' >> "$D/status.txt"; FAIL=1
else
  echo 'unapproved_axiom_probe_diagnostics=0' >> "$D/status.txt"
fi
# Optional exact-rational cross-checks for the now-certified distribution;
# these catch regressions but do not substitute for kernel proof verification.
runcheck stage166_small_cases python3 candidates/check_stage166_small.py
# The independent former candidate source has been retired. Instead compile
# the *public* theorem module and verify its frozen header through the audit.
runcheck stage166_promoted_public_module lake build ECRuntime.RLSUniformInitialCouponSurvivalInclusionExclusion
if [ "$FAIL" -eq 0 ]; then
  echo 'consolidation_public_gate=PASSED' >> "$D/status.txt"
  echo 'stage166_promotion_integration=PASSED_PROMOTED' >> "$D/status.txt"
  echo 'remaining_approved_open_candidates=0' >> "$D/status.txt"
else
  echo 'consolidation_public_gate=FAILED_OR_SKIPPED' >> "$D/status.txt"
  echo 'stage166_promotion_integration=FAILED_NOT_REVERIFIED' >> "$D/status.txt"
fi
mkdir -p "$(dirname "$OUT")"
# Zip only verification evidence; the repository source has its own ZIP.
zip -q -r "$OUT" "$D" "$G" 2>/dev/null || zip -q -r "$OUT" "$D"
printf 'RESULTS_ZIP=%s\n' "$OUT"
if [ "$FAIL" -ne 0 ]; then exit 1; fi
exit 0
