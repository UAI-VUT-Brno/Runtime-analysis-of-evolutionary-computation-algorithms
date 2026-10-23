import ECRuntimeTest.AxiomAudit
import ECRuntimeTest.NonVacuity
import ECRuntimeTest.Stage111NonVacuity
import ECRuntimeTest.Stage141NonVacuity
import ECRuntimeTest.Stage165NonVacuity

/-!
# Representative regression tests

The strict `scripts/audit.lean` examines the compiled environment for *all* public
ECRuntime declarations and transitively checks their axiom dependencies.  These
few tests exercise nonempty instances and the principal newly closed runtime
branches, instead of maintaining one near-duplicate witness per promotion round.
-/
