import ECRuntimeTest.AxiomAudit
import ECRuntimeTest.StatementPins
import ECRuntimeTest.NonVacuity
import ECRuntimeTest.Stage111NonVacuity
import ECRuntimeTest.Stage141NonVacuity
import ECRuntimeTest.Stage165NonVacuity
import ECRuntimeTest.VerifiedPapersAxiomAudit
import ECRuntimeTest.VerifiedPapersStatementPins

/-!
# ECRuntimeTest

The regression suite for `ECRuntime`. A Lean development has no unit tests in the
usual sense -- the proof *is* the test -- so this library checks the properties a
passing `lake build` does **not** establish on its own:

* `AxiomAudit`    -- no facade theorem acquires `sorryAx`, a new `axiom`, or
                     `native_decide`, even indirectly through a helper lemma;
* `StatementPins` -- no promoted theorem statement changes silently, which makes
                     `HISTORY.md`'s repeated "no public theorem statement changes"
                     claim mechanically enforced rather than merely asserted;
* `NonVacuity`    -- facade hypothesis sets are satisfiable, so the theorems are
                     not vacuously true;
* `VerifiedPapersAxiomAudit`, `VerifiedPapersStatementPins` -- the same axiom and
                     statement guarantees for every theorem `docs/current/papers/`
                     cites, so the paper audit cannot drift from the Lean statements.

Building this library is a promotion gate. It is in `defaultTargets`, so a plain
`lake build` runs it.
-/
