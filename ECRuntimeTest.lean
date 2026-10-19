import ECRuntimeTest.AxiomAudit
import ECRuntimeTest.StatementPins
import ECRuntimeTest.NonVacuity

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
                     not vacuously true.

Building this library is a promotion gate. It is in `defaultTargets`, so a plain
`lake build` runs it.
-/
