import ECRuntime.LeadingOnesOccupationTotalClosure
import ECRuntime.LeadingOnesStandardRateClosedForm
import ECRuntime.LeadingOnesScaledRate

namespace ECRuntime

/-!
# LeadingOnes main results

This is the stable public import façade for the completed LeadingOnes development.
Importing this module exposes, without requiring knowledge of the internal proof graph:

* `leadingOnesUniformFirstHittingTimeExpectation_eq_formula` for arbitrary `0 < p < 1`;
* `leadingOnesUniformFirstHittingTimeExpectation_scaledMutationRate_eq_formula` for
  `p = c/n`;
* `leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_formula`
  for the repository-wide standard rate `p = 1/n`;
* `leadingOnesUniformFirstHittingTimeExpectation_canonicalStandardMutationRate_eq_closedForm`
  for the conventional finite-`n` closed expression.

The older specialized theorem names remain available for compatibility.  This façade
contains no additional proof assumptions or mathematical content.
-/

end ECRuntime
