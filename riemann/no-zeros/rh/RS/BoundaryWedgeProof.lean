import rh.RS.sealed.BoundaryWedgeProofCore
import rh.analytic_number_theory.VinogradovKorobov

/-
# Boundary wedge proof – public API

This file intentionally keeps the Route B dependency surface small.  The full
arithmetical proof of `(P+)` along with all intermediate Whitney/VK machinery
now lives in `rh/RS/sealed/BoundaryWedgeProofCore.lean`.  Here we re-export only
the handful of declarations that the rest of the pipeline consumes:

* the calibrated constants (`A_default`, `B_default`, …),
* the dyadic bookkeeping helpers (`phi_of_nu`, `nu_default`, …),
* the VK partial-sum budget interface,
* the final `(P+)` theorem `PPlus_from_constants`.

Downstream stages should import this file (not the sealed core) so that the
analytic payload remains fenced off from the AF/RS build targets.
-/

namespace RH.RS.BoundaryWedgeProof

export RH.RS.BoundaryWedgeProof.Sealed
  (A_default B_default Cdiag_default C_cross_default
   phi_of_nu nu_default nu_default_nonneg
   VKPartialSumBudget VKPartialSumBudget.from_counts
   PPlus_from_constants)

export RH.AnalyticNumberTheory.VinogradovKorobov
  (ShortIntervalCounts
   ShortIntervalCounts.partial_sum_bound
   VinogradovKorobov.Standalone.AssembledConstants
   VinogradovKorobov.Standalone.Export
   VinogradovKorobov.Standalone.assembleConstants
   VinogradovKorobov.Standalone.buildVKExport
   defaultCounts
   hVK_counts_default
   VKPartialSumBudget_from_counts_default)

end RH.RS.BoundaryWedgeProof
