import Tao2026.Theorem25Complete
import Tao2026.ErdosSelfridgeComplete

/-!
# Remaining public-endpoint reductions

With specialized Theorem 2.5 and the square Erdős--Selfridge theorem now
internal, Proposition 2.3(ii) is the only remaining premise of the established
Section 4 route to Theorems 1.9 and 1.10.  Source-facing variants expose the
equivalent pinned Baker--Harman--Pintz boundary.
-/

namespace Tao2026

/-- Tao's Theorem 1.9 now depends only on Proposition 2.3(ii). -/
theorem taoTheorem19_of_proposition23ii
    (h23ii : TaoProposition23iiConclusion) : TaoTheorem19Conclusion :=
  taoTheorem19_of_analytic_inputs
    taoTheorem25Specialized_unconditional h23ii

/-- Tao's Theorem 1.10 now depends only on Proposition 2.3(ii). -/
theorem taoTheorem110_of_proposition23ii
    (h23ii : TaoProposition23iiConclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_analytic_inputs
    taoTheorem25Specialized_unconditional h23ii

/-- Source-facing Theorem 1.9 reduction to Baker--Harman--Pintz alone. -/
theorem taoTheorem19_of_bakerHarmanPintz
    (hBHP : BakerHarmanPintzTheorem1Conclusion) : TaoTheorem19Conclusion :=
  taoTheorem19_of_source_inputs
    taoTheorem25Specialized_unconditional hBHP

/-- Source-facing Theorem 1.10 reduction to Baker--Harman--Pintz alone. -/
theorem taoTheorem110_of_bakerHarmanPintz
    (hBHP : BakerHarmanPintzTheorem1Conclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_source_inputs
    taoTheorem25Specialized_unconditional hBHP

end Tao2026
