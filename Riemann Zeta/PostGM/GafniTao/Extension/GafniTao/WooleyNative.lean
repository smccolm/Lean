import GafniTao.WooleySourceCriticalBase
import GafniTao.WooleySourceToPadic
import GafniTao.WooleyPadicToCritical
import GafniTao.HeathBrownKthDerivativeConditional

/-!
# Native Wooley and Heath--Brown consequences

This file is the audited composition point from Wooley's source polynomial
mean-value theorem through the monomial p-adic specialization and critical
Vinogradov mean value theorem to Heath--Brown's k-th derivative estimate.
-/

namespace GafniTao

noncomputable section

/-- The Vinogradov main-conjecture estimate, obtained from the proved source
form of Wooley's Corollary 3.2. -/
theorem heathBrownVMVTMainConjecture_native :
    HeathBrownVMVTMainConjecture :=
  heathBrownVMVTMainConjecture_of_wooleyPadic
    (wooleyMonomialPadicConcentration_of_polynomialCorollary32
      wooleyPolynomialCorollary32_native)

/-- Heath--Brown's k-th derivative estimate with its VMVT dependency
discharged by the native Wooley chain. -/
theorem heathBrownKthDerivativeTheorem_native :
    HeathBrownKthDerivativeTheorem :=
  heathBrownKthDerivativeTheorem_of_vmvt
    heathBrownVMVTMainConjecture_native

#print axioms heathBrownVMVTMainConjecture_native
#print axioms heathBrownKthDerivativeTheorem_native

end

end GafniTao
