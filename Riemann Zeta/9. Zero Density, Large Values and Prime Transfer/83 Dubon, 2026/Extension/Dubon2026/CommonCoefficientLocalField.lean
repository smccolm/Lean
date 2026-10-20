import Dubon2026.CommonCoefficientField
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension

/-! The common coefficient field is a genuine finite local extension.
Reuse the original compatible norm and the proved spectral finite-field
extension and valuation-extension theorems. The finite field constructed
from all original embedding images acquires its actual local structure;
the common-field existence and adequacy required in BLGG Section 3.2
are derived together, on the route to Dubon's Theorem 2.6.
-/

namespace Dubon2026
noncomputable section

/-- The constructed common field admits a finite local coefficient extension structure preserving the original valuation and containing every original number-field embedding. -/
theorem commonCoefficientField_exists_local_structure
    (K F : Type) [Field K] [NumberField K] [Field F] [CharZero F]
    [ValuativeRel F] [UniformSpace F] [IsUniformAddGroup F] [IsNonarchimedeanLocalField F] :
    ∃ (_ : UniformSpace (commonCoefficientField K F))
      (_ : ValuativeRel (commonCoefficientField K F)),
      IsUniformAddGroup (commonCoefficientField K F) ∧
      IsNonarchimedeanLocalField (commonCoefficientField K F) ∧
      (ValuativeRel.valuation F).HasExtension
        (ValuativeRel.valuation (commonCoefficientField K F)) ∧
      FiniteDimensional F (commonCoefficientField K F) ∧
      ∀ (tau : K →ₐ[ℚ] AlgebraicClosure F) (x : K), tau x ∈ commonCoefficientField K F := by
  let normF := localFieldOriginalNorm F
  letI : NontriviallyNormedField F := normF
  letI : NormedField F := normF.toNormedField
  haveI : CompleteSpace F := localFieldOriginalNorm_complete F
  haveI : IsUltrametricDist F := localFieldOriginalNorm_isUltrametric F
  haveI : (NormedField.valuation (K := F)).Compatible := localFieldOriginalNorm_compatible F
  let E := commonCoefficientField K F
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField F E
  letI : NormedAlgebra F E := spectralNorm.normedAlgebra F E
  haveI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra F
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  haveI : IsNonarchimedeanLocalField E := spectralFiniteExtension_isNonarchimedeanLocalField F E
  haveI : (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension F E
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, commonCoefficientField_contains K F⟩

end
end Dubon2026
