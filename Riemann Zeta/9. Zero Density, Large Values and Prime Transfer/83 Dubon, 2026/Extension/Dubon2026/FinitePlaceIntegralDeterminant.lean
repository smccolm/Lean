import Dubon2026.FinitePlaceSphericalLevel

/-! # Genuine integral determinant units of the original local integral general-linear group -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

/-- The determinant of the actual original invertible matrix over the genuine local integer ring. -/
def finitePlaceIntegralDetUnit (v : HeightOneSpectrum ℤ) (g : finitePlaceGL2Gamma0 1 v) :
    (v.adicCompletionIntegers ℚ)ˣ :=
  GeneralLinearGroup.det (finitePlaceIntegralMatrix v g)

/-- Mapping the genuine integral determinant unit into the original local field recovers exactly its original field determinant. -/
theorem finitePlaceIntegralDetUnit_map (v : HeightOneSpectrum ℤ) (g : finitePlaceGL2Gamma0 1 v) :
    Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (finitePlaceIntegralDetUnit v g) =
      GeneralLinearGroup.det g.val := by
  rw [← finitePlaceIntegralMatrix_map v g, GeneralLinearGroup.map_det]
  rfl

end
end Dubon2026
