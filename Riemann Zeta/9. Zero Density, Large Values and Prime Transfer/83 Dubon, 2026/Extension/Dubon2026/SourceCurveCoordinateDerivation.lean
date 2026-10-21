import Dubon2026.SourceCurveLocalDifferentials

/-! DUB-17/18 -> function-field Riemann--Roch -> global residue identity
-> local residue/derivation compatibility. The actual local coefficient map
is linear, and composing it with the universal differential gives the
uniformizer-coordinate derivation. Pinned composition and integer-power
rules supply its algebraic laws.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

/-- The actual local differential coefficient as a function-field linear map. -/
def differentialCoeffLinearMap : Ω[F⁄K] →ₗ[F] F where
  toFun := v.differentialCoeff
  map_add' ω η := by
    apply v.differentialCoeff_unique
    rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord]
  map_smul' c ω := by
    simpa only [RingHom.id_apply, smul_eq_mul] using v.differentialCoeff_smul c ω

/-- Differentiation with respect to the chosen actual uniformizer. -/
def coordinateDerivation : Derivation K F F :=
  v.differentialCoeffLinearMap.compDer (D K F)

theorem coordinateDerivation_apply (f : F) :
    v.coordinateDerivation f = v.differentialCoeff (D K F f) := rfl

theorem coordinateDerivation_uniformizer : v.coordinateDerivation v.uniformizer = 1 :=
  v.differentialCoeff_dCoord

theorem coordinateDerivation_zpow (n : ℤ) :
    v.coordinateDerivation (v.uniformizer ^ n) = (n : F) * v.uniformizer ^ (n - 1) := by
  simp only [Derivation.leibniz_zpow, v.coordinateDerivation_uniformizer,
    smul_eq_mul, mul_one, zsmul_eq_mul]

end
end Dubon2026.SourceCurve.Place
