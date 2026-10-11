import Dubon2026.MatrixFiberProductPointEmbedding
import Dubon2026.FiniteFreeHopfPointModelEmbedding

/-! # Actual Hopf models for original coefficient fiber-product representations -/

namespace Dubon2026
noncomputable section

universe uC uD
open Matrix

variable {R F K ι A B C : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C]

/-- Models for both original projected representations construct a model of the original representation over the genuine coefficient fiber product. The tensor-coordinate product model and the actual compatible-vector embedding supply its subgroup coordinate model. -/
def matrixFiberProductHopfModel (f : A →+* C) (g : B →+* C)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (mA : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductFst f g)).comp ρ)))
    (mB : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductSnd f g)).comp ρ))) :
    FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → CoefficientFiberProduct f g))
      (matrixUnderlyingGroupAction ρ) :=
  finiteFreeHopfPointModelOfInjective (finiteFreeHopfPointModelProduct mA mB)
    (matrixFiberProductVectorMap f g) (matrixFiberProductVectorMap_injective f g)
    (matrixFiberProductVectorMap_equivariant f g ρ)

/-- The actual original fiber-product coefficient representation has a genuine model whenever both of its original projections do. This derives the original model without assuming it. -/
theorem matrixFiberProductHopfModel_exists (f : A →+* C) (g : B →+* C)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (mA : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductFst f g)).comp ρ)))
    (mB : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductSnd f g)).comp ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → CoefficientFiberProduct f g))
      (matrixUnderlyingGroupAction ρ)) := by
  exact ⟨matrixFiberProductHopfModel f g ρ mA mB⟩

end
end Dubon2026
