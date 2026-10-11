import Dubon2026.MatrixCoefficientPointActions
import Dubon2026.FiniteFreeHopfPointModelEmbedding
import Dubon2026.FiniteFreeHopfPointModelSurjection

/-! # Actual original coefficient maps preserve the appropriate Hopf model constructions -/

namespace Dubon2026
noncomputable section

universe uC
open Matrix

variable {R F K ι A B : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B]

/-- A model of the original representation after an injective coefficient map gives a genuine model of the original representation before that map, using its actual equivariant vector-group embedding. -/
def matrixCoefficientHopfModelOfInjective
    (f : A →+* B) (hf : Function.Injective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ) :=
  finiteFreeHopfPointModelOfInjective m (matrixCoefficientVectorMap f)
    (matrixCoefficientVectorMap_injective f hf) (matrixCoefficientVectorMap_equivariant f ρ)

/-- The genuine original matrix representation inherits an actual model through an injective original coefficient map. -/
theorem matrixCoefficientHopfModel_of_injective_exists
    (f : A →+* B) (hf : Function.Injective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) := by
  exact ⟨matrixCoefficientHopfModelOfInjective f hf ρ m⟩

/-- A surjective original coefficient map gives a model of the actual reduced matrix representation from a model of the original representation, through the genuine kernel quotient. -/
def matrixCoefficientHopfModelOfSurjective [Module.Flat R K]
    (f : A →+* B) (hf : Function.Surjective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ)) :=
  finiteFreeHopfPointModelOfSurjective m (matrixCoefficientVectorMap f)
    (matrixCoefficientVectorMap_surjective f hf) (matrixCoefficientVectorMap_equivariant f ρ)

/-- The actual coefficient reduction of the original matrix representation has a genuine derived Hopf model. -/
theorem matrixCoefficientHopfModel_of_surjective_exists [Module.Flat R K]
    (f : A →+* B) (hf : Function.Surjective f)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρ)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map f).comp ρ))) := by
  exact ⟨matrixCoefficientHopfModelOfSurjective f hf ρ m⟩

end
end Dubon2026
