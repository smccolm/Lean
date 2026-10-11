import Dubon2026.MatrixConjugacyHopfModels
import Dubon2026.MatrixFiberProductHopfModel
import Dubon2026.ContinuousStrictConjugacyGluing

/-! # Genuine finite free models under continuous strict-conjugacy gluing -/

namespace Dubon2026
noncomputable section

universe uC uD
open Matrix

variable {R F K ι A B C k : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Fintype ι] [DecidableEq ι] [CommRing A] [CommRing B] [CommRing C] [CommRing k]
  [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

/-- Glue the actual continuous representations and construct a genuine finite free model of the resulting original coefficient fiber product. The supplied models concern the two original representations, while strict conjugacy and the compatible-vector embedding derive the new model. -/
theorem continuousCoefficientFiberProductHopfModel_exists
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g) [IsLocalHom g]
    (rC : C →+* k)
    (ρA : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι A)
    (ρB : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι B)
    (h : MatrixStrictlyConjugate rC
      ((GeneralLinearGroup.map g).comp ρB.toMonoidHom)
      ((GeneralLinearGroup.map f).comp ρA.toMonoidHom))
    (mA : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ρA.toMonoidHom))
    (mB : FiniteFreeHopfPointModel.{_, _, _, _, uD} R F K (Multiplicative (ι → B))
      (matrixUnderlyingGroupAction ρB.toMonoidHom)) :
    ∃ ρ : (K ≃ₐ[F] K) →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom =
        ρA.toMonoidHom ∧
      MatrixStrictlyConjugate (rC.comp g) ρB.toMonoidHom
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom) ∧
      Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, max uC uD} R F K (Multiplicative (ι → CoefficientFiberProduct f g))
        (matrixUnderlyingGroupAction ρ.toMonoidHom)) := by
  obtain ⟨ρ, hA, hB⟩ :=
    continuousCoefficientFiberProduct_exists_of_strictlyConjugate f g hg rC ρA ρB h
  have hmodelA : Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative (ι → A))
      (matrixUnderlyingGroupAction ((GeneralLinearGroup.map
        (coefficientFiberProductFst f g)).comp ρ.toMonoidHom))) := by
    rw [hA]
    exact ⟨mA⟩
  have hmodelB := (matrixHopfModel_strictConjugacy_iff (R := R) (rC.comp g)
    ρB.toMonoidHom _ hB).mp ⟨mB⟩
  obtain ⟨mA'⟩ := hmodelA
  obtain ⟨mB'⟩ := hmodelB
  exact ⟨ρ, hA, hB, matrixFiberProductHopfModel_exists f g ρ.toMonoidHom mA' mB'⟩

end
end Dubon2026
