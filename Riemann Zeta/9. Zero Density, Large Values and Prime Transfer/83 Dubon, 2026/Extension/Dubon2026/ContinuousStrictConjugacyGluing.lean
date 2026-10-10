import Dubon2026.ContinuousCoefficientFiberProduct
import Dubon2026.LocalCoefficientMatrixLifting
import Dubon2026.MatrixRepresentationConjugation

/-! # Gluing whole continuous original representations from strictly conjugate common reductions -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B C K : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C] [CommRing K]
  [TopologicalSpace G] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing B]

/-- Lift the actual common strict conjugator, conjugate the whole second continuous representation, and glue the resulting equal reductions over the original coefficient fiber product. The first projection is exact and the second belongs to the supplied original strict-conjugacy class. -/
theorem continuousCoefficientFiberProduct_exists_of_strictlyConjugate
    (f : A →+* C) (g : B →+* C) (hg : Function.Surjective g) [IsLocalHom g]
    (rC : C →+* K)
    (ρA : G →ₜ* GeneralLinearGroup ι A) (ρB : G →ₜ* GeneralLinearGroup ι B)
    (h : MatrixStrictlyConjugate rC
      ((GeneralLinearGroup.map g).comp ρB.toMonoidHom)
      ((GeneralLinearGroup.map f).comp ρA.toMonoidHom)) :
    ∃ ρ : G →ₜ* GeneralLinearGroup ι (CoefficientFiberProduct f g),
      (GeneralLinearGroup.map (coefficientFiberProductFst f g)).comp ρ.toMonoidHom =
        ρA.toMonoidHom ∧
      MatrixStrictlyConjugate (rC.comp g) ρB.toMonoidHom
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f g)).comp ρ.toMonoidHom) := by
  obtain ⟨W, hW, hconj⟩ := h
  obtain ⟨V, hV, hVr⟩ := generalLinearGroup_strict_lift g hg (rC.comp g) rC rfl W hW
  let τB : G →ₜ* GeneralLinearGroup ι B :=
    ⟨matrixRepresentationConjugate ρB.toMonoidHom V,
      matrixRepresentationConjugate_continuous ρB.toMonoidHom ρB.continuous V⟩
  have hcompatible : (GeneralLinearGroup.map f).comp ρA.toMonoidHom =
      (GeneralLinearGroup.map g).comp τB.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change GeneralLinearGroup.map f (ρA x) = GeneralLinearGroup.map g (V * ρB x * V⁻¹)
    rw [map_mul, map_mul, map_inv, hV]
    exact hconj x
  obtain ⟨ρ, hρ, _⟩ := continuousCoefficientFiberProductRepresentation_existsUnique f g ρA τB hcompatible
  refine ⟨ρ, hρ.1, ?_⟩
  rw [hρ.2]
  exact matrixStrictlyConjugate_conjugate (rC.comp g) ρB.toMonoidHom V hVr

end
end Dubon2026
