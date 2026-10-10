import Dubon2026.MatrixCoefficientFiberProduct
import Dubon2026.MatrixRepresentationStrictConjugacy

/-! # Gluing actual compatible strict changes of basis over the original coefficient fiber product -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A B C K : Type} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing A] [CommRing B] [CommRing C] [CommRing K]

/-- Actual compatible original changes of basis glue to a strict conjugacy of the whole representations over the genuine coefficient fiber product. -/
theorem matrixStrictlyConjugate_fiberProduct_of_compatible_conjugators
    (f : A →+* C) (g : B →+* C) (rA : A →+* K)
    (ρ σ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f g))
    (U : GeneralLinearGroup ι A) (V : GeneralLinearGroup ι B)
    (hUV : GeneralLinearGroup.map f U = GeneralLinearGroup.map g V)
    (hU : GeneralLinearGroup.map rA U = 1)
    (hA : ∀ x, GeneralLinearGroup.map (coefficientFiberProductFst f g) (σ x) =
      U * GeneralLinearGroup.map (coefficientFiberProductFst f g) (ρ x) * U⁻¹)
    (hB : ∀ x, GeneralLinearGroup.map (coefficientFiberProductSnd f g) (σ x) =
      V * GeneralLinearGroup.map (coefficientFiberProductSnd f g) (ρ x) * V⁻¹) :
    MatrixStrictlyConjugate (rA.comp (coefficientFiberProductFst f g)) ρ σ := by
  obtain ⟨W, hW, _⟩ := generalLinearCoefficientFiberProduct_existsUnique f g U V hUV
  refine ⟨W, ?_, ?_⟩
  · rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hW.1]
    exact hU
  · intro x
    apply generalLinearCoefficientFiberProduct_ext f g
    · simpa only [map_mul, map_inv, hW.1] using hA x
    · simpa only [map_mul, map_inv, hW.2] using hB x

end
end Dubon2026
