import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer-cover genus and the
genus inequality for extending reductions. The original finite coordinate
remains finite after the actual Kummer field extension, with its exact degree.
Native intermediate-field equivalences and tower dimensions suffice.
Adapted from the coordinate-degree argument in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

theorem finrank_adjoin_algebraMap_mul
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E] (x : F) :
    Module.finrank K⟮algebraMap F E x⟯ E =
      Module.finrank K⟮x⟯ F * Module.finrank F E := by
  let φ : F →ₐ[K] E := IsScalarTower.toAlgHom K F E
  have hmap : K⟮x⟯.map φ = K⟮algebraMap F E x⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : K⟮x⟯ ≃ₐ[K] K⟮algebraMap F E x⟯ :=
    (IntermediateField.equivMap K⟮x⟯ φ).trans (IntermediateField.equivOfEq hmap)
  have he : ∀ y : K⟮x⟯, ((e y : K⟮algebraMap F E x⟯) : E) =
      algebraMap F E (y : F) := fun _ => rfl
  have h1 : Module.finrank K⟮x⟯ E = Module.finrank K⟮algebraMap F E x⟯ E :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl E)
      (RingHom.ext fun y => (he y).symm)
  rw [← h1, Module.finrank_mul_finrank]

end
end Dubon2026.SourceCurve
