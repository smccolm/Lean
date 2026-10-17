import Dubon2026.OriginalInternalHomPrecomposition
import Dubon2026.OriginalCoinducedInternalHomIso
import Dubon2026.OriginalCoinducedInvariantNorms
import Dubon2026.OriginalInternalHomNormQuotient

/-! # Compose and lift actual coefficient norms

The reverse chase for DUB-17's two-shift norm criterion uses only
literal internal-Hom norms, their functoriality, and the already
proved coinduced internal-Hom isomorphism.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module
variable {G : Type} [Group G] [Fintype G]
variable {A B C : Rep.{0} ℤ G}

/-- Postcomposition carries the original sum-of-conjugates morphism to the norm of the postcomposed linear map. -/
theorem originalCoefficientNorm_postcomp (η : A →ₗ[ℤ] B) (f : B ⟶ C) :
    originalCoefficientNormMorphism A B η ≫ f =
      originalCoefficientNormMorphism A C (f.hom.toLinearMap.comp η) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact ((congrArg (fun t : (Rep.ihom A).obj B => ((Rep.ihom A).map f).hom t)
    (originalInternalHom_norm_eq_coefficientNorm A B η)).symm.trans
      (originalCoefficientMorphism_norm ((Rep.ihom A).map f) η)).trans
        (originalInternalHom_norm_eq_coefficientNorm A C (f.hom.toLinearMap.comp η))

/-- Precomposition carries the original sum-of-conjugates morphism to the norm of the precomposed linear map. -/
theorem originalCoefficientNorm_precomp (f : A ⟶ B) (η : B →ₗ[ℤ] C) :
    f ≫ originalCoefficientNormMorphism B C η =
      originalCoefficientNormMorphism A C (η.comp f.hom.toLinearMap) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  exact ((congrArg (fun t : (Rep.ihom B).obj C => (originalInternalHomPrecomposition C f).hom t)
    (originalInternalHom_norm_eq_coefficientNorm B C η)).symm.trans
      (originalCoefficientMorphism_norm (originalInternalHomPrecomposition C f) η)).trans
        (originalInternalHom_norm_eq_coefficientNorm A C (η.comp f.hom.toLinearMap))

/-- Every actual coefficient morphism from the original coinduced source has a literal norm witness. -/
theorem originalCoinducedSource_norm_witness (M C : Rep.{0} ℤ G)
    (f : originalCoinducedFunctionRep M ⟶ C) :
    ∃ η : originalCoinducedFunctionRep M →ₗ[ℤ] C,
      originalCoefficientNormMorphism (originalCoinducedFunctionRep M) C η = f := by
  let e := originalCoinducedInternalHomIso M C
  obtain ⟨η, hη⟩ := originalInvariantNorm_preimages_of_retract e.hom e.inv e.hom_inv_id
    (originalCoinducedInvariant_norm_preimages (originalInternalHomPointRep M C))
    f.hom.toLinearMap (originalMorphism_internalHom_invariant _ _ f)
  refine ⟨η, Rep.hom_ext (Representation.IntertwiningMap.ext ?_)⟩
  exact (originalInternalHom_norm_eq_coefficientNorm _ _ η).symm.trans hη

end
end Dubon2026
