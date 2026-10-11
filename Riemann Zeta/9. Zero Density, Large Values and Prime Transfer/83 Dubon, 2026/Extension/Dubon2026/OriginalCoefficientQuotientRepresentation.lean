import Dubon2026.OriginalCoefficientRepresentationClass
import Dubon2026.LocalQuotientCoefficientFibers

/-! # The original continuous representation on its actual coefficient quotient -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {ι O A : Type u} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [CommRing A] [IsLocalRing A] [Algebra O A]
  [TopologicalSpace A] [IsTopologicalRing A]

/-- Reduce the same original continuous matrices through the actual ideal quotient
with its original quotient topology. Continuity follows from the actual quotient map. -/
def originalCoefficientQuotientRepresentation
    (H : ProfiniteGrp.{u}) (τ : H →ₜ* GeneralLinearGroup ι A) (J : Ideal A) :
    H →ₜ* GeneralLinearGroup ι (A ⧸ J) := by
  have hmap : Continuous (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk J)) := by
    apply Units.continuous_map
    apply continuous_matrix
    intro i j
    exact (QuotientRing.isOpenQuotientMap_mk J).continuous.comp (continuous_apply_apply i j)
  exact ⟨(GeneralLinearGroup.map (Ideal.Quotient.mk J)).comp τ.toMonoidHom,
    hmap.comp τ.continuous⟩

/-- The true original residue of the quotient representation is the same entire
residual representation, through the original local quotient residue equivalence. -/
theorem originalCoefficientQuotientRepresentation_residue
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) (J : Ideal A) [IsLocalRing (A ⧸ J)] :
    (GeneralLinearGroup.map (localCoefficientReduction
      (originalLocalQuotientResidueEquiv eA J)).toRingHom).comp
        (originalCoefficientQuotientRepresentation H τ J).toMonoidHom = σ := by
  apply MonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact (originalLocalQuotientResidueEquiv_original eA J ((τ g).val i j)).trans
    (congrArg (fun U : GeneralLinearGroup ι (IsLocalRing.ResidueField O) => U.val i j)
      (DFunLike.congr_fun hτ g))

variable {B : Type u} [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B]

/-- Evaluating the original quotient representation equals evaluating the original
representation through the same restricted quotient coefficient map, as an equality
of the actual original unframed deformation classes. -/
theorem originalCoefficientQuotientRepresentation_class
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp.{u}) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (τ : H →ₜ* GeneralLinearGroup ι A)
    (hτ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      τ.toMonoidHom = σ) (J : Ideal A) [IsLocalRing (A ⧸ J)]
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eA J) eB) :
    originalCoefficientRepresentationClass (originalLocalQuotientResidueEquiv eA J) eB H σ
        (originalCoefficientQuotientRepresentation H τ J)
        (originalCoefficientQuotientRepresentation_residue eA H σ τ hτ J) f =
      originalCoefficientRepresentationClass eA eB H σ τ hτ
        (originalQuotientCoefficientRestriction eA eB J f).val := by
  apply congrArg (originalUnframedClass eB H σ)
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro g
  rfl

end
end Dubon2026
