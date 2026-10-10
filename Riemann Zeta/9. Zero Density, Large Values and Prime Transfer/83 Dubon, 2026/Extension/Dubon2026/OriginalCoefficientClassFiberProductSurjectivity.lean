import Dubon2026.OriginalCoefficientClassFiberProduct
import Dubon2026.OriginalFiniteFiberProductFramedGluing

/-! # Actual surjectivity and bijectivity of the original deformation-class fiber-product map -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]

/-- Every genuinely compatible pair of original strict deformation classes is the pair of projections of an actual original deformation class over the coefficient fiber product. -/
theorem originalCoefficientClassFiberProductMap_surjective
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    Function.Surjective (originalCoefficientClassFiberProductMap hA hB eA eB eC f g hg hfres hgres H σ) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  rintro ⟨⟨qA, qB⟩, hq⟩
  obtain ⟨ρA, rfl⟩ := originalUnframedClass_surjective eA H σ qA
  obtain ⟨ρB, rfl⟩ := originalUnframedClass_surjective eB H σ qB
  have hcommon : MatrixStrictlyConjugate (localCoefficientReduction eC).toRingHom
      ((GeneralLinearGroup.map f.toRingHom).comp ρA.val.toMonoidHom)
      ((GeneralLinearGroup.map g.toRingHom).comp ρB.val.toMonoidHom) :=
    (originalUnframedClass_eq_iff eC H σ
      (originalFramedFiberPostcomp eA eC H σ f (finiteOriginalCoefficientHom_continuous hA f) hfres ρA)
      (originalFramedFiberPostcomp eB eC H σ g (finiteOriginalCoefficientHom_continuous hB g) hgres ρB)).mp hq
  have hreverse := matrixStrictlyConjugate_symm (localCoefficientReduction eC).toRingHom
    _ _ hcommon
  obtain ⟨ρ, hρA, hρB⟩ := originalFiniteFiberProductFramed_exists
    hA hB eA eB eC f g hg hgres H σ ρA ρB hreverse
  refine ⟨originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ ρ, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Quotient.sound
    change MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
      ((GeneralLinearGroup.map (coefficientFiberProductFst f.toRingHom g.toRingHom)).comp
        ρ.val.toMonoidHom) ρA.val.toMonoidHom
    exact (congrArg (fun μ : H →* GeneralLinearGroup ι A =>
      MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom μ ρA.val.toMonoidHom)
        hρA).mpr (matrixStrictlyConjugate_refl (localCoefficientReduction eA).toRingHom ρA.val.toMonoidHom)
  · apply Quotient.sound
    change MatrixStrictlyConjugate (localCoefficientReduction eB).toRingHom
      ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp
        ρ.val.toMonoidHom) ρB.val.toMonoidHom
    exact matrixStrictlyConjugate_symm (localCoefficientReduction eB).toRingHom _ _ hρB

/-- For the actual original absolutely irreducible residual representation, the genuine original deformation classes commute bijectively with this actual finite coefficient fiber product. -/
theorem originalCoefficientClassFiberProductMap_bijective {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((GeneralLinearGroup.map eC.symm.toRingHom).comp σ)))] :
    Function.Bijective (originalCoefficientClassFiberProductMap hA hB eA eB eC f g hg hfres hgres H σ) :=
  ⟨originalCoefficientClassFiberProductMap_injective (L := L) hA hB eA eB eC f g hg hfres hgres H σ,
    originalCoefficientClassFiberProductMap_surjective hA hB eA eB eC f g hg hfres hgres H σ⟩

/-- The actual canonical class map, now as an equivalence between the genuine original class of the coefficient fiber product and the genuine fiber product of original classes. -/
def originalCoefficientClassFiberProductEquiv {L : Type} [Field L]
    [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) ((GeneralLinearGroup.map eC.symm.toRingHom).comp σ)))] :
    OriginalCoefficientFiberProductClass eA f g hg H σ ≃
      OriginalCoefficientClassFiberProduct hA hB eA eB eC f g hfres hgres H σ :=
  Equiv.ofBijective (originalCoefficientClassFiberProductMap hA hB eA eB eC f g hg hfres hgres H σ)
    (originalCoefficientClassFiberProductMap_bijective (L := L) hA hB eA eB eC f g hg hfres hgres H σ)

end
end Dubon2026
