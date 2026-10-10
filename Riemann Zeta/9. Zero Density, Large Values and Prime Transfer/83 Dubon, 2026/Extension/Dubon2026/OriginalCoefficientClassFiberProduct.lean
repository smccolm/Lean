import Dubon2026.FiniteOriginalCoefficientClassMaps
import Dubon2026.OriginalCoefficientFiberProductClassInjectivity

/-! # The genuine fiber product of original deformation classes and its actual canonical map -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C] [WithIdeal C]

/-- The actual compatible pairs of original strict deformation classes, using the genuine original coefficient-change maps to the common coefficient algebra. -/
abbrev OriginalCoefficientClassFiberProduct
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  {q : OriginalUnframedDeformationClass eA H σ × OriginalUnframedDeformationClass eB H σ //
    finiteOriginalUnframedPostcomp hA eA eC H σ f hfres q.1 =
      finiteOriginalUnframedPostcomp hB eB eC H σ g hgres q.2}

/-- The two genuine projected original deformation classes have exactly the same original class over the common coefficient algebra. -/
theorem originalCoefficientFiberProductClass_projections_compatible
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
    (q : OriginalCoefficientFiberProductClass eA f g hg H σ) :
    finiteOriginalUnframedPostcomp hA eA eC H σ f hfres
      (originalCoefficientFiberProductClassFst hA hB eA f g hg H σ q) =
    finiteOriginalUnframedPostcomp hB eB eC H σ g hgres
      (originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ q) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  refine Quotient.inductionOn q ?_
  intro ρ
  apply congrArg (originalUnframedClass eC H σ)
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro x
  apply Units.ext
  apply Matrix.ext
  intro i j
  change f (((ρ.val x).val i j).val.1) = g (((ρ.val x).val i j).val.2)
  exact ((ρ.val x).val i j).property

/-- Send each actual original deformation class over the genuine coefficient fiber product to its compatible pair of actual original projected classes. -/
def originalCoefficientClassFiberProductMap
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
    (q : OriginalCoefficientFiberProductClass eA f g hg H σ) :
    OriginalCoefficientClassFiberProduct hA hB eA eB eC f g hfres hgres H σ :=
  ⟨(originalCoefficientFiberProductClassFst hA hB eA f g hg H σ q,
      originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ q),
    originalCoefficientFiberProductClass_projections_compatible hA hB eA eB eC f g hg hfres hgres H σ q⟩

/-- The actual canonical map to the genuine fiber product of original classes is injective for the actual original absolutely irreducible residual representation. -/
theorem originalCoefficientClassFiberProductMap_injective {L : Type} [Field L]
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
    Function.Injective (originalCoefficientClassFiberProductMap hA hB eA eB eC f g hg hfres hgres H σ) := by
  intro q τ h
  apply originalCoefficientFiberProductClass_projections_injective (L := L)
    hA hB eA eB eC f g hg hfres hgres H σ
  exact congrArg Subtype.val h

end
end Dubon2026
