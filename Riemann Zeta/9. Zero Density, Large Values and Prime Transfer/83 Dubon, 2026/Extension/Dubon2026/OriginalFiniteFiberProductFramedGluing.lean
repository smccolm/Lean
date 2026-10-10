import Dubon2026.CoefficientFiberProductResidueCompatibility
import Dubon2026.FiniteCoefficientFiberProductTopology
import Dubon2026.ContinuousStrictConjugacyGluing
import Dubon2026.OriginalUnframedDeformationClasses

/-! # Genuine finite-coefficient fiber-product gluing in the original continuous fixed-residue fiber -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C]

private def originalFiberOfHom {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra O R] [WithIdeal R]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ : H →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (hres : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ) :
    OriginalContinuousFramedFiber eR H σ := ⟨⟨ρ, hρ⟩, hres⟩

private theorem originalFiberOfHom_toMonoidHom {R : Type} [CommRing R] [IsLocalRing R]
    [Algebra O R] [WithIdeal R]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (H : ProfiniteGrp) (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ : H →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (hres : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp ρ = σ) :
    (originalFiberOfHom eR H σ ρ hρ hres).val.toMonoidHom = ρ := rfl

omit [IsLocalRing O] [IsLocalRing C] in
private theorem fiberProduct_adic_continuous {G : Type} [Group G] [TopologicalSpace G]
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (ρ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f.toRingHom g.toRingHom))
    (hρ : Continuous ρ) :
    (letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     @Continuous G (GeneralLinearGroup ι (CoefficientFiberProduct f.toRingHom g.toRingHom)) _
       (letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
          (IsLocalRing.maximalIdeal _).adicTopology
        inferInstance) ρ) := by
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  rw [finiteCoefficientFiberProduct_original_adicTopology_eq_product hA hB f.toRingHom g.toRingHom]
  exact hρ

omit [WithIdeal A] [Finite A] [IsLocalRing B] [WithIdeal B] [Finite B] [IsLocalRing C] in
private theorem fiberProduct_original_residue {G : Type} [Group G]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (ρ : G →* GeneralLinearGroup ι (CoefficientFiberProduct f.toRingHom g.toRingHom))
    (σ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (h : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      ((GeneralLinearGroup.map (coefficientFiberProductFst f.toRingHom g.toRingHom)).comp ρ) = σ) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     (GeneralLinearGroup.map
       (localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA)).toRingHom).comp
       ρ = σ) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  rw [coefficientFiberProductReduction_fst f g hg eA]
  exact h

/-- Actual original continuous fixed-residue lifts whose common reductions are strictly conjugate glue over the genuine finite coefficient fiber product with its true original residue field and maximal-adic topology. The first whole projection is exact and the second remains in the original strict class. -/
theorem originalFiniteFiberProductFramed_exists
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρA : OriginalContinuousFramedFiber eA H σ)
    (ρB : OriginalContinuousFramedFiber eB H σ)
    (h : MatrixStrictlyConjugate (localCoefficientReduction eC).toRingHom
      ((GeneralLinearGroup.map g.toRingHom).comp ρB.val.toMonoidHom)
      ((GeneralLinearGroup.map f.toRingHom).comp ρA.val.toMonoidHom)) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       ⟨IsLocalRing.maximalIdeal _⟩
     letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       (IsLocalRing.maximalIdeal _).adicTopology
     ∃ ρ : OriginalContinuousFramedFiber (coefficientFiberProductResidueEquiv f g hg eA) H σ,
       (GeneralLinearGroup.map (coefficientFiberProductFst f.toRingHom g.toRingHom)).comp
           ρ.val.toMonoidHom = ρA.val.toMonoidHom ∧
       MatrixStrictlyConjugate (localCoefficientReduction eB).toRingHom ρB.val.toMonoidHom
         ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp
           ρ.val.toMonoidHom)) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  obtain ⟨ρ, hρA, hρB⟩ := continuousCoefficientFiberProduct_exists_of_strictlyConjugate
    f.toRingHom g.toRingHom hg (localCoefficientReduction eC).toRingHom ρA.val ρB.val h
  let ρhom : H →* GeneralLinearGroup ι (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ρ.toMonoidHom
  have hcts := fiberProduct_adic_continuous hA hB f g ρhom ρ.continuous
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  have hres : (GeneralLinearGroup.map
      (localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA)).toRingHom).comp
      ρhom = σ := by
    apply fiberProduct_original_residue eA f g hg ρhom σ
    rw [hρA]
    exact ρA.property
  refine ⟨originalFiberOfHom (coefficientFiberProductResidueEquiv f g hg eA) H σ
    ρhom hcts hres, ?_, ?_⟩
  · rw [originalFiberOfHom_toMonoidHom]
    exact hρA
  · rw [originalFiberOfHom_toMonoidHom]
    change MatrixStrictlyConjugate ((localCoefficientReduction eC).comp g).toRingHom
      ρB.val.toMonoidHom
      ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp
        ρhom) at hρB
    rw [hgres] at hρB
    exact hρB

end
end Dubon2026
