import Dubon2026.CoefficientFiberProductResidueCompatibility
import Dubon2026.FiniteCoefficientFiberProductProjectionTopology
import Dubon2026.OriginalUnframedDeformationNaturality

/-! # Actual original unframed classes over the coefficient fiber product and their genuine projections -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O A B C : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C]

/-- The existing original continuous framed fiber on the actual coefficient fiber product, with its true residue and actual maximal-adic topology. -/
abbrev OriginalCoefficientFiberProductFramedFiber
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g) (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  OriginalContinuousFramedFiber (coefficientFiberProductResidueEquiv f g hg eA) H σ

/-- The existing genuine original strict deformation quotient on that same coefficient fiber product. -/
abbrev OriginalCoefficientFiberProductClass
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g) (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :=
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  OriginalUnframedDeformationClass (coefficientFiberProductResidueEquiv f g hg eA) H σ

/-- The actual first continuous original coefficient projection acts on the genuine original unframed classes. -/
def originalCoefficientFiberProductClassFst
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g) (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) :
    OriginalCoefficientFiberProductClass eA f g hg H σ → OriginalUnframedDeformationClass eA H σ := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  exact originalUnframedPostcomp (coefficientFiberProductResidueEquiv f g hg eA) eA H σ
    (coefficientFiberProductFstAlgHom f g)
    (finiteCoefficientFiberProductFst_adic_continuous hA hB f.toRingHom g.toRingHom)
    (coefficientFiberProductReduction_fst f g hg eA).symm

/-- The actual second continuous residue-preserving original projection acts on the same genuine original unframed classes. -/
def originalCoefficientFiberProductClassSnd
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
    OriginalCoefficientFiberProductClass eA f g hg H σ → OriginalUnframedDeformationClass eB H σ := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  exact originalUnframedPostcomp (coefficientFiberProductResidueEquiv f g hg eA) eB H σ
    (coefficientFiberProductSndAlgHom f g)
    (finiteCoefficientFiberProductSnd_adic_continuous hA hB f.toRingHom g.toRingHom)
    (coefficientFiberProductReduction_snd eA eB eC f g hg hfres hgres).symm

omit [IsLocalRing C] in
/-- Equality of the actual first projected original classes is exactly strict conjugacy of their entire genuine first projected representations. -/
theorem originalCoefficientFiberProductClassFst_eq_iff
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g) (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ τ : OriginalCoefficientFiberProductFramedFiber eA f g hg H σ) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       ⟨IsLocalRing.maximalIdeal _⟩
     letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       (IsLocalRing.maximalIdeal _).adicTopology
     originalCoefficientFiberProductClassFst hA hB eA f g hg H σ
         (originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ ρ) =
       originalCoefficientFiberProductClassFst hA hB eA f g hg H σ
         (originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ τ) ↔
     MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
       ((GeneralLinearGroup.map (coefficientFiberProductFst f.toRingHom g.toRingHom)).comp ρ.val.toMonoidHom)
       ((GeneralLinearGroup.map (coefficientFiberProductFst f.toRingHom g.toRingHom)).comp τ.val.toMonoidHom)) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  exact originalUnframedClass_eq_iff eA H σ
    (originalFramedFiberPostcomp (coefficientFiberProductResidueEquiv f g hg eA) eA H σ
      (coefficientFiberProductFstAlgHom f g)
      (finiteCoefficientFiberProductFst_adic_continuous hA hB f.toRingHom g.toRingHom)
      (coefficientFiberProductReduction_fst f g hg eA).symm ρ)
    (originalFramedFiberPostcomp (coefficientFiberProductResidueEquiv f g hg eA) eA H σ
      (coefficientFiberProductFstAlgHom f g)
      (finiteCoefficientFiberProductFst_adic_continuous hA hB f.toRingHom g.toRingHom)
      (coefficientFiberProductReduction_fst f g hg eA).symm τ)


/-- Equality of the actual second projected original classes is exactly strict conjugacy of their entire genuine second projected representations. -/
theorem originalCoefficientFiberProductClassSnd_eq_iff
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (eB : IsLocalRing.ResidueField B ≃ₐ[O] IsLocalRing.ResidueField O)
    (eC : IsLocalRing.ResidueField C ≃ₐ[O] IsLocalRing.ResidueField O)
    (f : A →ₐ[O] C) (g : B →ₐ[O] C) [IsLocalHom g.toRingHom]
    (hg : Function.Surjective g)
    (hfres : (localCoefficientReduction eC).comp f = localCoefficientReduction eA)
    (hgres : (localCoefficientReduction eC).comp g = localCoefficientReduction eB)
    (H : ProfiniteGrp)
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (ρ τ : OriginalCoefficientFiberProductFramedFiber eA f g hg H σ) :
    (letI := coefficientFiberProductAlgebra f g
     letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
     letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       ⟨IsLocalRing.maximalIdeal _⟩
     letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
       (IsLocalRing.maximalIdeal _).adicTopology
     originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ
         (originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ ρ) =
       originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ
         (originalUnframedClass (coefficientFiberProductResidueEquiv f g hg eA) H σ τ) ↔
     MatrixStrictlyConjugate (localCoefficientReduction eB).toRingHom
       ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp ρ.val.toMonoidHom)
       ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp τ.val.toMonoidHom)) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  exact originalUnframedClass_eq_iff eB H σ
    (originalFramedFiberPostcomp (coefficientFiberProductResidueEquiv f g hg eA) eB H σ
      (coefficientFiberProductSndAlgHom f g)
      (finiteCoefficientFiberProductSnd_adic_continuous hA hB f.toRingHom g.toRingHom)
      (coefficientFiberProductReduction_snd eA eB eC f g hg hfres hgres).symm ρ)
    (originalFramedFiberPostcomp (coefficientFiberProductResidueEquiv f g hg eA) eB H σ
      (coefficientFiberProductSndAlgHom f g)
      (finiteCoefficientFiberProductSnd_adic_continuous hA hB f.toRingHom g.toRingHom)
      (coefficientFiberProductReduction_snd eA eB eC f g hg hfres hgres).symm τ)

end
end Dubon2026
