import Dubon2026.OriginalCoefficientFiberProductClasses
import Dubon2026.OriginalFramedTrueResidueTransport
import Dubon2026.CoefficientFiberProductConjugatorAlignment

/-! # Genuine original deformation classes are determined by their coefficient projections -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O A B C L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [Finite A]
  [CommRing B] [IsLocalRing B] [Algebra O B] [WithIdeal B] [Finite B]
  [CommRing C] [IsLocalRing C] [Algebra O C]
  [Field L] [Algebra (IsLocalRing.ResidueField C) L] [IsAlgClosed L]

/-- For an actual absolutely irreducible original residual representation, equality of both projected original unframed classes forces equality of the original fiber-product classes. The stabilizer-lifting hypothesis is derived from the literal fixed-residue condition of the original whole framed lift. -/
theorem originalCoefficientFiberProductClass_projections_injective
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
    Function.Injective (fun q : OriginalCoefficientFiberProductClass eA f g hg H σ =>
      (originalCoefficientFiberProductClassFst hA hB eA f g hg H σ q,
       originalCoefficientFiberProductClassSnd hA hB eA eB eC f g hg hfres hgres H σ q)) := by
  letI := coefficientFiberProductAlgebra f g
  letI := coefficientFiberProduct_isLocalRing f.toRingHom g.toRingHom
  letI : WithIdeal (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    ⟨IsLocalRing.maximalIdeal _⟩
  letI : TopologicalSpace (CoefficientFiberProduct f.toRingHom g.toRingHom) :=
    (IsLocalRing.maximalIdeal _).adicTopology
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro ρ τ h
  have hfirst := (originalCoefficientFiberProductClassFst_eq_iff hA hB eA f g hg H σ ρ τ).mp
    (congrArg Prod.fst h)
  have hsecond := (originalCoefficientFiberProductClassSnd_eq_iff
    hA hB eA eB eC f g hg hfres hgres H σ ρ τ).mp (congrArg Prod.snd h)
  have hresg : (localCoefficientReduction eC).comp (g.comp (coefficientFiberProductSndAlgHom f g)) =
      localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA) := by
    apply AlgHom.ext
    intro x
    exact (DFunLike.congr_fun hgres ((coefficientFiberProductSndAlgHom f g) x)).trans
      (DFunLike.congr_fun (coefficientFiberProductReduction_snd eA eB eC f g hg hfres hgres) x).symm
  have htrue := originalFramedFiber_coefficient_trueResidue
    (coefficientFiberProductResidueEquiv f g hg eA) eC
    (g.comp (coefficientFiberProductSndAlgHom f g)) hresg H σ ρ
  change (GeneralLinearGroup.map (IsLocalRing.residue C)).comp
      ((GeneralLinearGroup.map g.toRingHom).comp
        ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp
          ρ.val.toMonoidHom)) = (GeneralLinearGroup.map eC.symm.toRingHom).comp σ at htrue
  letI : Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L)
        ((GeneralLinearGroup.map (IsLocalRing.residue C)).comp
          ((GeneralLinearGroup.map g.toRingHom).comp
            ((GeneralLinearGroup.map (coefficientFiberProductSnd f.toRingHom g.toRingHom)).comp
              ρ.val.toMonoidHom))))) := by
    rw [htrue]
    infer_instance
  have hstrict := matrixStrictlyConjugate_fiberProduct_of_projections (L := L)
    f.toRingHom g.toRingHom hg ρ.val.toMonoidHom τ.val.toMonoidHom
    (localCoefficientReduction eA).toRingHom (localCoefficientReduction eB).toRingHom hfirst hsecond
  apply Quotient.sound
  change MatrixStrictlyConjugate
    (localCoefficientReduction (coefficientFiberProductResidueEquiv f g hg eA)).toRingHom
    ρ.val.toMonoidHom τ.val.toMonoidHom
  have hred := congrArg AlgHom.toRingHom (coefficientFiberProductReduction_fst f g hg eA)
  exact (congrArg (fun r : CoefficientFiberProduct f.toRingHom g.toRingHom →+*
      IsLocalRing.ResidueField O =>
    MatrixStrictlyConjugate r ρ.val.toMonoidHom τ.val.toMonoidHom) hred).mpr hstrict

end
end Dubon2026
