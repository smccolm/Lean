import Dubon2026.PolarizedFramedFiberEquivalence
import Dubon2026.PolarizedAlgebraCoefficientCriterion
import Dubon2026.LocalQuotientCoefficientFibers

/-! Restriction of the proved original matrix classification by the literal
polarized ideal, with exact matrix evaluation. The actual native framed
coefficient ring supplies the matrix classification in the DUB-17 consumer. -/

namespace Dubon2026
open Matrix
noncomputable section

universe u
variable {ι O R A : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [CommRing O] [IsLocalRing O]
  [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A] [CompactSpace A] [T2Space A]
  (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
  (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
  (H : ProfiniteGrp.{u}) (σ : H →* PolarizedGaloisGroup ι (IsLocalRing.ResidueField O))
  (ν : H →* Oˣ) (τ : H →* GeneralLinearGroup (ι ⊕ ι) R)


variable [hQ : IsLocalRing (R ⧸ (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν)))]
  (F : OriginalContinuousCoefficientFiber eR eA ≃
    OriginalContinuousFramedFiber eA H (polarizedBlockRepresentation.comp σ))
  (hF : ∀ (f : OriginalContinuousCoefficientFiber eR eA) (g : H),
    (F f).val g = GeneralLinearGroup.map f.val.toRingHom (τ g))

/-- The original matrix classification restricts to the actual polarized quotient
and genuine continuous polarized lifts with the prescribed base similitude. -/
@[irreducible] def polarizedQuotientFiberEquiv :
    OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν))) eA ≃
      OriginalContinuousPolarizedFiber eA H σ ν := by
  have hcond (f : OriginalContinuousCoefficientFiber eR eA) :
      (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν)) ≤ RingHom.ker f.val.toRingHom ↔
        PolarizedMatrixEquations (F f).val.toMonoidHom
          ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
          ((Units.map (algebraMap O A).toMonoidHom).comp ν) := by
    have he : (F f).val.toMonoidHom = (GeneralLinearGroup.map f.val.toRingHom).comp τ :=
      MonoidHom.ext (hF f)
    exact (representationPolarizedIdeal_le_algebraKernel_iff τ _ ν f.val).trans
      (congrArg (fun t => PolarizedMatrixEquations t
        ((polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)).comp σ)
        ((Units.map (algebraMap O A).toMonoidHom).comp ν)) he.symm).to_iff
  exact ((originalLocalQuotientCoefficientFiberEquiv eR eA (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν))).trans
    (F.subtypeEquiv hcond)).trans (polarizedFramedFiberEquiv eA H σ ν).symm

/-- Restriction of matrix universality retains its original coefficient evaluation. -/
theorem polarizedQuotientFiberEquiv_block
    (f : OriginalContinuousCoefficientFiber (originalLocalQuotientResidueEquiv eR (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν))) eA)
    (g : H) :
    polarizedBlockRepresentation ((polarizedQuotientFiberEquiv eR eA H σ ν τ F hF f).val g) =
      GeneralLinearGroup.map f.val.toRingHom (GeneralLinearGroup.map (Ideal.Quotient.mk (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν))) (τ g)) := by
  unfold polarizedQuotientFiberEquiv
  change polarizedBlockRepresentation
    ((polarizedFramedFiberOfMatrices eA H σ ν _).val g) = _
  rw [polarizedFramedFiberOfMatrices_block]
  exact hF (originalLocalQuotientCoefficientFiberEquiv eR eA (representationPolarizedIdeal τ
  (MonoidHom.comp (polarizedComponent (R := IsLocalRing.ResidueField O) (ι := ι)) σ)
  (MonoidHom.comp (Units.map (RingHom.toMonoidHom (algebraMap O R))) ν)) f).val g

end
end Dubon2026
