import Dubon2026.CompletedPresentationUnframedUniversality
import Dubon2026.OriginalCoefficientRepresentationClass
import Dubon2026.CoefficientSubalgebraResidue

/-! # Genuine trace-coefficient maps biject with the existing original unframed classes -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- For the actual original completed presentation trace ring, evaluation of a genuine whole trace descent bijects continuous residue-preserving coefficient maps with the repository's existing original unframed deformation classes. -/
theorem completedTraceCoefficientClass_bijective
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    [IsLocalRing (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq))]
    [IsLocalHom (closedMatrixTraceAlgebra (O := O)
      (completedPresentationRepresentation ρ H q hq)).val.toRingHom]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (σ₀ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (hσ₀ : (σ₀.comp q.toMonoidHom).comp
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of G)).hom = ρ)
    (τ : H →ₜ* GeneralLinearGroup ι
      (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))
    (hτ : MatrixStrictlyConjugate
      (IsLocalRing.residue (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      ((GeneralLinearGroup.map
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)).val.toRingHom).comp
          τ.toMonoidHom) (completedPresentationRepresentation ρ H q hq))
    (hτres : (GeneralLinearGroup.map (localCoefficientReduction
      (coefficientSubalgebraResidueEquiv (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))).toRingHom).comp
          τ.toMonoidHom = σ₀) :
    Function.Bijective (originalCoefficientRepresentationClass
      (coefficientSubalgebraResidueEquiv (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))
      eA H σ₀ τ hτres) := by
  let R := CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker
  let υ := completedPresentationRepresentation ρ H q hq
  let S := closedMatrixTraceAlgebra (O := O) υ
  let eR := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  let eS := coefficientSubalgebraResidueEquiv eR S
  have hAtop : IsAdic (IsLocalRing.maximalIdeal A) := by rw [← hA]; rfl
  letI : T2Space A := (IsAdic.isHausdorff_iff hAtop).mp inferInstance
  constructor
  · intro f g hfg
    apply Subtype.ext
    exact descendedTraceCoefficientMaps_eq (IsLocalRing.residue R) υ τ.toMonoidHom hτ
      f.val g.val f.property.1 g.property.1 (localCoefficientReduction eA).toRingHom
      ((originalCoefficientRepresentationClass_eq_iff eS eA H σ₀ τ hτres f g).mp hfg)
  · intro c
    obtain ⟨ω, rfl⟩ := originalUnframedClass_surjective eA H σ₀ c
    have hω : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
        (profiniteMatrixRestriction (ω.val.comp q)) = ρ := by
      rw [← hσ₀]
      apply MonoidHom.ext
      intro g
      exact DFunLike.congr_fun ω.property
        (q (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of G) g))
    obtain ⟨f, ⟨hcf, hrf, hconj⟩, _hunique⟩ :=
      completedPresentationTraceCoefficient_exists_unique hA ρ H q hq eA τ hτ ω.val hω
    have hfr : (localCoefficientReduction eA).comp f = localCoefficientReduction eS :=
      hrf.trans (coefficientSubalgebraReduction_eq eR S).symm
    let f₀ : OriginalContinuousCoefficientFiber eS eA := ⟨f, hcf, hfr⟩
    refine ⟨f₀, ?_⟩
    exact (originalUnframedClass_eq_iff eA H σ₀
      (originalCoefficientRepresentationFramed eS eA H σ₀ τ hτres f₀) ω).mpr hconj

end
end Dubon2026
