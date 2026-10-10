import Dubon2026.FixedResidualTraceUniversalRing
import Dubon2026.OriginalTraceUnframedUniversality
import Dubon2026.OriginalCoefficientClassFixedQuotient

/-! # Genuine whole-group unframed universality of the original fixed-residual trace ring -/

namespace Dubon2026
noncomputable section
open Matrix

variable {ι O L : Type} [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)] [TopologicalSpace (IsLocalRing.ResidueField O)]
  [T2Space (IsLocalRing.ResidueField O)]
  [Field L] [Algebra (IsLocalRing.ResidueField O) L] [IsAlgClosed L]

omit [IsNoetherianRing O] in
private theorem wholeClassUniversality_of_fixedQuotient
    {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] [TopologicalSpace R]
    (eR : IsLocalRing.ResidueField R ≃ₐ[O] IsLocalRing.ResidueField O)
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    (τq : originalResidualProfiniteGroup p H σ hσ →ₜ* GeneralLinearGroup ι R)
    (hτq : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τq.toMonoidHom = (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom)
    (hbijq : ∀ (A : Type) [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
      (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
      (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
      Function.Bijective (originalCoefficientRepresentationClass eR eA _
        (fixedResidualOriginalRepresentation p H σ hσ).toMonoidHom τq hτq)) :
    ∃ (τ : H →ₜ* GeneralLinearGroup ι R)
      (hτres : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
        τ.toMonoidHom = σ),
      ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
        [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
        (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
        (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
        Function.Bijective (originalCoefficientRepresentationClass eR eA H σ τ hτres) := by
  let π : H →ₜ* originalResidualProfiniteGroup p H σ hσ := ⟨QuotientGroup.mk'
    (fixedResidualProPKernel p H σ.ker (originalResidualMatrixKernel_isClosed H σ hσ)),
      QuotientGroup.continuous_mk⟩
  let τ := τq.comp π
  have hτres : (GeneralLinearGroup.map (localCoefficientReduction eR).toRingHom).comp
      τ.toMonoidHom = σ := by
    apply MonoidHom.ext
    intro g
    exact DFunLike.congr_fun hτq (π g)
  refine ⟨τ, hτres, ?_⟩
  intro A _ _ _ _ _ _ hA eA
  exact originalCoefficientRepresentationClass_fixedQuotient_bijective hA eR eA
    p hp H σ hσ τ hτres τq hτq (fun _ => rfl) (hbijq A hA eA)

/-- The actual original whole-group trace ring is complete local and Noetherian and classifies all genuine original continuous unframed lifts over every complete Noetherian local target. The fixed-residual quotient and the original group have exactly the same deformation classes via the proved original quotient equivalence. -/
theorem fixedResidualTraceUnframedUniversality_exists
    (p : ℕ) (hp : p.Prime) [CharP (IsLocalRing.ResidueField O) p]
    (H : ProfiniteGrp.{0})
    (σ : H →* GeneralLinearGroup ι (IsLocalRing.ResidueField O)) (hσ : Continuous σ)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))]
    (S : Finset (originalResidualProfiniteGroup p H σ hσ))
    (hS : Function.Surjective (profiniteGeneratorPresentation
      (originalResidualProfiniteGroup p H σ hσ) S)) (i₀ : ι) :
    let T := closedMatrixTraceAlgebra (O := O)
      (fixedResidualFramedUniversalRepresentation p H σ hσ S hS)
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
          [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eT eA H σ τ hτres) := by
  let Q := originalResidualProfiniteGroup p H σ hσ
  let q := profiniteGeneratorPresentation Q S
  let σq := fixedResidualOriginalRepresentation p H σ hσ
  letI := fixedResidualOriginalRepresentation_absoluteIrreducible (L := L) p H σ hσ
  let property := fun T : Subalgebra O (FixedResidualFramedCoefficientRing p H σ hσ S) =>
    ∃ hlocal : IsLocalRing T,
      letI := hlocal
      IsNoetherianRing T ∧ IsAdic (IsLocalRing.maximalIdeal T) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal T) T ∧
      ∃ (eT : IsLocalRing.ResidueField T ≃ₐ[O] IsLocalRing.ResidueField O)
        (τ : H →ₜ* GeneralLinearGroup ι T)
        (hτres : (GeneralLinearGroup.map (localCoefficientReduction eT).toRingHom).comp
          τ.toMonoidHom = σ),
        ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
          [Algebra O A] [WithIdeal A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
          (_hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
          (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O),
          Function.Bijective (originalCoefficientRepresentationClass eT eA H σ τ hτres)
  change property (closedMatrixTraceAlgebra (O := O)
    (fixedResidualFramedUniversalRepresentation p H σ hσ S hS))
  apply (congrArg property (fixedResidualTraceAlgebra_eq p H σ hσ S hS)).mpr
  obtain ⟨hlocal, hnoeth, htop, hcomplete, eT, τq, hτq, hbijq⟩ :=
    originalTraceUnframedUniversality_exists (L := L) Q q hS σq i₀
  let T := closedMatrixTraceAlgebra (O := O)
    (completedPresentationRepresentation (originalPresentedResidualRestriction Q q σq) Q q hS)
  letI : IsLocalRing T := hlocal
  obtain ⟨τ, hτres, hbij⟩ := wholeClassUniversality_of_fixedQuotient eT p hp H σ hσ
    τq hτq hbijq
  exact ⟨hlocal, hnoeth, htop, hcomplete, eT, τ, hτres, hbij⟩

end
end Dubon2026
