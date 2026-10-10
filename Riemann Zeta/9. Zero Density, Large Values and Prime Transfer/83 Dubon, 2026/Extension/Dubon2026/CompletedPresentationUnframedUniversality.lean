import Dubon2026.CompletedPresentationConjugatingEndomorphism
import Dubon2026.DescendedTraceCoefficientGeneration
import Dubon2026.MatrixStrictConjugacyCoefficientChange

/-! # Actual continuous trace-coefficient maps classify original lifts up to strict conjugacy -/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {G ι O A : Type u} [Group G] [Fintype ι] [DecidableEq ι]
  [CommRing O] [IsLocalRing O] [Group.FG G] [IsNoetherianRing O]
  [Finite (IsLocalRing.ResidueField O)]
  [CommRing A] [IsLocalRing A] [Algebra O A] [WithIdeal A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

/-- A genuine whole trace descent of the original universal representation gives exactly one continuous trace-coefficient map for each original framed lift up to strict conjugacy. The proof constructs the map by framed universality and proves uniqueness using the actual descended trace generators. -/
theorem completedPresentationTraceCoefficient_exists_unique
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : G →* GeneralLinearGroup ι (IsLocalRing.ResidueField O))
    (H : ProfiniteGrp.{u})
    (q : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of G) →ₜ* H)
    (hq : Function.Surjective q)
    [IsLocalRing (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker)]
    (eA : IsLocalRing.ResidueField A ≃ₐ[O] IsLocalRing.ResidueField O)
    (τ : H →ₜ* GeneralLinearGroup ι
      (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)))
    (hτ : MatrixStrictlyConjugate
      (IsLocalRing.residue (CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker))
      ((GeneralLinearGroup.map
        (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)).val.toRingHom).comp
          τ.toMonoidHom) (completedPresentationRepresentation ρ H q hq))
    (σ : H →ₜ* GeneralLinearGroup ι A)
    (hσ : (GeneralLinearGroup.map (localCoefficientReduction eA).toRingHom).comp
      (profiniteMatrixRestriction (σ.comp q)) = ρ) :
    ∃! f : closedMatrixTraceAlgebra (O := O)
        (completedPresentationRepresentation ρ H q hq) →ₐ[O] A,
      Continuous f ∧
      (localCoefficientReduction eA).comp f =
        (localCoefficientReduction (completedPresentationResidueEquiv ρ q.toMonoidHom.ker)).comp
          (closedMatrixTraceAlgebra (O := O) (completedPresentationRepresentation ρ H q hq)).val ∧
      MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
        ((GeneralLinearGroup.map f.toRingHom).comp τ.toMonoidHom) σ.toMonoidHom := by
  let R := CompletedPresentationCoefficientQuotient ρ q.toMonoidHom.ker
  let υ := completedPresentationRepresentation ρ H q hq
  let S := closedMatrixTraceAlgebra (O := O) υ
  let eR := completedPresentationResidueEquiv ρ q.toMonoidHom.ker
  have hAtop : IsAdic (IsLocalRing.maximalIdeal A) := by rw [← hA]; rfl
  letI : T2Space A := (IsAdic.isHausdorff_iff hAtop).mp inferInstance
  obtain ⟨φ, ⟨hφ, hcφ, hrφ⟩, _huφ⟩ :=
    completedPresentationCoefficient_exists_unique hA ρ eA H q hq σ hσ
  have hr : (localCoefficientReduction eA).comp φ = localCoefficientReduction eR := by
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (DFunLike.congr_fun hrφ y).trans
      (completedPresentationResidueEquiv_original ρ q.toMonoidHom.ker y).symm
  have hτred : MatrixStrictlyConjugate (localCoefficientReduction eR).toRingHom
      ((GeneralLinearGroup.map S.val.toRingHom).comp τ.toMonoidHom) υ :=
    matrixStrictlyConjugate_comp_reduction (IsLocalRing.residue R) eR.toRingHom _ _ hτ
  let f : S →ₐ[O] A := φ.comp S.val
  have hcf : Continuous f := hcφ.comp continuous_subtype_val
  have hconj : MatrixStrictlyConjugate (localCoefficientReduction eA).toRingHom
      ((GeneralLinearGroup.map f.toRingHom).comp τ.toMonoidHom) σ.toMonoidHom := by
    have hm := matrixStrictlyConjugate_map (localCoefficientReduction eR).toRingHom
      (localCoefficientReduction eA).toRingHom φ.toRingHom
      (congrArg AlgHom.toRingHom hr) _ _ hτred
    have heq : (GeneralLinearGroup.map φ.toRingHom).comp υ = σ.toMonoidHom :=
      MonoidHom.ext hφ
    rw [heq] at hm
    exact hm
  have hrf : (localCoefficientReduction eA).comp f =
      (localCoefficientReduction eR).comp S.val :=
    congrArg (fun k : R →ₐ[O] IsLocalRing.ResidueField O => k.comp S.val) hr
  refine ⟨f, ⟨hcf, hrf, hconj⟩, ?_⟩
  intro g hg
  exact descendedTraceCoefficientMaps_eq (IsLocalRing.residue R) υ τ.toMonoidHom hτ
    g f hg.1 hcf (localCoefficientReduction eA).toRingHom
    (matrixStrictlyConjugate_trans _ _ _ _ hg.2.2
      (matrixStrictlyConjugate_symm _ _ _ hconj))

end
end Dubon2026
