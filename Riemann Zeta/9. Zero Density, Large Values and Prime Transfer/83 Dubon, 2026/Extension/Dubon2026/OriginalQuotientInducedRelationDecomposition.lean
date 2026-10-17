import Dubon2026.OriginalInducedRelationComparison
import Dubon2026.OriginalFiniteNormalizedQuotientSystem
import Dubon2026.OriginalFundamentalTwoDegreeVanishing

/-! # Actual quotient-class kernel decomposition for the induced sequence

The original normalized outside-unit quotient system supplies the full
fundamental order and every subgroup vanishing input. Thus DUB-17's
kernel step consumes the real arithmetic quotient and actual induced
presentation, with no chosen comparison or norm witness supplied.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

/-- Every zero obstruction into the actual arithmetic quotient decomposes
through its constructed induced relation comparison. -/
theorem originalClassQuotient_induced_relation_decomposition
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
    (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (N : Subgroup Gal(L/K)) (B : Rep.{0} ℤ Gal(L/K)) [Finite B] :
    let C := originalIdeleClassesModOutsideRep K L S hS
    let SB := originalSubgroupInducedSequence N B
    let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)
    ∃ (ιR : originalRelationModule B ⟶ TI.X₁)
      (ιP : Rep.free ℤ Gal(L/K) B ⟶ TI.X₂)
      (ρR : TI.X₁ ⟶ originalRelationModule SB.X₃)
      (ρP : TI.X₂ ⟶ Rep.free ℤ Gal(L/K) SB.X₃),
      originalRelationInclusion B ≫ ιP = ιR ≫ TI.f ∧
      originalRelationFreeCover B ≫ SB.f = ιP ≫ TI.g ∧
      TI.f ≫ ρP = ρR ≫ originalRelationInclusion SB.X₃ ∧
      TI.g ≫ SB.g = ρP ≫ originalRelationFreeCover SB.X₃ ∧
      ∀ χ : originalRelationModule B ⟶ C,
        originalRelationExtensionObstruction B C χ = 0 →
        ∃ (ψ : TI.X₁ ⟶ C) (a : Rep.free ℤ Gal(L/K) B ⟶ C),
          χ = ιR ≫ ψ + originalRelationInclusion B ≫ a := by
  obtain ⟨u, ho, h1, hc, hg, _⟩ := hsys
  let C := originalIdeleClassesModOutsideRep K L S hS
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  have hv (H : Subgroup Gal(L/K)) :
      Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 2) := by
    letI : Fintype H := Fintype.ofFinite H
    exact originalFundamentalSubgroup_first_second_zero C φ H (h1 H)
      ((hc H).trans Nat.card_eq_fintype_card) (hg H)
  exact originalInducedRelation_zero_obstruction_decomposition N B C φ
    (ho.trans ((IsGalois.card_aut_eq_finrank K L).symm.trans Nat.card_eq_fintype_card)) hv

end
end Dubon2026
