import Dubon2026.OriginalInducedFiniteCoefficientSequence
import Dubon2026.OriginalRelationObstructionDecomposition

/-! # Comparisons for the actual induced relation sequence

The pinned projective lifting theorem constructs both comparison maps
needed by DUB-17's relation-extension reduction. The original zero
obstruction then gives its kernel decomposition for this actual sequence.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (N : Subgroup G) (B : Rep.{0} ℤ G)

/-- Both presentation comparisons are constructed for the original
induction unit and its literal quotient. -/
theorem originalInducedRelation_comparisons :
    let SB := originalSubgroupInducedSequence N B
    let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)
    ∃ (ιR : originalRelationModule B ⟶ TI.X₁)
      (ιP : Rep.free ℤ G B ⟶ TI.X₂)
      (ρR : TI.X₁ ⟶ originalRelationModule SB.X₃)
      (ρP : TI.X₂ ⟶ Rep.free ℤ G SB.X₃),
      originalRelationInclusion B ≫ ιP = ιR ≫ TI.f ∧
      originalRelationFreeCover B ≫ SB.f = ιP ≫ TI.g ∧
      TI.f ≫ ρP = ρR ≫ originalRelationInclusion SB.X₃ ∧
      TI.g ≫ SB.g = ρP ≫ originalRelationFreeCover SB.X₃ := by
  dsimp only
  let SB := originalSubgroupInducedSequence N B
  let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
    (Rep.indFunctor ℤ N.subtype)
  letI : Projective (originalRelationShortComplex B).X₂ :=
    inferInstanceAs (Projective (Rep.free ℤ G B))
  letI : Projective TI.X₂ := originalInducedRelationFree_projective N B
  obtain ⟨ιR, ιP, hi₁, hi₂⟩ := originalPresentation_exists_comparison
    (originalRelationShortComplex B) TI (originalInducedRelationSequence_shortExact N B) SB.f
  obtain ⟨ρR, ρP, hr₁, hr₂⟩ := originalPresentation_exists_comparison
    TI (originalRelationShortComplex SB.X₃) (originalRelationShortComplex_shortExact SB.X₃) SB.g
  exact ⟨ιR, ιP, ρR, ρP, hi₁, hi₂, hr₁, hr₂⟩

/-- The actual induced relation comparison decomposes every zero
obstruction, with neither a comparison map nor a lifting certificate
assumed as input. -/
theorem originalInducedRelation_zero_obstruction_decomposition [Finite B]
    (C : Rep.{0} ℤ G) (φ : groupCohomology.cocycles₂ C)
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
    (hv : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype
        (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype
        (originalFundamentalSplittingModule C φ)) 2)) :
    let SB := originalSubgroupInducedSequence N B
    let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)
    ∃ (ιR : originalRelationModule B ⟶ TI.X₁)
      (ιP : Rep.free ℤ G B ⟶ TI.X₂)
      (ρR : TI.X₁ ⟶ originalRelationModule SB.X₃)
      (ρP : TI.X₂ ⟶ Rep.free ℤ G SB.X₃),
      originalRelationInclusion B ≫ ιP = ιR ≫ TI.f ∧
      originalRelationFreeCover B ≫ SB.f = ιP ≫ TI.g ∧
      TI.f ≫ ρP = ρR ≫ originalRelationInclusion SB.X₃ ∧
      TI.g ≫ SB.g = ρP ≫ originalRelationFreeCover SB.X₃ ∧
      ∀ χ : originalRelationModule B ⟶ C,
        originalRelationExtensionObstruction B C χ = 0 →
        ∃ (ψ : TI.X₁ ⟶ C) (a : Rep.free ℤ G B ⟶ C),
          χ = ιR ≫ ψ + originalRelationInclusion B ≫ a := by
  dsimp only
  let SB := originalSubgroupInducedSequence N B
  let TI := (originalRelationShortComplex (Rep.res N.subtype B)).map
    (Rep.indFunctor ℤ N.subtype)
  letI : Finite SB.X₁ := inferInstanceAs (Finite B)
  letI : Projective TI.X₂ := originalInducedRelationFree_projective N B
  obtain ⟨ιR, ιP, ρR, ρP, hi₁, hi₂, hr₁, hr₂⟩ := originalInducedRelation_comparisons N B
  refine ⟨ιR, ιP, ρR, ρP, hi₁, hi₂, hr₁, hr₂, ?_⟩
  intro χ hz
  exact originalRelation_zero_obstruction_decomposition C φ ho hv
    (originalSubgroupInducedSequence_shortExact N B) TI.f TI.g TI.zero ιR ιP hi₁ hi₂ χ hz

end
end Dubon2026
