import Dubon2026.OriginalRelationNormDecomposition
import Dubon2026.OriginalFiniteFundamentalRelationCriterion

/-! # Decompose the actual zero relation obstruction

The finite-group converse norm theorem and the original presentation
horseshoe discharge the kernel step of DUB-17's nontrivial-action
relation extension. No prime, normal subgroup or trivial-action premise
is needed for this step. Fundamental order and subgroup vanishing are
the explicit upstream class-formation inputs.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Zero of the actual original obstruction factors through the middle
relation term modulo a morphism from the original free cover. -/
theorem originalRelation_zero_obstruction_decomposition
    {G : Type} [Group G] [Fintype G]
    (C : Rep.{0} ℤ G) (φ : groupCohomology.cocycles₂ C)
    (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
    (hv : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype
        (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype
        (originalFundamentalSplittingModule C φ)) 2))
    {SB : ShortComplex (Rep.{0} ℤ G)} (hSB : SB.ShortExact) [Finite SB.X₁]
    {R_I P_I : Rep.{0} ℤ G} (f_I : R_I ⟶ P_I) (g_I : P_I ⟶ SB.X₂)
    (w_I : f_I ≫ g_I = 0) [Projective P_I]
    (ιR : originalRelationModule SB.X₁ ⟶ R_I)
    (ιP : Rep.free ℤ G SB.X₁ ⟶ P_I)
    (sq₁ : originalRelationInclusion SB.X₁ ≫ ιP = ιR ≫ f_I)
    (sq₂ : originalRelationFreeCover SB.X₁ ≫ SB.f = ιP ≫ g_I)
    (χ : originalRelationModule SB.X₁ ⟶ C)
    (hz : originalRelationExtensionObstruction SB.X₁ C χ = 0) :
    ∃ (ψ : R_I ⟶ C) (a : Rep.free ℤ G SB.X₁ ⟶ C),
      χ = ιR ≫ ψ + originalRelationInclusion SB.X₁ ≫ a := by
  obtain ⟨η, hη⟩ :=
    (originalFiniteFundamental_relation_obstruction_zero_iff_norm C φ ho hv SB.X₁ χ).mp hz
  rw [← hη]
  exact originalRelation_norm_decomposition C hSB f_I g_I w_I ιR ιP sq₁ sq₂ η

end
end Dubon2026
