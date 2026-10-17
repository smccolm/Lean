import Dubon2026.OriginalPGroupInternalHomNorms
import Dubon2026.OriginalRegularSubgroupAcyclicity

/-! # Derived norm and homology conditions for the original Hom sequences

The converse norm criterion uses internal Hom into the actual
fundamental coefficient and the actual regular coefficient. Existing
subgroup acyclicity and p-group results discharge their coinvariant
norm injectivity and first homology vanishing; these are not new inputs
to the arithmetic construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
variable [Module.Projective ℤ M]

/-- The actual internal Hom has injective coinvariant norm and zero first homology, derived from its coefficient's two original subgroup cohomology degrees. -/
theorem originalPGroup_internalHom_norm_homology
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    OriginalNormCoinvariantInjective ((Rep.ihom M).obj B) ∧
      Limits.IsZero (groupHomology ((Rep.ihom M).obj B) 1) := by
  have hS (S : Subgroup G) :
      Limits.IsZero (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) 2) :=
    ⟨originalPGroup_internalHom_subgroup_positive_zero M B p hG h S 0,
      originalPGroup_internalHom_subgroup_positive_zero M B p hG h S 1⟩
  exact ⟨originalPGroup_normCoinvariantInjective _ p hG hS,
    originalPGroup_first_homology_zero _ p hG hS⟩

/-- The actual regular internal-Hom coefficient has both required norm and homology properties, with subgroup vanishing already proved. -/
theorem originalPGroup_regularInternalHom_norm_homology
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G) :
    OriginalNormCoinvariantInjective ((Rep.ihom M).obj (Rep.leftRegular ℤ G)) ∧
      Limits.IsZero (groupHomology ((Rep.ihom M).obj (Rep.leftRegular ℤ G)) 1) :=
  originalPGroup_internalHom_norm_homology M (Rep.leftRegular ℤ G) p hG
    (fun S => ⟨originalRegularSubgroup_positive_zero (k := ℤ) S 0,
      originalRegularSubgroup_positive_zero (k := ℤ) S 1⟩)

end
end Dubon2026
