import Dubon2026.OriginalPGroupNormCoinvariants
import Dubon2026.OriginalFreeHomologyVanishing
import Dubon2026.OriginalHomologyFirstFromCoinvariants

/-! # Actual first homology vanishing from two subgroup cohomology degrees

The literal free kernel inherits the two subgroup degrees, hence has
injective norm on coinvariants. Its inclusion is therefore injective on
coinvariants. Pinned Shapiro and the genuine homology sequence discharge
H1 homology, the second required input to DUB-17's integral projectivity.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Original subgroup H1/H2 cohomology vanishing for a finite p-group implies first homology vanishing for the original coefficient. -/
theorem originalPGroup_first_homology_zero
    {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Limits.IsZero (groupHomology B 1) := by
  have hK := originalPGroup_relationKernel_subgroup_first_second_zero B p hG h
  have hn := originalPGroup_normCoinvariantInjective (originalRelationModule B) p hG hK
  exact originalQuotient_first_homology_zero_of_coinvariant_inclusion
    (originalRelationShortComplex_shortExact B)
    (originalArbitraryFree_positive_homology_zero B 0)
    (originalCoinvariantMap_injective_of_norm (originalRelationInclusion B)
      (fun x y hxy => Subtype.ext hxy) hn)

end
end Dubon2026
