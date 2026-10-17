import Dubon2026.OriginalNormCoinvariantExact
import Dubon2026.OriginalPGroupRelationKernelPreparation

/-! # Original p-group norm injectivity from two subgroup degrees

The actual free cover has injective coinvariant norm. Its kernel's norm
surjectivity has already been derived from the original subgroup H1/H2
vanishing, so the literal exact sequence removes the negative-one input
from DUB-17's integral projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Original subgroup H1/H2 vanishing for a finite p-group implies injectivity of the actual norm on the original coinvariants. -/
theorem originalPGroup_normCoinvariantInjective
    {G : Type} [Group G] [Fintype G] (B : Rep ℤ G)
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    OriginalNormCoinvariantInjective B := by
  have hK := (originalPGroup_relationKernel_prepared B p hG h).2.2.2
  exact originalNormCoinvariantInjective_of_shortExact
    (originalRelationShortComplex_shortExact B)
    (originalArbitraryFree_normCoinvariantInjective B) hK

end
end Dubon2026
