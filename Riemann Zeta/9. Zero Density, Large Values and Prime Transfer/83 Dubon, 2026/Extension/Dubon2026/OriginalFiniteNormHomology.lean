import Dubon2026.OriginalFiniteInvariantNorms
import Dubon2026.OriginalPGroupFirstHomology

/-! # Finite-group norm and homology inputs for the original duality

The actual free presentation and invariant norm lifting extend the
existing norm-coinvariant and first-homology proofs to finite groups.
These are the precise inputs used by DUB-17's fundamental norm/homology
comparison. No general projectivity or all-degree vanishing is asserted.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (B : Rep.{0} ℤ G)
  (h : ∀ S : Subgroup G,
    Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2))

include h

/-- The actual relation kernel inherits the two subgroup degrees, with
its literal norm-lifting hypotheses derived for any finite group. -/
theorem originalFinite_relationKernel_subgroup_first_second_zero (S : Subgroup G) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalRelationModule B)) 2) := by
  letI := Fintype.ofFinite S
  exact originalRelationKernel_subgroup_first_second_zero B S (h S).1
    (originalFinite_subgroup_norm_preimages B h S)

/-- Actual two-degree subgroup vanishing implies injectivity of the
literal norm on the original coefficient's coinvariants. -/
theorem originalFinite_normCoinvariantInjective : OriginalNormCoinvariantInjective B := by
  have hK := originalFinite_relationKernel_subgroup_first_second_zero B h
  exact originalNormCoinvariantInjective_of_shortExact
    (originalRelationShortComplex_shortExact B)
    (originalArbitraryFree_normCoinvariantInjective B)
    (originalFinite_norm_preimages_of_subgroup_first_second (originalRelationModule B) hK)

/-- The same actual subgroup conditions force first homology to vanish,
using the existing free homology sequence and coinvariant inclusion. -/
theorem originalFinite_first_homology_zero : Limits.IsZero (groupHomology B 1) := by
  have hK := originalFinite_relationKernel_subgroup_first_second_zero B h
  have hn := originalFinite_normCoinvariantInjective (originalRelationModule B) hK
  exact originalQuotient_first_homology_zero_of_coinvariant_inclusion
    (originalRelationShortComplex_shortExact B)
    (originalArbitraryFree_positive_homology_zero B 0)
    (originalCoinvariantMap_injective_of_norm (originalRelationInclusion B)
      (fun x y hxy => Subtype.ext hxy) hn)

end
end Dubon2026
