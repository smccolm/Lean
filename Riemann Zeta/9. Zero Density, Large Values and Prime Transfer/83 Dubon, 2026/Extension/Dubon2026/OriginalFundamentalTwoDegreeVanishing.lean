import Dubon2026.OriginalFundamentalSubgroupSequence
import Dubon2026.OriginalFiniteSplittingVanishing
import Dubon2026.OriginalAugmentationFirstCardinality

/-! # Derived subgroup vanishing of the actual fundamental extension

The original coefficient's H1 vanishing, exact H2 order and restricted
fundamental generator now suffice: the augmentation H1/H2 and killed-class
inputs are proved for the literal constructed extension. This removes
those auxiliary premises from DUB-17's finite class/Ext duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {G : Type} [Group G] [Finite G] (C : Rep ℤ G)
  (φ : groupCohomology.cocycles₂ C) (S : Subgroup G) [Fintype S]

/-- The literal fundamental extension has zero subgroup H1 and H2 from the original finite class-system data, with augmentation and class-killing inputs discharged. -/
theorem originalFundamentalSubgroup_first_second_zero
    (h1 : Limits.IsZero (groupCohomology (Rep.res S.subtype C) 1))
    (h2card : Nat.card (groupCohomology (Rep.res S.subtype C) 2) = Fintype.card S)
    (h2gen : Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype C)) 2) (groupCohomology.H2π C φ)} = ⊤) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2) :=
  originalFiniteSplitting_first_second_zero (originalFundamentalSubgroup_shortExact C φ S)
    h1 (Fintype.card S) Fintype.card_ne_zero h2card _ h2gen
    (originalFundamentalSubgroup_class_zero C φ S)
    (originalAugmentationSubgroup_first_card S) (originalAugmentationSubgroup_second_zero S)

end
end Dubon2026
