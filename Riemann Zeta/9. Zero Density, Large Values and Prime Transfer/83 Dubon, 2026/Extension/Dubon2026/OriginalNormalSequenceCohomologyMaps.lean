import Dubon2026.OriginalCohomologyGroupChangeNaturality
import Dubon2026.OriginalCoinducedGlobalDimensionShift

/-! # Original inflation and restriction commute with the actual dimension shifts -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]

/-- The literal inclusions of original invariant coefficients form a
map from the actual quotient sequence to the original coefficient sequence. -/
def normalInvariantSequenceInflationMap
    (X : ShortComplex (Rep.{0} k G)) (S : Subgroup G) [S.Normal] :
    (normalInvariantCoefficientSequence X S).map (Rep.resFunctor (QuotientGroup.mk' S)) ⟶ X where
  τ₁ := Rep.ofHom (X.X₁.ρ.quotientToInvariants_lift S)
  τ₂ := Rep.ofHom (X.X₂.ρ.quotientToInvariants_lift S)
  τ₃ := Rep.ofHom (X.X₃.ρ.quotientToInvariants_lift S)
  comm₁₂ := by apply Rep.hom_ext; ext x; rfl
  comm₂₃ := by apply Rep.hom_ext; ext x; rfl

/-- Actual inflation commutes with both original connecting maps in
the coinduced dimension shift, by genuine cochain naturality. -/
theorem originalCoinduced_delta_inflation
    (A : Rep.{0} k G) (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl ≫
        groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 =
      (groupCohomology.H1InfRes (originalCoinducedQuotient A) S).f ≫
        groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl := by
  exact originalCohomologyGroupChange_delta_naturality (QuotientGroup.mk' S)
    (normalInvariantSequenceInflationMap (originalCoinducedShortComplex A) S)
    (originalCoinducedInvariantSequence_shortExact A S hfirst)
    (originalCoinducedShortComplex_shortExact A) 1 2 rfl

/-- Actual subgroup restriction commutes with the original global and
subgroup connecting maps in the same coinduced dimension shift. -/
theorem originalCoinduced_delta_restriction
    (A : Rep.{0} k G) (S : Subgroup G) :
    groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl ≫
        groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalCoinducedQuotient A))) 1 ≫
        groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl := by
  exact originalCohomologyGroupChange_delta_naturality S.subtype (𝟙 _)
    (originalCoinducedShortComplex_shortExact A)
    (originalCoinducedShortComplex_restrict_shortExact A S) 1 2 rfl

end
end Dubon2026
