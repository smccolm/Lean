import Dubon2026.OriginalFundamentalConverseNorm

/-! # Injectivity of the actual fundamental norm-quotient H2 map

The direct two-shift criterion applies to representatives of the
already defined original morphism quotient. The result is injectivity
of that same actual H2 map, rather than a replacement pairing.
This discharges the finite norm-map premise on DUB-17's class/Ext route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module Submodule.Quotient.module
variable {G : Type} [Group G] [Fintype G]
variable (M C : Rep.{0} ℤ G) [Module.Finite ℤ M] [Module.Projective ℤ M]
variable (φ : groupCohomology.cocycles₂ C)
variable (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
variable (ho : addOrderOf (groupCohomology.H2π C φ) = Fintype.card G)
variable (h : ∀ S : Subgroup G,
  Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalFundamentalSplittingModule C φ)) 2))

include φ p hG ho h

/-- The original degree-two cohomology map on actual coefficient morphisms modulo norms is injective under full order and proved fundamental subgroup vanishing. -/
theorem originalFundamental_normQuotient_h2_injective :
    Function.Injective (originalNormQuotientCohomologyMap M C 1) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro q hq
  obtain ⟨χ, rfl⟩ := (originalCoefficientNormLinearMap M C).range.mkQ_surjective q
  have hχ : (groupCohomology.functor ℤ G 2).map χ = 0 := hq
  obtain ⟨η, hη⟩ := originalFundamental_h2_zero_norm M C φ p hG ho h χ hχ
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨η, hη⟩

/-- Vanishing of the actual induced H2 map is exactly existence of an original literal norm witness. -/
theorem originalFundamental_h2_zero_iff_norm (χ : M ⟶ C) :
    (groupCohomology.functor ℤ G 2).map χ = 0 ↔
      ∃ η : M →ₗ[ℤ] C, originalCoefficientNormMorphism M C η = χ := by
  constructor
  · exact originalFundamental_h2_zero_norm M C φ p hG ho h χ
  · rintro ⟨η, rfl⟩
    exact originalCoefficientNormMorphism_positive_map_zero M C η 1

end
end Dubon2026
