import Dubon2026.SourceGammaOneAnalyticJOrders
import Dubon2026.SourceOriginalRamificationIsolated

/-! DUB-17/18 -> original Gamma1 Picard-period comparison -> actual local
charts. The existing exact j-order bounds actual ramification; isolated
E4/E6 zeros then remove branching on a punctured neighborhood. This needs
no classification of the subgroup stabilizer or global place dictionary. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter ModularForm SourceCurve
open scoped Topology MatrixGroups
variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

theorem analyticRamification_dvd_full_stabilizer_half (τ : ℍ) :
    analyticRamification hT τ ∣ Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 := by
  have hx : jCoordinateOver Γ ℂ -
      algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ) ≠ 0 :=
    Place.transcendental_sub_algebraMap_ne_zero (transcendental_jCoordinateOver Γ ℂ) _
  have h := analyticPlace_order hT τ _ hx
  rw [analyticOrder_j_sub hT] at h
  have he := h.symm.trans (JMultiplicity.main τ)
  have hi := WithTop.coe_injective he
  have hd : (analyticRamification hT τ : ℤ) ∣
      ((Nat.card (MulAction.stabilizer SL(2, ℤ) τ) / 2 : ℕ) : ℤ) := ⟨_, hi.symm⟩
  exact_mod_cast hd

theorem analyticRamification_eq_one_of_generic (τ : ℍ)
    (h4 : E₄ τ ≠ 0) (h6 : E₆ τ ≠ 0) : analyticRamification hT τ = 1 := by
  have h := analyticRamification_dvd_full_stabilizer_half hT τ
  rw [(JMultiplicity.case_generic h4 h6).2] at h
  exact Nat.dvd_one.mp h

theorem analyticRamification_eventually_one (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), analyticRamification hT (ofComplex z) = 1 := by
  have h4 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), E₄ (ofComplex z) ≠ 0 :=
    (JMultiplicity.analyticAt_comp JMultiplicity.mdiff_E₄ τ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => JMultiplicity.analyticOrderAt_ne_top JMultiplicity.mdiff_E₄
        JMultiplicity.E₄_I_ne_zero τ (analyticOrderAt_eq_top.mpr h))
  have h6 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), E₆ (ofComplex z) ≠ 0 :=
    (JMultiplicity.analyticAt_comp JMultiplicity.mdiff_E₆ τ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => JMultiplicity.analyticOrderAt_ne_top JMultiplicity.mdiff_E₆
        JMultiplicity.E₆_ρ_ne_zero τ (analyticOrderAt_eq_top.mpr h))
  filter_upwards [h4, h6] with z hz4 hz6
  exact analyticRamification_eq_one_of_generic hT (ofComplex z) hz4 hz6

end
end Dubon2026.SourceFunctionField.GammaOne
