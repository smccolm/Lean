import Dubon2026.SourceOriginalEllipticFibers

/-! DUB-17/18 -> original torsion cardinality -> exact orders throughout
finite-place charts. The existing nonzero E4/E6 germs have isolated zeros.
The proved full-stabilizer formula therefore forces the actual original
ramification to be one in a punctured neighborhood of any center.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter ModularForm
open scoped Topology MatrixGroups

theorem originalAnalyticRamification_eventually_one (N : ℕ) [NeZero N] (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), originalAnalyticRamification N (ofComplex z) = 1 := by
  have h4 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), E₄ (ofComplex z) ≠ 0 :=
    (JMultiplicity.analyticAt_comp JMultiplicity.mdiff_E₄ τ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => JMultiplicity.analyticOrderAt_ne_top JMultiplicity.mdiff_E₄
        JMultiplicity.E₄_I_ne_zero τ (analyticOrderAt_eq_top.mpr h))
  have h6 : ∀ᶠ z in 𝓝[≠] (τ : ℂ), E₆ (ofComplex z) ≠ 0 :=
    (JMultiplicity.analyticAt_comp JMultiplicity.mdiff_E₆ τ).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (fun h => JMultiplicity.analyticOrderAt_ne_top JMultiplicity.mdiff_E₆
        JMultiplicity.E₆_ρ_ne_zero τ (analyticOrderAt_eq_top.mpr h))
  filter_upwards [h4, h6] with z hz4 hz6
  have h := originalAnalyticRamification_dvd_full_stabilizer_half N (ofComplex z)
  rw [(JMultiplicity.case_generic hz4 hz6).2] at h
  exact Nat.dvd_one.mp h

theorem originalAnalyticRamification_param_eventually_one (N : ℕ) [NeZero N] (τ : ℍ) :
    ∀ᶠ u in 𝓝[≠] (0 : ℂ),
      originalAnalyticRamification N (ofComplex (EllipticCoordinate.param τ u)) = 1 := by
  have ht := (EllipticCoordinate.hasDerivAt_param τ).tendsto_nhdsNE
    (sub_ne_zero.mpr (EllipticCoordinate.upper_ne_conj τ τ))
  rw [EllipticCoordinate.param_zero] at ht
  exact ht.eventually (originalAnalyticRamification_eventually_one N τ)

end
end Dubon2026.SourceFunctionField
