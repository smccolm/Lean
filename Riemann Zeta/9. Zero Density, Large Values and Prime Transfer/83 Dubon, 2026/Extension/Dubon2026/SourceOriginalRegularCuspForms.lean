import Dubon2026.SourceOriginalDifferentialCuspDecay

/-! DUB-17/18 -> matching cusp-form lower dimension -> regular-differential
cusp-form comparison. Original regularity now supplies both finite holomorphy
and decay at all cusps, giving an actual native weight-two cusp form.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter ModularForm KaehlerDifferential SourceCurve
open scoped Topology BigOperators MatrixGroups ModularForm

theorem exists_original_regular_cusp_form (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {k : ℤ} (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      ∀ τ : ℍ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) := by
  obtain ⟨F, hF, he, hs⟩ := exists_original_holomorphic_differential N x hx hreg g h hh hr
  refine ⟨{ toFun := F, holo' := hF, slash_action_eq' := ?_, zero_at_cusps' := ?_ }, he⟩
  · intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    exact hs δ hδ
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact original_regular_differential_cusp_decay N x hx hreg g h hh hr F hF he γ

theorem original_regular_differential_cusp_form_realization (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k)
        (F : CuspForm (CongruenceSubgroup.Gamma0 N) 2),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g ∧
        ∀ τ : ℍ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) := by
  obtain ⟨k, g, h, hh, hr⟩ := original_field_modular_ratio N x
  obtain ⟨F, hF⟩ := exists_original_regular_cusp_form N x hx hreg g h hh hr
  exact ⟨k, g, h, F, hh, hr, hF⟩

end
end Dubon2026.SourceFunctionField
