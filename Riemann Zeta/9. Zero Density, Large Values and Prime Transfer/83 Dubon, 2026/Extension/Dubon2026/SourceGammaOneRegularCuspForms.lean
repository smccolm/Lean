import Dubon2026.SourceGammaOneRegularCuspOrder

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison. Original
regularity supplies finite holomorphy and vanishing at every cusp. Their
native consumer constructs the actual weight-two cusp form, retaining
the exact modular quotient and literal analytic derivative identity. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane ModularForm KaehlerDifferential SourceCurve
open scoped MatrixGroups ModularForm
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} [Γ.FiniteIndex]

private local instance originalFieldAlgebra : Algebra ℂ (functionFieldOver Γ ℂ) :=
  (functionFieldOver Γ ℂ).toSubalgebra.algebra

theorem exists_regular_cusp_form (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (functionFieldOver Γ ℂ) (jCoordinateOver Γ ℂ) ∈
      regularDifferentials ℂ (functionFieldOver Γ ℂ))
    {k : ℤ} (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g) :
    ∃ F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2,
      ∀ τ : ℍ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) := by
  obtain ⟨F, hF, he, hs⟩ := exists_holomorphic_differential hT x hx hreg g h hh hr
  refine ⟨{ toFun := F, holo' := hF, slash_action_eq' := ?_, zero_at_cusps' := ?_ }, he⟩
  · intro γ hγ
    obtain ⟨δ, hδ, rfl⟩ := hγ
    exact hs δ hδ
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    exact regular_differential_cusp_decay N hΓ hT x hx hreg g h hh hr F hF he hs γ

theorem regular_differential_cusp_form_realization (N : ℕ) [NeZero N]
    (hΓ : CongruenceSubgroup.Gamma N ≤ Γ) (hT : ModularGroup.T ∈ Γ)
    (x : functionFieldOver Γ ℂ) (hx : x ≠ 0)
    (hreg : x • D ℂ (functionFieldOver Γ ℂ) (jCoordinateOver Γ ℂ) ∈
      regularDifferentials ℂ (functionFieldOver Γ ℂ)) :
    ∃ (k : ℤ) (g h : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
        (F : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) 2),
      h ≠ 0 ∧ (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g ∧
        ∀ τ : ℍ, F τ * h τ = g τ * deriv (JMultiplicity.jf ∘ ofComplex) (τ : ℂ) := by
  obtain ⟨k, g, h, hh, hr⟩ := functionFieldOver_modular_ratio hT x
  obtain ⟨F, hF⟩ := exists_regular_cusp_form N hΓ hT x hx hreg g h hh hr
  exact ⟨k, g, h, F, hh, hr, hF⟩

end
end Dubon2026.SourceFunctionField.GammaOne
