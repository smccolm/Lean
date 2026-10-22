import Dubon2026.SourceOriginalDifferentialGerm
import Dubon2026.SourceOriginalRegularCuspForms

/-! DUB-17/18 -> matching cusp-form lower dimension. The actual original
regular differential germ lies in the image of the native cusp-form germ
map. This linear range inclusion is sufficient for the required dimension
bound and avoids an unnecessary choice of a new cusp-form normalization.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter KaehlerDifferential SourceCurve
open scoped Topology

/-- The complex-linear analytic germ map on native weight-two cusp forms. -/
def originalCuspFormGerm (N : ℕ) (τ : ℍ) :
    CuspForm (CongruenceSubgroup.Gamma0 N) 2 →ₗ[ℂ] Germ (𝓝[≠] (τ : ℂ)) ℂ where
  toFun F := ((fun z : ℂ => F (ofComplex z)) : Germ (𝓝[≠] (τ : ℂ)) ℂ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem original_regular_cusp_germ (N : ℕ) [NeZero N] (τ : ℍ)
    (x : modularFunctionFieldOver N ℂ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (F : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (he : ∀ w : ℍ, F w * h w = g w * deriv (JMultiplicity.jf ∘ ofComplex) (w : ℂ)) :
    originalCoefficientDifferentialGerm N τ x = originalCuspFormGerm N τ F := by
  apply Germ.coe_eq.mpr
  filter_upwards [realize_eventuallyEq_of_ratio g h x hh hr τ,
    ModularRatios.eventually_ne_zero_ofComplex h hh τ,
    mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)] with z hz hhZ hp
  rw [hz]
  have hzc : ((ofComplex z : ℍ) : ℂ) = z := by rw [ofComplex_apply_of_im_pos hp]
  have hF := he (ofComplex z)
  rw [hzc] at hF
  apply mul_right_cancel₀ hhZ
  field_simp
  simpa only [mul_comm] using hF.symm

theorem original_regular_coefficient_germ_mem_cusp_range (N : ℕ) [NeZero N] (τ : ℍ)
    (x : modularFunctionFieldOver N ℂ)
    (hreg : x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) :
    originalCoefficientDifferentialGerm N τ x ∈ (originalCuspFormGerm N τ).range := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, by rw [map_zero, map_zero]⟩
  obtain ⟨k, g, h, F, hh, hr, he⟩ := original_regular_differential_cusp_form_realization N x hx hreg
  exact ⟨F, (original_regular_cusp_germ N τ x g h hh hr F he).symm⟩

theorem original_regular_differential_germ_range_le (N : ℕ) [NeZero N] (τ : ℍ) :
    (originalRegularDifferentialGerm N τ).range ≤ (originalCuspFormGerm N τ).range := by
  rintro _ ⟨ω, rfl⟩
  apply original_regular_coefficient_germ_mem_cusp_range
  change (originalDifferentialCoordinateEquiv N).symm (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) •
    D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) ∈
      regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
  have he := (originalDifferentialCoordinateEquiv N).apply_symm_apply
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
  rw [originalDifferentialCoordinateEquiv_apply] at he
  rw [he]
  exact ω.property

end
end Dubon2026.SourceFunctionField
