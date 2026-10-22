import Dubon2026.SourceAnalyticJDerivativeForms

/-! DUB-17/18 -> numerical modular genus -> elliptic ramification ->
the exact analytic multiplicity of j at each upper-half-plane point.
The required derivative identity follows from native level-one dimension
and discriminant division. This avoids adding a general Ramanujan system
or elliptic-curve uniformization. Full modular orbit separation identifies
the two exceptional fibers with the actual elliptic-point stabilizers.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_meromorphicOrderAt_E4_cube_div_discriminant_sub_eq_card_stabilizer_div_two.
-/
namespace Dubon2026.SourceFunctionField.JMultiplicity
noncomputable section
open UpperHalfPlane ModularForm Complex SlashInvariantForm Derivative Filter ModularGroup
open scoped MatrixGroups Real Topology ModularForm Manifold Derivative Modular
local notation "Δ" => ModularForm.discriminant
theorem isOpen_uhp : IsOpen {w : ℂ | 0 < w.im} := isOpen_upperHalfPlaneSet

theorem isPreconnected_uhp : IsPreconnected {w : ℂ | 0 < w.im} :=
  (convex_halfSpace_im_gt 0).isPreconnected

theorem differentiableOn_comp {G : ℍ → ℂ} (hG : MDiff G) :
    DifferentiableOn ℂ (G ∘ ofComplex) {w : ℂ | 0 < w.im} :=
  UpperHalfPlane.mdifferentiable_iff.mp hG

theorem analyticOnNhd_comp {G : ℍ → ℂ} (hG : MDiff G) :
    AnalyticOnNhd ℂ (G ∘ ofComplex) {w : ℂ | 0 < w.im} :=
  (differentiableOn_comp hG).analyticOnNhd isOpen_uhp

theorem analyticAt_comp {G : ℍ → ℂ} (hG : MDiff G) (τ : ℍ) :
    AnalyticAt ℂ (G ∘ ofComplex) (τ : ℂ) :=
  analyticOnNhd_comp hG (τ : ℂ) τ.im_pos

theorem comp_apply_coe (G : ℍ → ℂ) (τ : ℍ) : (G ∘ ofComplex) (τ : ℂ) = G τ := by
  simp [Function.comp_apply, ofComplex_apply]

theorem analyticOrderAt_ne_top {G : ℍ → ℂ} (hG : MDiff G) {z₀ : ℍ} (h0 : G z₀ ≠ 0) (τ : ℍ) :
    analyticOrderAt (G ∘ ofComplex) (τ : ℂ) ≠ ⊤ := by
  refine (analyticOnNhd_comp hG).analyticOrderAt_ne_top_of_isPreconnected isPreconnected_uhp
    z₀.im_pos τ.im_pos ?_
  rw [(analyticAt_comp hG z₀).analyticOrderAt_eq_zero.mpr (by simpa using h0)]
  exact ENat.zero_ne_top

theorem analyticOrderAt_eq_zero_of_ne_zero {G : ℍ → ℂ} (hG : MDiff G) {τ : ℍ} (h0 : G τ ≠ 0) :
    analyticOrderAt (G ∘ ofComplex) (τ : ℂ) = 0 :=
  (analyticAt_comp hG τ).analyticOrderAt_eq_zero.mpr (by simpa using h0)

theorem deriv_jf_eq (w : ℂ) (hw : 0 < w.im) :
    deriv (jf ∘ ofComplex) w = (2 * π * Complex.I) * D jf (ofComplex w) := by
  rw [normalizedDerivOfComplex, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk, ← mul_assoc,
    mul_inv_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_mul]

theorem g14_ne_zero : g14 ≠ 0 := by
  intro h
  have hD : ∀ z : ℍ, D jf z = 0 := fun z => by
    have hz : g14 z = 0 := by rw [h]; rfl
    rw [g14_apply] at hz
    exact (mul_eq_zero.mp hz).resolve_right (discriminant_ne_zero z)
  have hderiv : Set.EqOn (deriv (jf ∘ ofComplex)) 0 {w : ℂ | 0 < w.im} := fun w hw => by
    rw [deriv_jf_eq w hw, hD, mul_zero, Pi.zero_apply]
  have := isOpen_uhp.is_const_of_deriv_eq_zero isPreconnected_uhp
    (differentiableOn_comp mdifferentiable_jf) hderiv ρ.im_pos UpperHalfPlane.I.im_pos
  rw [comp_apply_coe, comp_apply_coe, jf_ρ] at this
  exact jf_I_ne_zero this.symm

theorem e14_ne_zero : e14 ≠ 0 := by
  intro h
  have hfun : ((E₄ : ℍ → ℂ) * (E₄ : ℍ → ℂ)) * (E₆ : ℍ → ℂ) = 0 := by
    funext z
    have hz : e14 z = 0 := by rw [h]; rfl
    rw [e14_apply] at hz
    simpa [pow_two] using hz
  have hE4 : MDiff (E₄ : ℍ → ℂ) := E₄.holo'
  have hE6 : MDiff (E₆ : ℍ → ℂ) := E₆.holo'
  rw [UpperHalfPlane.mul_eq_zero_iff (hE4.mul hE4) hE6,
    UpperHalfPlane.mul_eq_zero_iff hE4 hE4, or_self] at hfun
  rcases hfun with h4 | h6
  · exact E₄_I_ne_zero (by rw [h4]; rfl)
  · exact E₆_ρ_ne_zero (by rw [h6]; rfl)

theorem exists_D_jf_mul_Δ_eq :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℍ, D jf z * Δ z = c * (E₄ z ^ 2 * E₆ z) := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' e14 e14_ne_zero).mp finrank_fourteen g14
  have hpt : ∀ z : ℍ, D jf z * Δ z = c * (E₄ z ^ 2 * E₆ z) := fun z => by
    rw [← g14_apply, ← e14_apply, ← hc]
    rfl
  refine ⟨c, ?_, hpt⟩
  rintro rfl
  rw [zero_smul] at hc
  exact g14_ne_zero hc.symm


end
end Dubon2026.SourceFunctionField.JMultiplicity
