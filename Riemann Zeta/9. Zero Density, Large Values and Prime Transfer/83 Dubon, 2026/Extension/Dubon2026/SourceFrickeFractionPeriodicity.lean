import Dubon2026.SourceFrickeCyclotomicFractionGerm

/-! DUB-17/18 -> rational Fourier structure -> cyclotomic monic descent.
Periodicity of a holomorphic Fricke fraction is derived from its actual
numerator and denominator, using the native analytic domain theorem.
The upper-half-plane translation bridge follows the fixed primary source
anthropics/fermats-last-theorem 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WLight_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient, Apache-2.0. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped Manifold ModularForm MatrixGroups

theorem apply_T_of_periodic {N : ℕ} {f : ℍ → ℂ}
    (hf : Function.Periodic (f ∘ ofComplex) N) (τ : ℍ) :
    f (ModularGroup.T ^ (N : ℤ) • τ) = f τ := by
  have h := hf (τ : ℂ)
  have he : ofComplex ((τ : ℂ) + (N : ℂ)) = ModularGroup.T ^ (N : ℤ) • τ := by
    apply UpperHalfPlane.ext
    rw [ofComplex_apply_of_im_pos (by simpa using τ.im_pos),
      modular_T_zpow_smul, coe_vadd]
    push_cast
    ring
  simpa only [Function.comp_apply, Complex.ofReal_natCast, he, ofComplex_apply] using h

theorem periodic_comp_ofComplex_of_T {N : ℕ} {f : ℍ → ℂ}
    (h : ∀ τ : ℍ, f (ModularGroup.T ^ (N : ℤ) • τ) = f τ) :
    Function.Periodic (f ∘ ofComplex) N := by
  intro w
  by_cases hw : 0 < w.im
  · have hw' : 0 < (w + (N : ℂ)).im := by simpa using hw
    simp only [Function.comp_apply,
      ofComplex_apply_of_im_pos hw', ofComplex_apply_of_im_pos hw]
    rw [← h ⟨w, hw⟩]
    congr 1
    apply UpperHalfPlane.ext
    rw [modular_T_zpow_smul, coe_vadd]
    push_cast
    ring
  · have hw' : (w + (N : ℂ)).im ≤ 0 := by simpa using le_of_not_gt hw
    simp only [Function.comp_apply,
      ofComplex_apply_of_im_nonpos hw', ofComplex_apply_of_im_nonpos (le_of_not_gt hw)]

theorem periodic_cyclotomic_fraction {N : ℕ} [NeZero N]
    {a b f : ℍ → ℂ} (ha : a ∈ cyclotomicLevelRing N) (hb : b ∈ cyclotomicLevelRing N)
    (hb0 : b ≠ 0) (hf : MDiff f) (hrel : f * b = a) :
    Function.Periodic (f ∘ ofComplex) N := by
  let γ := ModularGroup.T ^ (N : ℤ)
  have htrans : MDiff (fun τ : ℍ => f (γ • τ)) := by
    have h : MDiff (f ∣[(0 : ℤ)] γ) := hf.slash 0 γ
    have he : f ∣[(0 : ℤ)] γ = fun τ : ℍ => f (γ • τ) := by
      funext τ
      simp only [ModularForm.SL_slash_apply, neg_zero, zpow_zero, mul_one]
    exact he ▸ h
  have hm : ((fun τ : ℍ => f (γ • τ)) - f) * b = 0 := by
    funext τ
    have h1 := congrFun hrel (γ • τ)
    have h2 := congrFun hrel τ
    change f τ * b τ = a τ at h2
    have haT := apply_T_of_periodic (cyclotomicLevelRing_periodic ha) τ
    have hbT := apply_T_of_periodic (cyclotomicLevelRing_periodic hb) τ
    change f (γ • τ) * b (γ • τ) = a (γ • τ) at h1
    rw [hbT, haT] at h1
    change (f (γ • τ) - f τ) * b τ = 0
    rw [sub_mul, h1, h2, sub_self]
  have he := (UpperHalfPlane.mul_eq_zero_iff (htrans.sub hf)
    (cyclotomicLevelRing_holomorphic hb)).mp hm |>.resolve_right hb0
  exact periodic_comp_ofComplex_of_T fun τ => sub_eq_zero.mp (congrFun he τ)

end
end Dubon2026.SourceFricke