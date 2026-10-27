import Dubon2026.SourceCuspWeightCriterion

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> descent of the actual cusp-form image. The source weight-lowering map
uses the original E4, E6 and discriminant. Its exact multiplicative identity,
holomorphy and injectivity are proved for the actual cusp-form space. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField SourceFunctionField.CuspWeightCriterion
open scoped Manifold MatrixGroups ModularForm

/-- The source weight-lowering map on actual cusp forms. -/
def cuspWeightImage (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ) :
    CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := fun τ => f τ * eisensteinFactor a b τ / ModularForm.discriminant τ ^ m
  map_add' f g := by funext τ; simp only [CuspForm.add_apply, Pi.add_apply]; ring
  map_smul' c f := by
    funext τ
    simp only [CuspForm.IsGLPos.smul_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem cuspWeightImage_mul_discriminant (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    f τ * eisensteinFactor a b τ = cuspWeightImage Γ k a b m f τ * ModularForm.discriminant τ ^ m := by
  change _ = (f τ * eisensteinFactor a b τ / ModularForm.discriminant τ ^ m) * _
  rw [div_mul_cancel₀ _ (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))]

theorem mdifferentiable_cuspWeightImage (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ)
    (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) : MDiff (cuspWeightImage Γ k a b m f) :=
  (f.holo'.mul (mdifferentiable_eisensteinFactor a b)).div (JMultiplicity.mdiff_Δ.pow m)
    (fun τ => pow_ne_zero _ (ModularForm.discriminant_ne_zero τ))

theorem cuspWeightImage_injective (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (a b m : ℕ) :
    Function.Injective (cuspWeightImage Γ k a b m) := by
  intro f g he
  have hprod : (f : ℍ → ℂ) * eisensteinFactor a b = (g : ℍ → ℂ) * eisensteinFactor a b := by
    funext τ
    change f τ * eisensteinFactor a b τ = g τ * eisensteinFactor a b τ
    rw [cuspWeightImage_mul_discriminant, cuspWeightImage_mul_discriminant, he]
  have hm : ((f : ℍ → ℂ) - (g : ℍ → ℂ)) * eisensteinFactor a b = 0 := by
    rw [sub_mul, hprod, sub_self]
  obtain ⟨τ, hτ⟩ := exists_eisensteinFactor_ne_zero a b
  have hz := ((UpperHalfPlane.mul_eq_zero_iff (f.holo'.sub g.holo')
    (mdifferentiable_eisensteinFactor a b)).mp hm).resolve_right (fun h => hτ (congrFun h τ))
  exact DFunLike.ext _ _ (fun z => congrFun (sub_eq_zero.mp hz) z)

end
end Dubon2026.SourceFricke