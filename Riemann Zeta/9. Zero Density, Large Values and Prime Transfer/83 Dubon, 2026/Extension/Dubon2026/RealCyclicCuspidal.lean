import Dubon2026.RealUnipotentCuspPeriod
import Dubon2026.RealProjectiveCyclic
import Dubon2026.PrincipalCuspOrbit

/-! # Actual vanishing periods at every integral cusp throughout the original cyclic representation -/

namespace Dubon2026

noncomputable section
open UpperHalfPlane Matrix.SpecialLinearGroup CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

attribute [local instance] principalNormal

/-- The genuine upper unipotent subgroup depends continuously on its real parameter. -/
theorem realUpperUnipotent_continuous : Continuous realUpperUnipotent := by
  apply Continuous.subtype_mk
  change Continuous (fun t : ℝ => !![1, t; 0, 1])
  fun_prop

/-- The original cusp lift has zero period at every integral cusp and every real-group point. -/
theorem realWeightLift_integral_cusp_period_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    (σ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    (∫ x in (0 : ℝ)..1,
      realWeightLift k f (integralToRealSL σ * realUpperUnipotent ((Q : ℝ) * x) * g)) = 0 := by
  let F := normalCuspAction (Gamma Q) k σ⁻¹ (cuspGamma0ToPrincipal Q k f)
  have he : ⇑F = ⇑f ∣[k] mapGL ℝ σ := by
    simp only [F, normalCuspAction_apply, inv_inv, cuspGamma0ToPrincipal_apply]
  have hp : (Q : ℝ) ∈ ((Gamma Q).map (mapGL ℝ)).strictPeriods := by simp
  have hQ : (0 : ℝ) < Q := by exact_mod_cast NeZero.pos Q
  have hz := realWeightLift_unipotent_integral_zero F hQ hp g
  simp only [he] at hz
  simpa only [mul_assoc, realWeightLift_mul, integralToRealSL_mapGL] using hz

/-- Every original cyclic vector has zero unipotent average at every integral cusp. -/
theorem realLiftCyclic_integral_cusp_period_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm (Gamma0 Q : Subgroup (GL (Fin 2) ℝ)) k)
    {v : SL(2, ℝ) → ℂ} (hv : v ∈ (realLiftCyclicRepresentation k f).toSubmodule)
    (σ : SL(2, ℤ)) (g : SL(2, ℝ)) :
    (∫ x in (0 : ℝ)..1, v (integralToRealSL σ * realUpperUnipotent ((Q : ℝ) * x) * g)) = 0 := by
  have hc : Continuous (fun x : ℝ =>
      integralToRealSL σ * realUpperUnipotent ((Q : ℝ) * x) * g) :=
    (continuous_const.mul (realUpperUnipotent_continuous.comp
      (continuous_const.mul continuous_id))).mul_const g
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    simpa only [TannakaDuality.FiniteGroup.rightRegular_apply, mul_assoc] using
      realWeightLift_integral_cusp_period_zero f σ (g * a)
  | zero => simp
  | add x y hx hy hix hiy =>
    simp only [Pi.add_apply]
    have hi := intervalIntegral.integral_add (μ := volume)
      (((realLiftCyclic_continuous f hx).comp hc).intervalIntegrable 0 1)
      (((realLiftCyclic_continuous f hy).comp hc).intervalIntegrable 0 1)
    simpa only [Function.comp_def, hix, hiy, add_zero] using hi
  | smul c x hx hix =>
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [intervalIntegral.integral_const_mul, hix, mul_zero]

end
end Dubon2026
