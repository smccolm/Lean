import Dubon2026.SourceOriginalBoundaryArcPaths
import Dubon2026.SourceCellArcIntegralExtension

/-! DUB-17/18 -> cover reciprocity -> coordinate edge integrals.
Reuse the native affine arc parameter, interval FTC and substitution theorem.
This isolates the real-variable calculation used by the actual cover consumer. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
open Set
open scoped Interval

theorem arc_integral_eq_primitive_sub (R : RadialRegion) (k : Fin R.N)
    {gd : ℝ → ℂ} (hgd : ContinuousOn gd (R.arcIcc k))
    {G : ℝ → ℂ} (hGc : ContinuousOn G (Icc 0 1))
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt G
      (gd (arcParam R k t) * ((R.φs k.succ - R.φs k.castSucc : ℝ) : ℂ)) t) :
    (∫ s in (R.φs k.castSucc)..(R.φs k.succ), gd s) = G 1 - G 0 := by
  have hab : R.φs k.castSucc < R.φs k.succ := R.hmono Fin.castSucc_lt_succ
  have hcont : ContinuousOn (fun t => gd (arcParam R k t) *
      ((R.φs k.succ - R.φs k.castSucc : ℝ) : ℂ)) (Icc 0 1) := by
    refine (hgd.comp (by unfold arcParam; fun_prop) fun t ht => ?_).mul continuousOn_const
    exact arcParam_mem R k ⟨t, ht⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hGc hderiv
    ((hcont.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable)
  have hsub : (∫ t in (0 : ℝ)..1, gd (arcParam R k t) *
      ((R.φs k.succ - R.φs k.castSucc : ℝ) : ℂ)) =
      ∫ s in (R.φs k.castSucc)..(R.φs k.succ), gd s := by
    have h1 : (∫ t in (0 : ℝ)..1, gd (arcParam R k t) *
        ((R.φs k.succ - R.φs k.castSucc : ℝ) : ℂ)) =
        ((R.φs k.succ - R.φs k.castSucc : ℝ) : ℂ) * ∫ t in (0 : ℝ)..1,
          gd ((R.φs k.succ - R.φs k.castSucc) * t + R.φs k.castSucc) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [arcParam]
      ring_nf
    rw [h1, intervalIntegral.integral_comp_mul_add gd (sub_ne_zero.2 hab.ne')]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel, Complex.real_smul, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast sub_ne_zero.2 hab.ne'), one_mul]
  exact hsub.symm.trans hftc

end Dubon2026.SourceFunctionField.CellGeometry.OriginalEdgePaths
