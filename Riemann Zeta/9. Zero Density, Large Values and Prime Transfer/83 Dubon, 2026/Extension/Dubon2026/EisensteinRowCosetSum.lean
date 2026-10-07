import Dubon2026.EisensteinRowFibers

/-! # Exact primitive-row and projective-coset sums -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory
open scoped ENNReal

noncomputable section

/-- The actual projective parabolic subgroup preserves the imaginary coordinate. -/
theorem gamma0ProjectiveTranslations_im {Q : ℕ} (g : gamma0ProjectiveTranslations Q) (z : ℍ) :
    (g • z).im = z.im := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  change (g.val • z).im = _
  rw [← hn, gamma0ProjectiveT_zpow_smul, vadd_im]

/-- Inverse-coset representatives give the same genuine height. -/
theorem gamma0Parabolic_im_congr {Q : ℕ} (A B : projectiveGamma0 Q)
    (h : (QuotientGroup.mk A : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) =
      QuotientGroup.mk B) (z : ℍ) : (A⁻¹ • z).im = (B⁻¹ • z).im := by
  have hm := QuotientGroup.eq.mp h
  have he : B⁻¹ = (A⁻¹ * B)⁻¹ * A⁻¹ := by group
  rw [he, mul_smul]
  exact (gamma0ProjectiveTranslations_im
    ⟨(A⁻¹ * B)⁻¹, (gamma0ProjectiveTranslations Q).inv_mem hm⟩ (A⁻¹ • z)).symm

/-- The primitive-row kernel is literally the height used by its projective parabolic coset. -/
theorem eisensteinRowHeight_parabolic {Q : ℕ} (v : gamma0PrimitiveRows Q) (z : ℍ) :
    eisensteinRowHeight v.val z = ((gamma0RowParabolicCoset v).out⁻¹ • z).im := by
  have h := gamma0Parabolic_im_congr ((gamma0Projectivize Q (gamma0RowCompletion v))⁻¹)
    (gamma0RowParabolicCoset v).out (gamma0RowParabolicCoset v).out_eq.symm z
  rw [inv_inv] at h
  change ((gamma0RowCompletion v).val • z).im = _ at h
  rw [← eisensteinRowHeight_bottom_row] at h
  have hv := congrArg Subtype.val (gamma0RowCompletion_row v)
  change (gamma0RowCompletion v).val.val 1 = v.val at hv
  rwa [hv] at h

/-- Summing over the actual two-element fiber contributes precisely twice the projective height term. -/
theorem eisenstein_parabolic_fiber_sum (Q : ℕ) (σ : ℝ) (z : ℍ)
    (q : (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) :
    (∑' v : {v : gamma0PrimitiveRows Q // gamma0RowParabolicCoset v = q},
      ENNReal.ofReal (eisensteinRowHeight v.val.val z ^ σ)) =
        2 * ENNReal.ofReal ((q.out⁻¹ • z).im ^ σ) := by
  rw [← (gamma0RowFiberEquiv q).tsum_eq
    (fun v => ENNReal.ofReal (eisensteinRowHeight v.val.val z ^ σ))]
  have he (b : Bool) : eisensteinRowHeight (gamma0RowFiberEquiv q b).val.val z =
      (q.out⁻¹ • z).im := by
    rw [eisensteinRowHeight_parabolic, (gamma0RowFiberEquiv q b).property]
  simp_rw [he]
  rw [tsum_fintype]
  simp [two_mul]

/-- The literal nonnegative primitive-row sum is exactly twice the actual projective-coset series. -/
theorem eisenstein_primitive_row_sum_eq_two_coset (Q : ℕ) (σ : ℝ) (z : ℍ) :
    (∑' v : gamma0PrimitiveRows Q, ENNReal.ofReal (eisensteinRowHeight v.val z ^ σ)) =
      2 * gamma0CosetEisensteinNN Q σ z := by
  have h := ENNReal.tsum_fiberwise
    (fun v : gamma0PrimitiveRows Q => ENNReal.ofReal (eisensteinRowHeight v.val z ^ σ))
    gamma0RowParabolicCoset
  change (∑' q, ∑' v : {v : gamma0PrimitiveRows Q // gamma0RowParabolicCoset v = q},
    ENNReal.ofReal (eisensteinRowHeight v.val.val z ^ σ)) = _ at h
  rw [← h]
  simp_rw [eisenstein_parabolic_fiber_sum]
  rw [ENNReal.tsum_mul_left]
  rfl

/-- The factor one half in the row definition precisely removes the central two-fold count. -/
theorem gamma0CosetEisensteinNN_eq_half_row_sum (Q : ℕ) (σ : ℝ) (z : ℍ) :
    gamma0CosetEisensteinNN Q σ z = (1 / 2 : ℝ≥0∞) *
      ∑' v : gamma0PrimitiveRows Q, ENNReal.ofReal (eisensteinRowHeight v.val z ^ σ) := by
  rw [eisenstein_primitive_row_sum_eq_two_coset, ← mul_assoc]
  rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

end
end Dubon2026
