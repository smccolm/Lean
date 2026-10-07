import Dubon2026.EisensteinRowCosetSum

/-! # Unfolding the actual primitive-row Eisenstein series -/

namespace Dubon2026

open UpperHalfPlane CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ENNReal

noncomputable section

/-- At real parameters the actual complex kernel is the real positive height power. -/
theorem nonholomorphicEisensteinTerm_real (σ : ℝ) (v : Fin 2 → ℤ) (z : ℍ) :
    nonholomorphicEisensteinTerm (σ : ℂ) v z = (eisensteinRowHeight v z ^ σ : ℝ) :=
  (Complex.ofReal_cpow (eisensteinRowHeight_nonneg v z) σ).symm

/-- The literal positive height-power series is summable to the right of one. -/
theorem summable_eisenstein_real_rows (Q : ℕ) {σ : ℝ} (hσ : 1 < σ) (z : ℍ) :
    Summable (fun v : gamma0PrimitiveRows Q => eisensteinRowHeight v.val z ^ σ) := by
  have h := gamma0Eisenstein_summable_norm Q (s := (σ : ℂ)) hσ z
  simpa only [nonholomorphicEisensteinTerm_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (eisensteinRowHeight_nonneg _ _) _)] using h

/-- The actual complex Eisenstein value is real at real parameters, with the literal half-sum value. -/
theorem gamma0Eisenstein_real_value (Q : ℕ) (σ : ℝ) (z : ℍ) :
    gamma0Eisenstein Q (σ : ℂ) z =
      (((1 / 2 : ℝ) * ∑' v : gamma0PrimitiveRows Q, eisensteinRowHeight v.val z ^ σ : ℝ) : ℂ) := by
  rw [gamma0Eisenstein]
  simp_rw [nonholomorphicEisensteinTerm_real]
  rw [← Complex.ofReal_tsum]
  push_cast
  rfl

/-- The convergent genuine Eisenstein series equals the nonnegative projective-coset series exactly. -/
theorem gamma0Eisenstein_re_eq_cosetNN (Q : ℕ) {σ : ℝ} (hσ : 1 < σ) (z : ℍ) :
    ENNReal.ofReal (gamma0Eisenstein Q (σ : ℂ) z).re = gamma0CosetEisensteinNN Q σ z := by
  rw [gamma0Eisenstein_real_value, Complex.ofReal_re,
    ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_tsum_of_nonneg (fun v : gamma0PrimitiveRows Q =>
      Real.rpow_nonneg (eisensteinRowHeight_nonneg v.val z) σ)
      (summable_eisenstein_real_rows Q hσ z), gamma0CosetEisensteinNN_eq_half_row_sum]
  congr 1
  norm_num [ENNReal.ofReal_div_of_pos]

/-- The actual primitive-row Eisenstein series unfolds the genuine Petersson density onto the unit strip. -/
theorem gamma0_eisenstein_petersson_unfold {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (Matrix.SpecialLinearGroup.mapGL ℝ)) k)
    {σ : ℝ} (hσ : 1 < σ) :
    (∫⁻ z in gamma0FundamentalDomain Q,
      ENNReal.ofReal (gamma0Eisenstein Q (σ : ℂ) z).re * ENNReal.ofReal ‖petersson k f f z‖) =
      ∫⁻ z in upperHalfPlaneUnitStrip,
        ENNReal.ofReal (z.im ^ σ) * ENNReal.ofReal ‖petersson k f f z‖ := by
  simp_rw [gamma0Eisenstein_re_eq_cosetNN Q hσ]
  exact gamma0_petersson_coset_unfold f σ

end
end Dubon2026
