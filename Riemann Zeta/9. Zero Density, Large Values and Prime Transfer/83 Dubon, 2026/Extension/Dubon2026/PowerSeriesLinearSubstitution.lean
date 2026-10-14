import Dubon2026.PowerSeriesFiniteCoefficientSubstitution

/-! # The linear coefficient of actual substitution

Only the linear coefficient is required to apply uniqueness of DUB-17's
constructed semilinear series. Use the proved one-variable finite-degree
comparison directly, without multivariate linear-term machinery.
-/
namespace Dubon2026
noncomputable section

/-- For series with zero constants, the linear coefficient of substitution is the product of the original linear coefficients. -/
theorem powerSeries_coeff_one_subst {R : Type*} [CommRing R]
    {f g : PowerSeries R} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst g f) =
      PowerSeries.coeff 1 f * PowerSeries.coeff 1 g := by
  have heq : PowerSeries.coeff 1 (PowerSeries.subst g f) =
      PowerSeries.coeff 1 (PowerSeries.subst g
        (PowerSeries.monomial 1 (PowerSeries.coeff 1 f))) := by
    apply powerSeries_coeff_subst_eq_of_coeff_eq_le hg hg 1
    · intro d hd
      have hd01 : d = 0 ∨ d = 1 := by omega
      rcases hd01 with rfl | rfl
      · rw [PowerSeries.coeff_monomial]
        simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
      · simp
    · intro _ _
      rfl
  rw [heq, PowerSeries.monomial_eq_C_mul_X_pow,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hg),
    PowerSeries.subst_C, PowerSeries.subst_pow (PowerSeries.HasSubst.of_constantCoeff_zero' hg),
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hg), pow_one]
  exact PowerSeries.coeff_C_mul _ _ _

end
end Dubon2026
