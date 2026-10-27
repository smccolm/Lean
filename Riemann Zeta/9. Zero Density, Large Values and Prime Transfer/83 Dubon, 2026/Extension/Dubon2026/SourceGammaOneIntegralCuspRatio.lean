import Dubon2026.SourceIntegerJEulerBaseChange
import Dubon2026.SourceGammaOneFourierLinear

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field. An actual integral weight-two cusp form supplies the
equal-weight ratio f Delta / (E4 squared E6). The proved nonzero integer
j-derivative normalization turns that literal ratio into a coefficient y
whose product with q d/dq j is the original cusp-form Fourier expansion.
No field-membership or differential-expansion premise is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane SourceDifferential SourceFricke ModularForm CongruenceSubgroup
open scoped ModularForm MatrixGroups

theorem exists_integral_cusp_differential_coefficient
    (K : Type*) [Field K] [CharZero K] (N : ℕ)
    (f : CuspForm (Gamma1 N) 2) (p : PowerSeries ℤ) (hp : IsIntegralQExp f p) :
    ∃ y : qExpFunctionFieldC K (Gamma1 N),
      (y : LaurentSeries K) * qEuler K (jqModC K) = intSeriesC K p := by
  let fm : ModularForm (Gamma1 N) 2 := f
  let d : ModularForm (Gamma1 N) 12 :=
    ModularNormPolynomial.restrict (Subgroup.map_le_range _ (Gamma1 N))
      (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  let a : ModularForm (Gamma1 N) 14 := (fm.mul d).mcast (by norm_num)
  let b : ModularForm (Gamma1 N) 14 :=
    ModularNormPolynomial.restrict (Subgroup.map_le_range _ (Gamma1 N))
      (((E₄.pow 2).mul E₆).mcast (by norm_num))
  have ha : IsIntegralQExp a (p * (PowerSeries.X * dedekindEtaUnit)) := by
    change (p * (PowerSeries.X * dedekindEtaUnit)).map (Int.castRingHom ℂ) =
      qExpansion 1 (((fm.mul d).mcast (by norm_num) : ModularForm (Gamma1 N) 14) : ℍ → ℂ)
    rw [map_mul, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos (gammaOne_one_mem_strictPeriods N)]
    exact congrArg₂ (fun x y : PowerSeries ℂ => x * y) hp
      qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit.symm
  have hb : IsIntegralQExp b (eisenstein4 ^ 2 * eisenstein6) := by
    change (eisenstein4 ^ 2 * eisenstein6).map (Int.castRingHom ℂ) =
      qExpansion 1 ((((E₄.pow 2).mul E₆).mcast (by norm_num) : ModularForm 𝒮ℒ 14) : ℍ → ℂ)
    rw [map_mul, map_pow, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      qExpansion_E4_eq_map_eisenstein4, qExpansion_E6_eq_map_eisenstein6]
  have hBcoeff : (intSeriesC K (eisenstein4 ^ 2 * eisenstein6)).coeff (0 : ℤ) = 1 := by
    rw [intSeriesC, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff, map_mul, map_pow,
      constantCoeff_eisenstein4, constantCoeff_eisenstein6, one_pow, one_mul, map_one]
  have hB0 : intSeriesC K (eisenstein4 ^ 2 * eisenstein6) ≠ 0 := by
    intro hz
    rw [hz, HahnSeries.coeff_zero] at hBcoeff
    exact zero_ne_one hBcoeff
  have hr := div_mem_qExpFunctionFieldC a b ha hb hB0
  obtain ⟨c, hc, he⟩ := exists_integer_qEuler_integral_ratio_formula K
  let C : LaurentSeries K := algebraMap K (LaurentSeries K) (c : K)
  have hC : C ≠ 0 := (map_ne_zero (algebraMap K (LaurentSeries K))).mpr (Int.cast_ne_zero.mpr hc)
  have hCm : C ∈ qExpFunctionFieldC K (Gamma1 N) :=
    (qExpFunctionFieldC K (Gamma1 N)).algebraMap_mem (c : K)
  refine ⟨⟨C⁻¹ * (intSeriesC K (p * (PowerSeries.X * dedekindEtaUnit)) /
    intSeriesC K (eisenstein4 ^ 2 * eisenstein6)), mul_mem (inv_mem hCm) hr⟩, ?_⟩
  change C⁻¹ * (intSeriesC K (p * (PowerSeries.X * dedekindEtaUnit)) /
    intSeriesC K (eisenstein4 ^ 2 * eisenstein6)) * qEuler K (jqModC K) = intSeriesC K p
  rw [intSeriesC_mul]
  calc
    _ = C⁻¹ * (intSeriesC K p * (qEuler K (jqModC K) *
        intSeriesC K (PowerSeries.X * dedekindEtaUnit))) /
        intSeriesC K (eisenstein4 ^ 2 * eisenstein6) := by ring
    _ = C⁻¹ * (intSeriesC K p * (C * intSeriesC K (eisenstein4 ^ 2 * eisenstein6))) /
        intSeriesC K (eisenstein4 ^ 2 * eisenstein6) := by rw [he]
    _ = intSeriesC K p := by field_simp

end
end Dubon2026.SourceFunctionField.GammaOne
