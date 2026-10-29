import Dubon2026.SourceDiscriminantIntegralExpansion
import Dubon2026.SourceIntegralTracePowerCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus -> uniform level-power
slash integrality -> common integer denominator. Cancel the literal
discriminant Fourier series using the already proved integer eta-unit
inverse. A common denominator for Delta times a form is therefore a
common denominator for the original form; no inverse-integrality
certificate or new formal-product infrastructure is assumed. -/
namespace Dubon2026.SourceFunctionField.IntegralFricke
noncomputable section
open UpperHalfPlane

theorem integral_coeff_of_discriminant_mul (F : PowerSeries ℂ) (d : ℤ)
    (h : ∀ n : ℕ, IsIntegral ℤ ((d : ℂ) *
      ((qExpansion 1 ModularForm.discriminant) * F).coeff n)) :
    ∀ n : ℕ, IsIntegral ℤ ((d : ℂ) * F.coeff n) := by
  let A := PowerSeries.C (d : ℂ) * ((qExpansion 1 ModularForm.discriminant) * F)
  let V := dedekindEtaUnitInv.map (Int.castRingHom ℂ)
  have hA : ∀ n, A.coeff n ∈ (integralClosure ℤ ℂ).toSubring := by
    intro n
    change IsIntegral ℤ (A.coeff n)
    simpa only [A, PowerSeries.coeff_C_mul] using h n
  have hV : ∀ n, V.coeff n ∈ (integralClosure ℤ ℂ).toSubring := by
    intro n
    change IsIntegral ℤ (V.coeff n)
    rw [show V = dedekindEtaUnitInv.map (Int.castRingHom ℂ) from rfl,
      PowerSeries.coeff_map]
    exact isIntegral_algebraMap
  have he : A * V = PowerSeries.X * (PowerSeries.C (d : ℂ) * F) := by
    dsimp only [A, V]
    rw [qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, map_mul, PowerSeries.map_X]
    calc
      _ = PowerSeries.X * (PowerSeries.C (d : ℂ) * F) *
          (dedekindEtaUnit.map (Int.castRingHom ℂ) *
            dedekindEtaUnitInv.map (Int.castRingHom ℂ)) := by ring
      _ = _ := by rw [← map_mul, dedekindEtaUnit_mul_inv, map_one, mul_one]
  intro n
  have hi := IntegralTrace.coeff_mul_mem hA hV (n + 1)
  change IsIntegral ℤ ((A * V).coeff (n + 1)) at hi
  rw [he] at hi
  rw [← pow_one (PowerSeries.X : PowerSeries ℂ), PowerSeries.coeff_X_pow_mul,
    PowerSeries.coeff_C_mul] at hi
  exact hi

end
end Dubon2026.SourceFunctionField.IntegralFricke
