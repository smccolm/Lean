import Dubon2026.SourceDiscriminantIntegralExpansion
import Dubon2026.SourceIntegralTracePowerCoefficients

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action
-> actual integral diamond forms. The already proved integer inverse
of the discriminant's eta unit cancels Delta in rational coefficients.
This is the required passage from the rational cusp diamond to the
original modular diamond, using no new formal-product theory. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane

theorem rational_coeff_of_discriminant_mul (F : PowerSeries ℂ)
    (h : ∀ n : ℕ, ((qExpansion 1 ModularForm.discriminant) * F).coeff n ∈
      (algebraMap ℚ ℂ).range) :
    ∀ n : ℕ, F.coeff n ∈ (algebraMap ℚ ℂ).range := by
  let V := dedekindEtaUnitInv.map (Int.castRingHom ℂ)
  have hV : ∀ n, V.coeff n ∈ (algebraMap ℚ ℂ).range := by
    intro n
    rw [show V = dedekindEtaUnitInv.map (Int.castRingHom ℂ) from rfl,
      PowerSeries.coeff_map]
    exact intCast_mem _ _
  have he : ((qExpansion 1 ModularForm.discriminant) * F) * V = PowerSeries.X * F := by
    dsimp only [V]
    rw [qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit, map_mul, PowerSeries.map_X]
    calc
      _ = PowerSeries.X * F * (dedekindEtaUnit.map (Int.castRingHom ℂ) *
          dedekindEtaUnitInv.map (Int.castRingHom ℂ)) := by ring
      _ = _ := by rw [← map_mul, dedekindEtaUnit_mul_inv, map_one, mul_one]
  intro n
  have hi := IntegralTrace.coeff_mul_mem h hV (n + 1)
  rw [he, ← pow_one (PowerSeries.X : PowerSeries ℂ), PowerSeries.coeff_X_pow_mul] at hi
  exact hi

end
end Dubon2026.SourceFunctionField.IntegralSlash
