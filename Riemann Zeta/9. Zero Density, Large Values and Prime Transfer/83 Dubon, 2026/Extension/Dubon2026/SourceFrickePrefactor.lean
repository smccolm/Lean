import Dubon2026.SourceEisensteinRationalSeries
import Dubon2026.SourceEllipticPeriodModularCurve

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 characters -> Picard/H1 and diamond comparison -> differential
realization -> rational Fourier structure -> faithful Fricke generators.
The existing actual period map and exact kernel give separation at a
single point where E4 E6 is nonzero. That point exists by the native
constant Fourier coefficient, without any injectivity assumption. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SourceEllipticPeriod
open scoped Manifold MatrixGroups ModularForm PeriodPair

theorem qExpansion_E4E6_coeff_zero {N : ℕ} (hN : N ≠ 0) :
    (qExpansion N (⇑E₄ * ⇑E₆ : ℍ → ℂ)).coeff 0 = 1 := by
  rw [← e4e6QSeries_map hN, PowerSeries.coeff_map]
  simp [e4e6QSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul, eisensteinQSeries]

theorem exists_E4E6_ne_zero : ∃ τ : ℍ, E₄ τ * E₆ τ ≠ 0 := by
  by_contra! h
  have he : (⇑E₄ * ⇑E₆ : ℍ → ℂ) = 0 := funext h
  have hq := qExpansion_E4E6_coeff_zero (N := 1) one_ne_zero
  rw [he, qExpansion_zero, map_zero] at hq
  exact zero_ne_one hq

theorem frickePrefactor_ne_zero {τ : ℍ} (hτ : E₄ τ * E₆ τ ≠ 0) :
    -(E₄ τ * E₆ τ / discriminant τ) / 2592 ≠ 0 :=
  div_ne_zero (neg_ne_zero.mpr (div_ne_zero hτ (discriminant_ne_zero τ))) (by norm_num)

end
end Dubon2026.SourceFricke
