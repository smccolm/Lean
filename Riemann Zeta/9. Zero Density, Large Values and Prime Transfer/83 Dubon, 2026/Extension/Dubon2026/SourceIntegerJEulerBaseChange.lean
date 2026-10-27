import Dubon2026.SourceIntegerJEulerNormalization
import Dubon2026.SourceGammaOneFunctionField

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio coefficient. Transport the proved integer j-derivative
normalization to the actual coefficient field. The scalar remains an
explicit nonzero integer, so it is invertible in characteristic zero. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceDifferential SourceFricke

theorem exists_integer_qEuler_integral_ratio_formula (K : Type*) [Field K] :
    ∃ c : ℤ, c ≠ 0 ∧
      qEuler K (jqModC K) * intSeriesC K (PowerSeries.X * dedekindEtaUnit) =
        algebraMap K (LaurentSeries K) (c : K) *
          intSeriesC K (eisenstein4 ^ 2 * eisenstein6) := by
  obtain ⟨c, hc, he⟩ := exists_integer_qEuler_jqModC_formula
  refine ⟨c, hc, ?_⟩
  let ι : LaurentSeries ℤ →+* LaurentSeries K := coeffMap (Int.castRingHom K)
  have hQ : ι (qEuler ℤ (jqModC ℤ)) = qEuler K (jqModC K) := by
    rw [← map_jqModC (Int.castRingHom K)]
    apply HahnSeries.ext
    funext n
    simp only [ι, coeffMap_coeff, qEuler_coeff, Int.coe_castRingHom,
      Int.cast_mul, Int.cast_id, HahnSeries.map_coeff]
  have hC : ι (HahnSeries.C c) = algebraMap K (LaurentSeries K) (c : K) := by
    rw [algebraMap_laurentSeries_apply_alt]
    exact coeffMap_single (Int.castRingHom K) 0 c
  have hD : ι ((PowerSeries.X * dedekindEtaUnit : PowerSeries ℤ) : LaurentSeries ℤ) =
      intSeriesC K (PowerSeries.X * dedekindEtaUnit) := coeffMap_ofPowerSeries _ _
  have hE : ι ((eisenstein4 : LaurentSeries ℤ) ^ 2 * (eisenstein6 : LaurentSeries ℤ)) =
      intSeriesC K (eisenstein4 ^ 2 * eisenstein6) := by
    rw [← map_pow, ← map_mul]
    exact coeffMap_ofPowerSeries _ _
  have h := congrArg ι he
  rw [map_mul ι, map_mul ι, hQ, hD, hC, hE] at h
  exact h

end
end Dubon2026.SourceFunctionField.GammaOne
