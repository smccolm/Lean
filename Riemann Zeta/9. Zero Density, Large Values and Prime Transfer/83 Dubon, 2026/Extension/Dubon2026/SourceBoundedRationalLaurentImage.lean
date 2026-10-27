import Dubon2026.SourceBoundedIntegralLaurentAlgebra
import Dubon2026.SourceIntegralRationalLaurentSeries
import Mathlib.Data.Rat.Floor

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded rational Laurent coefficients. A uniform
integral bound gives an actual integer Laurent series after scaling. The
zero-preserving floor map transports the existing Laurent support, and
normality of Z in Q identifies every scaled coefficient exactly. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem HasBoundedIntegralLaurentCoefficients.exists_integer_series
    {f : LaurentSeries ℚ} (hf : HasBoundedIntegralLaurentCoefficients f) :
    ∃ d : ℤ, ∃ F : LaurentSeries ℤ, d ≠ 0 ∧
      coeffMap (algebraMap ℤ ℚ) F = (d : LaurentSeries ℚ) * f := by
  obtain ⟨d, hd, hi⟩ := hf
  let g := (d : LaurentSeries ℚ) * f
  have hg (n : ℤ) : IsIntegral ℤ (g.coeff n) := by
    dsimp [g]
    rw [← HahnSeries.single_zero_intCast d, HahnSeries.coeff_single_zero_mul]
    exact hi n
  let π : ZeroHom ℚ ℤ := ⟨Int.floor, Int.floor_zero⟩
  refine ⟨d, g.map π, hd, ?_⟩
  ext n
  rw [coeffMap_coeff, HahnSeries.map_coeff]
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (hg n)
  change (z : ℚ) = g.coeff n at hz
  change (⌊g.coeff n⌋ : ℚ) = g.coeff n
  rw [← hz, Int.floor_intCast]

theorem hasBoundedIntegralLaurentCoefficients_of_integer_series
    {f : LaurentSeries ℚ} (d : ℤ) (hd : d ≠ 0) (F : LaurentSeries ℤ)
    (hF : coeffMap (algebraMap ℤ ℚ) F = (d : LaurentSeries ℚ) * f) :
    HasBoundedIntegralLaurentCoefficients f := by
  refine ⟨d, hd, fun n => ?_⟩
  have he := congrArg (fun g : LaurentSeries ℚ => g.coeff n) hF
  dsimp only at he
  rw [coeffMap_coeff, ← HahnSeries.single_zero_intCast d, HahnSeries.coeff_single_zero_mul] at he
  rw [← he]
  exact isIntegral_algebraMap

end
end Dubon2026.SourceFunctionField
