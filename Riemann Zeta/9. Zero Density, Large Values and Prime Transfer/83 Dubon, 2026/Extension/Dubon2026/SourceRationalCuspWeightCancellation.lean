import Dubon2026.SourceBoundedRationalCuspImage
import Dubon2026.SourceIntegralLaurentWeightFactors

/-! DUB-17/18 -> actual Gamma1 differential realization -> original
integral-ratio field -> bounded denominators of the original cusp form.
Cancel the literal E4/E6 factor using its integer Laurent inverse and
restore the discriminant power using its integer coefficients. The
uniform bound is then read at the original, width-one Fourier indices. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField CongruenceSubgroup ModularForm
open SourceFunctionField.CuspWeightCriterion
open scoped Manifold ModularForm MatrixGroups

theorem gammaOne_rational_series_hasBoundedIntegralCoefficients
    (N : ℕ) [NeZero N] (k : ℤ) (a b m : ℕ)
    (hk : k + 4 * a + 6 * b = 12 * m) (f : CuspForm (Gamma1 N) k)
    (y : PowerSeries ℚ) (hy : y.map (algebraMap ℚ ℂ) = qExpansion 1 f) :
    HasBoundedIntegralCoefficients y := by
  obtain ⟨X, hX, hbound⟩ :=
    exists_bounded_rational_cuspWeightImage_laurent N k a b m hk f y hy
  let D : LaurentSeries ℚ :=
    qExpand ℚ N ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℚ))
  let E : LaurentSeries ℚ :=
    qExpand ℚ N (eisensteinQSeries 4) ^ a * qExpand ℚ N (eisensteinQSeries 6) ^ b
  let Y : LaurentSeries ℚ := qExpand ℚ N y
  have hd := represents_rational_discriminantLaurent N
  have he := represents_rational_eisensteinFactorLaurent N a b
  have hp := gammaOne_one_mem_strictPeriods N
  letI : Fact (IsCusp OnePoint.infty ((Gamma1 N) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods zero_lt_one hp⟩
  have hf := represents_qExpand_rational_series N f y hy
    (SlashInvariantFormClass.periodic_comp_ofComplex f hp) f.holo'
    (ModularFormClass.bdd_at_infty f)
  have hFun : cuspWeightImage (Gamma1 N) k a b m f *
      (⇑CuspForm.discriminant : ℍ → ℂ) ^ m =
      (⇑f : ℍ → ℂ) * eisensteinFactor a b := by
    funext τ
    exact (cuspWeightImage_mul_discriminant (Gamma1 N) k a b m f τ).symm
  have hleft : CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) (X * D ^ m))
      (cuspFunction N ((⇑f : ℍ → ℂ) * eisensteinFactor a b)) := by
    rw [map_mul, map_pow]
    rw [← hFun]
    exact hX.cusp_mul (hd.cusp_pow m)
  have hright : CuspTaylor.Represents (coeffMap (algebraMap ℚ ℂ) (Y * E))
      (cuspFunction N ((⇑f : ℍ → ℂ) * eisensteinFactor a b)) := by
    rw [map_mul]
    exact hf.cusp_mul he
  have hid : X * D ^ m = Y * E :=
    (coeffMap (algebraMap ℚ ℂ)).injective (hleft.eq_series hright)
  have hD : HasBoundedIntegralLaurentCoefficients D := by
    simpa only [D, coeffMap_qExpand, coeffMap_ofPowerSeries] using
      (hasBoundedIntegralLaurentCoefficients_integer_map (K := ℚ)
        (qExpand ℤ N ((PowerSeries.X * dedekindEtaUnit : PowerSeries ℤ) : LaurentSeries ℤ)))
  have hYE : HasBoundedIntegralLaurentCoefficients (Y * E) :=
    hid ▸ hbound.mul (hD.pow m)
  obtain ⟨u, hu⟩ := exists_integer_unit_eisensteinFactorLaurent N a b
  change coeffMap (Int.castRingHom ℚ) (↑u : LaurentSeries ℤ) = E at hu
  have hi := hasBoundedIntegralLaurentCoefficients_integer_map (K := ℚ)
    (↑u⁻¹ : LaurentSeries ℤ)
  have hui : coeffMap (Int.castRingHom ℚ) (↑u : LaurentSeries ℤ) *
      coeffMap (Int.castRingHom ℚ) (↑u⁻¹ : LaurentSeries ℤ) = 1 := by
    rw [← map_mul]
    simp only [Units.mul_inv, map_one]
  have hY : HasBoundedIntegralLaurentCoefficients Y := by
    have ht := hYE.mul hi
    rw [← hu, mul_assoc, hui, mul_one] at ht
    exact ht
  obtain ⟨d, hd0, hc⟩ := hY
  refine ⟨d, hd0, fun n => ?_⟩
  simpa only [Y, qExpand_coeff_mul, HahnSeries.ofPowerSeries_apply_coeff] using
    hc ((N : ℤ) * (n : ℤ))

end
end Dubon2026.SourceFricke
