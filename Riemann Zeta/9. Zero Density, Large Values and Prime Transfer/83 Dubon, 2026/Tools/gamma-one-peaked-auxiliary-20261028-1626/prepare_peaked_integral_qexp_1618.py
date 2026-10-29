from pathlib import Path
s=Path(__file__).parent
c=(s/'anthropic-peaked-core-1533/S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow.lean.txt').read_text(encoding='utf-8')
a=c.index('theorem solution');b=c.index(' := by',a)
sig=c[a:b].replace('theorem solution','theorem qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow').replace('ModularCurve.siegelFun','siegelFun')
header='''import SourcePeakedWidthOneIdentification1617a

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> integral width-one expansion.
The real modular form is identified with the constructed shifted series.
Its exact vanishing range, nonzero leading coefficient, level-cleared leading
inverse and all level-cleared coefficients follow from proved coefficient
algebra. This is the exact source theorem, with its order relation visible.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Coefficients
noncomputable section
open Complex UpperHalfPlane PowerSeries Filter Topology FiniteExpansion
open scoped MatrixGroups ModularForm

'''
proof=''' := by
  have hcoef := qExpansion_one_coeff_adjusted N m t ϑ hϑ m₀ hm₀
  refine ⟨12 * N * ∑ r : ZMod N, ∑ s : ZMod N, m r s, fun n hn => ?_, ?_, ?_, fun n => ?_⟩
  · rw [hcoef, coeff_adjustedSeries, if_neg (not_le.mpr (Nat.mul_lt_mul_left (NeZero.pos N) |>.mpr hn)), mul_zero]
  · rw [hcoef, coeff_adjustedSeries_leading]
    exact mul_ne_zero (phase_ne_zero N m) (productSeries_zero_ne_zero N m hm0)
  · rw [hcoef, coeff_adjustedSeries_leading]
    exact integral_level_inverse_phase_leading N m hm0
  · rw [hcoef]
    have hN : IsIntegral ℤ (N : ℂ) := by
      exact_mod_cast (isIntegral_algebraMap : IsIntegral ℤ ((N : ℤ) : ℂ))
    exact (hN.pow _).mul (integral_adjustedSeries N m t m₀ _)

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Coefficients
'''
f=s/'SourcePeakedIntegralQExpansion1618a.lean';assert not f.exists();f.write_text(header+sig+proof,encoding='utf-8')
