import Dubon2026.SourceIntegralEisensteinSix

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace -> level-one coefficient
criterion. The trace's weight adjustment uses the original E4 and E6,
with integral expansions and unit constant coefficient. Their existing
native Fourier formulas are reused; no Bernoulli recalculation is needed.
This is the specialization of the weight factor in the pinned Anthropic
trace proof, Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one. -/
namespace Dubon2026.SourceFunctionField.LevelOneCoefficientRing
noncomputable section
open UpperHalfPlane ModularForm SourceFricke
open scoped MatrixGroups

private theorem integral_e6 :
    eisenstein6.map (Int.castRingHom ℂ) = qExpansion 1 (E₆ : ℍ → ℂ) := by
  have h := eisensteinQSeries_map (k := 6) (by norm_num) (by decide)
  rw [eisensteinQSeries_six_eq_integer_map] at h
  ext n
  have hn := congrArg (fun f : PowerSeries ℂ => f.coeff n) h
  simpa only [PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast] using hn

theorem exists_integral_weight_factor (a b : ℕ) (e : ℤ)
    (he : 4 * (a : ℤ) + 6 * (b : ℤ) = e) :
    ∃ (E : ModularForm 𝒮ℒ e) (P : PowerSeries ℤ),
      P.map (Int.castRingHom ℂ) = qExpansion 1 (E : ℍ → ℂ) ∧
        PowerSeries.constantCoeff P = 1 := by
  have hw : (a : ℤ) * 4 + (b : ℤ) * 6 = e := by rw [← he]; ring
  refine ⟨ModularForm.mcast hw ((E₄.pow a).mul (E₆.pow b)),
    eisenstein4 ^ a * eisenstein6 ^ b, ?_, ?_⟩
  · rw [map_mul, map_pow, map_pow, ← qExpansion_E4_eq_map_eisenstein4, integral_e6,
      ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  · rw [map_mul, map_pow, map_pow, constantCoeff_eisenstein4, constantCoeff_eisenstein6,
      one_pow, one_pow, one_mul]

end
end Dubon2026.SourceFunctionField.LevelOneCoefficientRing
