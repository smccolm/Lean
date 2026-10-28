import Dubon2026.SourceGammaOneHeckeFieldInclusion
import Dubon2026.SourceGammaOneModularRatios

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> beta analytic
degeneracy map. The already proved coefficient formula identifies the
Laurent expansion of the actual stretched form with q-dilation.
Its nonvanishing permits the existing equal-weight ratio realization. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups

theorem modularStretch_qL (M d : ℕ) [NeZero d] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ModularRatios.qL (modularStretch M d f) = qExpand ℂ d (ModularRatios.qL f) := by
  ext n
  by_cases hd : (d : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hd
    rw [qExpand_coeff_mul]
    by_cases hm : 0 ≤ m
    · lift m to ℕ using hm
      simp only [ModularRatios.qL, ← Nat.cast_mul, HahnSeries.ofPowerSeries_apply_coeff]
      rw [modularStretch_coeff]
      simp [Nat.pos_of_neZero d]
    · simp only [ModularRatios.qL]
      rw [ofPowerSeries_coeff_of_neg _ (mul_neg_of_pos_of_neg
        (by exact_mod_cast Nat.pos_of_neZero d) (lt_of_not_ge hm)),
        ofPowerSeries_coeff_of_neg _ (lt_of_not_ge hm)]
  · rw [qExpand_coeff_of_not_dvd d _ hd]
    rcases le_or_gt 0 n with hn | hn
    · lift n to ℕ using hn
      simp only [ModularRatios.qL, HahnSeries.ofPowerSeries_apply_coeff]
      rw [modularStretch_coeff, if_neg (fun hdn => hd (Int.natCast_dvd_natCast.mpr hdn))]
    · exact ofPowerSeries_coeff_of_neg _ hn

theorem modularStretch_ne_zero (M d : ℕ) [NeZero d] {k : ℤ}
    (hT : ModularGroup.T ∈ Gamma1 M)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    modularStretch M d f ≠ 0 := by
  intro hz
  have he := modularStretch_qL M d f
  rw [hz] at he
  have hz' : ModularRatios.qL (0 : ModularForm
      ((Gamma1 M ⊓ Gamma0 (d * M)).map (mapGL ℝ)) k) = 0 := by
    simp only [ModularRatios.qL, ModularForm.coe_zero,
      UpperHalfPlane.qExpansion_zero, PowerSeries.coe_zero]
  rw [hz'] at he
  exact (map_ne_zero (qExpand ℂ d)).mpr (ModularRatios.qL_ne_zero hT f hf) he.symm

end
end Dubon2026.SourceFunctionField.GammaOne
