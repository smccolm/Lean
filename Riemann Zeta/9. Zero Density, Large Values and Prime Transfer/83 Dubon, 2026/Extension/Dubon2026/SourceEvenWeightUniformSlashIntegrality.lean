import Dubon2026.SourceIntegralSlashSMove
import Dubon2026.SourceIntegralSlashTMove
import Dubon2026.SourceQExpansionPeriodWidth
import Dubon2026.SourceIntegralTraceModularForm

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action.
Every actual SL2 translate of an even-weight Gamma1 modular form has
one level power clearing all width-M Fourier coefficients. The proof
uses the actual S and T transport and native SL2 generation. The
original integral q-expansion consumer is explicit. Even-weight
representatives of the original ratio field were proved upstream;
neither the field nor the Dubon source contract is changed. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
variable {M : ℕ} [NeZero M] {k : ℤ}

theorem exists_level_power_cusp_one (f : ModularForm (Gamma1 M) k) {a : ℕ}
    (hF : ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ a * (qExpansion 1 f).coeff n)) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ b *
      (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n) := by
  refine ⟨a, fun n => ?_⟩
  have hone : ((1 : SL(2, ℤ)) : GL (Fin 2) ℝ) = 1 := map_one (mapGL ℝ)
  rw [hone, SlashAction.slash_one, SourceFricke.qExpansion_coeff_width f (NeZero.ne M)
    (SlashInvariantFormClass.periodic_comp_ofComplex f (SourceFricke.gammaOne_one_mem_strictPeriods M))
    f.holo' (ModularFormClass.bdd_at_infty f)]
  split_ifs
  · exact hF _
  · rw [mul_zero]
    exact isIntegral_zero

theorem exists_level_power_integral_even_slash_of_level_power (hk : Even k)
    (f : ModularForm (Gamma1 M) k) {a : ℕ}
    (hF : ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ a * (qExpansion 1 f).coeff n))
    (γ : SL(2, ℤ)) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ b *
      (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n) := by
  have hmem : γ ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]
    exact Subgroup.mem_top γ
  induction hmem using Subgroup.closure_induction_right with
  | one => exact exists_level_power_cusp_one f hF
  | mul_right x hx y hy ih =>
    rcases hy with rfl | rfl
    · exact exists_level_power_cusp_mul_S hk f x ih
    · simpa only [zpow_one] using exists_level_power_cusp_mul_T_zpow f x 1 ih
  | mul_inv_cancel x hx y hy ih =>
    rcases hy with rfl | rfl
    · have he : (⇑f : ℍ → ℂ) ∣[k] ((x * ModularGroup.S⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) =
          (⇑f : ℍ → ℂ) ∣[k] ((x * ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
        rw [ModularGroup.S_inv, mul_neg]
        exact IntegralTrace.slash_neg_even hk f (x * ModularGroup.S)
      rw [he]
      exact exists_level_power_cusp_mul_S hk f x ih
    · simpa only [zpow_neg_one] using exists_level_power_cusp_mul_T_zpow f x (-1) ih

theorem exists_level_power_integral_even_slash_coefficients (hk : Even k)
    (f : ModularForm (Gamma1 M) k) {p : PowerSeries ℤ}
    (hp : GammaOne.IsIntegralQExp f p) (γ : SL(2, ℤ)) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((M : ℂ) ^ b *
      (qExpansion (M : ℝ) ((⇑f : ℍ → ℂ) ∣[k] (γ : GL (Fin 2) ℝ))).coeff n) := by
  apply exists_level_power_integral_even_slash_of_level_power hk f (a := 0) _ γ
  intro n
  rw [pow_zero, one_mul]
  have hn := congrArg (PowerSeries.coeff n) hp
  rw [PowerSeries.coeff_map] at hn
  rw [← hn]
  exact isIntegral_algebraMap

end
end Dubon2026.SourceFunctionField.IntegralSlash
