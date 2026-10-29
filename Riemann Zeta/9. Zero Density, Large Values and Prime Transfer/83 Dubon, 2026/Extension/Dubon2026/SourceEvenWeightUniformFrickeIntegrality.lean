import Dubon2026.SourceEvenWeightFrickeCommonDenominator

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action
-> uniform level-power slash integrality. The actual even-weight Fricke
transform has one level power clearing every Fourier coefficient.
The trace, peaked auxiliary and common integer denominator are all
constructed upstream; none remains a premise. Level one is handled
directly by the original modular invariance. Even-weight integral
ratios represent the unchanged original function field. The remaining
SL2 slash transport and reduced field action are separate obligations. -/
namespace Dubon2026.SourceFunctionField.IntegralFricke
noncomputable section
open UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem exists_level_power_integral_even_fricke_coefficients
    (N : ℕ) [NeZero N] {k : ℤ} (hk : Even k)
    (F : ModularForm (Gamma1 N) k) (a : ℕ)
    (hF : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (qExpansion 1 F).coeff n)) :
    ∃ b : ℕ, ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b *
      (qExpansion 1 ((⇑F : ℍ → ℂ) ∣[k] frickeMatrix N)).coeff n) := by
  by_cases hN : N = 1
  · subst N
    have hS : frickeMatrix 1 = ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
      ext i j
      rw [frickeMatrix_val]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]
    have hmem : ModularGroup.S ∈ Gamma1 1 := by
      rw [Gamma1_mem]
      exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
    have he : (⇑F : ℍ → ℂ) ∣[k] frickeMatrix 1 = ⇑F := by
      rw [hS]
      exact SlashInvariantFormClass.slash_action_eq F _ ⟨ModularGroup.S, hmem, rfl⟩
    refine ⟨a, fun n => ?_⟩
    rw [he]
    exact hF n
  · have hN2 : 2 ≤ N := by have := NeZero.pos N; omega
    obtain ⟨D, hD, hcommon⟩ := exists_common_nat_denominator_even_fricke hN2 hk F hF
    exact ⟨D, even_weight_level_power_fricke_of_common_denominator hN2 hk F hD hF hcommon⟩

end
end Dubon2026.SourceFunctionField.IntegralFricke
