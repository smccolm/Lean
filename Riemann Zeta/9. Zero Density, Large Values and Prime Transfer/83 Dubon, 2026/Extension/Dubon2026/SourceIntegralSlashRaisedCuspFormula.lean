import Dubon2026.SourceIntegralSlashRaisedLevelOne
import Dubon2026.SourceIntegralSlashCuspTriangular

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> second full-base coordinate of the actual cusp
chart. The exact matrix factorization and full modular invariance reduce the
actual raised form at the cusp to its triangular translate, with the literal
d^(-k) multiplier. Native slash normalization supplies every factor. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

theorem gammaOneRaisedLevelOne_slash (N a d : ℕ) [NeZero N] [NeZero a] [NeZero d]
    (had : a * d = N) {k : ℤ} (f : ModularForm 𝒮ℒ k) (g : SL(2, ℤ))
    (B : ℕ) (c t : ℤ) (hc : g 1 0 = a * c)
    (ht : g 1 1 * a - g 1 0 * (B : ℤ) = N * t) :
    (⇑(gammaOneRaisedLevelOne N f) : ℍ → ℂ) ∣[k] (g : GL (Fin 2) ℝ) =
      (d : ℂ) ^ (-k) • fun τ => f (heckeTriangularMatrix a d B • τ) := by
  obtain ⟨δ, hδ⟩ := levelRaise_mul_cusp_triangular N a d had g B c t hc ht
  have hs : (⇑f : ℍ → ℂ) ∣[k] (δ : GL (Fin 2) ℝ) = f :=
    SlashInvariantForm.slash_action_eqn f _ ⟨δ, rfl⟩
  rw [coe_gammaOneRaisedLevelOne, ← ModularForm.SL_slash, ModularForm.SL_smul_slash,
    ModularForm.SL_slash, ← SlashAction.slash_mul, hδ, SlashAction.slash_mul, hs]
  funext τ
  rw [Pi.smul_apply, smul_eq_mul, heckeTriangular_slash_apply,
    Pi.smul_apply, smul_eq_mul, heckeTriangularMatrix_smul]
  have ha : (a : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne a
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hN : (N : ℂ) = a * d := by exact_mod_cast had.symm
  rw [hN, mul_zpow]
  calc
    _ = ((a : ℂ) ^ (1 - k) * (a : ℂ) ^ (k - 1)) *
        ((d : ℂ) ^ (1 - k) * (d : ℂ) ^ (-1 : ℤ)) *
        f (heckeUpperPoint d B (levelRaiseMatrix a • τ)) := by rw [zpow_neg_one]; ring
    _ = _ := by
      rw [← zpow_add₀ ha, ← zpow_add₀ hd,
        show (1 - k) + (k - 1) = 0 by ring,
        show (1 - k) + (-1) = -k by ring, zpow_zero, one_mul]

end
end Dubon2026.SourceFunctionField.IntegralSlash
