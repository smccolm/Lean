import Dubon2026.SourceIntegralSlashReducedSeries
import Dubon2026.SourceIntegralDiamondAdditiveSeries

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual reduced slash chart. Reduction preserves
addition and products of the actual integral modular forms. Both identities
are transported from native Fourier and slash identities through the literal
coefficient subring, so they require no relation-preservation certificate.
-/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open IntegralFricke UpperHalfPlane CongruenceSubgroup GammaOne IntegralDiamond
open scoped MatrixGroups ModularForm
local notation "Zbar" => integralClosure ℤ ℂ
variable (N : ℕ) [NeZero N] {K : Type*} [Field K]
  (φ : Zbar →+* K) (hN : (N : K) ≠ 0) (β : SL(2, ℤ))

theorem reducedSlashSeries_add {k : ℤ} (hk : Even k)
    (f g : ModularForm (Gamma1 N) k) {p q : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (hq : IsIntegralQExp g q) :
    reducedSlashSeries N hk (f + g) (integralQExp_add f g hp hq) β φ hN =
      reducedSlashSeries N hk f hp β φ hN + reducedSlashSeries N hk g hq β φ hN := by
  have he : slashCoefficientSeries N hk (f + g) (integralQExp_add f g hp hq) β =
      slashCoefficientSeries N hk f hp β + slashCoefficientSeries N hk g hq β := by
    apply PowerSeries.map_injective (RN N).subtype Subtype.val_injective
    rw [map_add, slashCoefficientSeries_map, slashCoefficientSeries_map,
      slashCoefficientSeries_map]
    change qExpansion (N : ℝ) (((⇑f : ℍ → ℂ) + ⇑g) ∣[k] (β : GL (Fin 2) ℝ)) = _
    rw [SlashAction.add_slash]
    exact ModularForm.qExpansion_add (Nat.cast_pos.mpr (NeZero.pos N))
      (cusp_strictPeriod N β) (ModularForm.translate f (β : GL (Fin 2) ℝ))
        (ModularForm.translate g (β : GL (Fin 2) ℝ))
  unfold reducedSlashSeries
  rw [he, map_add]

theorem reducedSlashSeries_mul {k l : ℤ} (hk : Even k) (hl : Even l)
    (f : ModularForm (Gamma1 N) k) (g : ModularForm (Gamma1 N) l)
    {p q : PowerSeries ℤ} (hp : IsIntegralQExp f p) (hq : IsIntegralQExp g q) :
    reducedSlashSeries N (hk.add hl) (f.mul g) (integralQExp_mul f g hp hq) β φ hN =
      reducedSlashSeries N hk f hp β φ hN * reducedSlashSeries N hl g hq β φ hN := by
  have he : slashCoefficientSeries N (hk.add hl) (f.mul g)
        (integralQExp_mul f g hp hq) β =
      slashCoefficientSeries N hk f hp β * slashCoefficientSeries N hl g hq β := by
    apply PowerSeries.map_injective (RN N).subtype Subtype.val_injective
    rw [map_mul, slashCoefficientSeries_map, slashCoefficientSeries_map,
      slashCoefficientSeries_map]
    change qExpansion (N : ℝ) (((⇑f : ℍ → ℂ) * ⇑g) ∣[k + l] (β : GL (Fin 2) ℝ)) = _
    rw [← ModularForm.SL_slash, ModularForm.mul_slash_SL2]
    exact ModularForm.qExpansion_mul_coe (Nat.cast_pos.mpr (NeZero.pos N))
      (cusp_strictPeriod N β) (ModularForm.translate f (β : GL (Fin 2) ℝ))
        (ModularForm.translate g (β : GL (Fin 2) ℝ))
  unfold reducedSlashSeries
  rw [he, map_mul]

end
end Dubon2026.SourceFunctionField.IntegralSlash
