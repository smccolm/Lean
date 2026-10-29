import Dubon2026.SourceIntegralSlashDiamondChart

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual diamond-chart equivariance. Compute the
chart on a literal level-cleared diamond generator. The level-one discriminant
has the same reduced series at every cusp, so its powers do not introduce an
extra multiplier. This is the exact generator identity required to cancel the
clearing scalar in the actual diamond action. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open IntegralDiamond UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm
local notation "Zbar" => integralClosure ℤ ℂ
variable (N : ℕ) [NeZero N] {K : Type*} [Field K]
  (φ : Zbar →+* K) (hN : (N : K) ≠ 0)

theorem ofPowerSeries_reducedSlashSeries_discriminant (β : SL(2, ℤ)) :
    HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N (by decide)
      (gammaOneDiscriminant N) (integralQExp_gammaOneDiscriminant N) β φ hN) =
      qExpand K N (intSeriesC K discriminantSeries) :=
  ofPowerSeries_reducedSlashSeries_levelOne N φ hN β (by decide)
    (CuspForm.discriminant : ModularForm 𝒮ℒ 12) (integralQExp_gammaOneDiscriminant N)

theorem normalizedSlashValue_scaledDiamond (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    {r : ℕ} (f : ModularForm (Gamma1 N) (12 * (r : ℤ))) {p P : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (γ : Gamma0 N) (a : ℕ)
    (hP : IsIntegralQExp (scaledDiamond N γ a f) P) (β : SL(2, ℤ)) :
    normalizedSlashValue N φ hN β (intSeriesC K P / intSeriesC K discriminantSeries ^ r) =
      HahnSeries.C ((N : K) ^ a) * normalizedSlashValue N φ hN (γ.val * β)
        (intSeriesC K p / intSeriesC K discriminantSeries ^ r) := by
  rw [normalizedSlashValue_eq N φ hN β ℓ (scaledDiamond N γ a f) hP rfl,
    normalizedSlashValue_eq N φ hN (γ.val * β) ℓ f hp rfl,
    reducedSlashSeries_scaledDiamond N φ hN _ f hp γ a hP β,
    map_mul, HahnSeries.ofPowerSeries_C,
    ofPowerSeries_reducedSlashSeries_discriminant,
    ofPowerSeries_reducedSlashSeries_discriminant, mul_div_assoc]

end
end Dubon2026.SourceFunctionField.IntegralSlash
