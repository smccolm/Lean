import Dubon2026.SourceIntegralDiamondReducedAddition

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action.
Actual slash composition identifies the twice-cleared diamond with the
product matrix and the sum of clearing exponents. Normalized reduction
then proves the precise scaling law needed to compose field pullbacks.
Only the already constructed integer witnesses are used. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

theorem scaledDiamond_comp (N : ℕ) (γ δ : Gamma0 N) (a c : ℕ) {k : ℤ}
    (f : ModularForm (Gamma1 N) k) :
    scaledDiamond N δ c (scaledDiamond N γ a f) =
      scaledDiamond N (γ * δ) (c + a) f := by
  apply DFunLike.coe_injective
  dsimp only
  rw [coe_scaledDiamond, coe_scaledDiamond, coe_scaledDiamond,
    ModularForm.SL_smul_slash, smul_smul, ← SlashAction.slash_mul, pow_add]
  rfl

theorem reducedDiamond_scaled_comp (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) {k : ℤ} (hk : Even k) (γ δ : Gamma0 N)
    (f : ModularForm (Gamma1 N) k) {p P : PowerSeries ℤ} {a : ℕ}
    (hp : IsIntegralQExp f p) (hP : IsIntegralQExp (scaledDiamond N γ a f) P) :
    reducedDiamond N ℓ hk δ (scaledDiamond N γ a f) hP =
      (N : LaurentSeries (ZMod ℓ)) ^ a * reducedDiamond N ℓ hk (γ * δ) f hp := by
  let w := diamondWitness N hk δ (scaledDiamond N γ a f) hP
  have hw : IsIntegralQExp (scaledDiamond N (γ * δ) (w.val.1 + a) f) w.val.2 := by
    rw [← scaledDiamond_comp]
    exact w.property
  rw [reducedDiamond_eq N ℓ hℓN hk δ (scaledDiamond N γ a f) hP w.property,
    reducedDiamond_eq N ℓ hℓN hk (γ * δ) f hp hw,
    normalizedRed, normalizedRed, pow_add]
  field_simp [level_ne_zero N ℓ hℓN]

end
end Dubon2026.SourceFunctionField.IntegralDiamond
