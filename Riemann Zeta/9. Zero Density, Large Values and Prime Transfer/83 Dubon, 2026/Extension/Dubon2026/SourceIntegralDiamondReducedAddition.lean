import Dubon2026.SourceIntegralDiamondRatioClosure

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action.
Addition is derived from the already proved difference law and exact zero
preservation. This avoids rebuilding integral common-exponent witnesses.
The resulting laws are required by the actual original-field homomorphism. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

theorem integralQExp_neg {N : ℕ} {k : ℤ} (f : ModularForm (Gamma1 N) k)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) : IsIntegralQExp (-f) (-p) := by
  simpa only [ModularForm.coe_zero, zero_sub] using integralQExp_sub 0 f (integralQExp_zero N k) hp

theorem reducedDiamond_zero (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    {k : ℤ} (hk : Even k) (δ : Gamma0 N) :
    reducedDiamond N ℓ hk δ 0 (integralQExp_zero N k) = 0 :=
  (reducedDiamond_zero_iff N ℓ hℓN hk δ 0 (integralQExp_zero N k)).mpr (map_zero _)

theorem reducedDiamond_neg (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    {k : ℤ} (hk : Even k) (δ : Gamma0 N) (f : ModularForm (Gamma1 N) k)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) :
    reducedDiamond N ℓ hk δ (-f) (integralQExp_neg f hp) =
      -reducedDiamond N ℓ hk δ f hp := by
  have hs := reducedDiamond_sub N ℓ hℓN hk δ 0 f (integralQExp_zero N k) hp
  simpa only [zero_sub, reducedDiamond_zero N ℓ hℓN hk δ] using hs

theorem reducedDiamond_add (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    {k : ℤ} (hk : Even k) (δ : Gamma0 N) (f h : ModularForm (Gamma1 N) k)
    {p q : PowerSeries ℤ} (hp : IsIntegralQExp f p) (hq : IsIntegralQExp h q) :
    reducedDiamond N ℓ hk δ (f + h) (integralQExp_add f h hp hq) =
      reducedDiamond N ℓ hk δ f hp + reducedDiamond N ℓ hk δ h hq := by
  have hs := reducedDiamond_sub N ℓ hℓN hk δ f (-h) hp (integralQExp_neg h hq)
  simpa only [sub_neg_eq_add, reducedDiamond_neg N ℓ hℓN hk δ h hq] using hs

end
end Dubon2026.SourceFunctionField.IntegralDiamond
