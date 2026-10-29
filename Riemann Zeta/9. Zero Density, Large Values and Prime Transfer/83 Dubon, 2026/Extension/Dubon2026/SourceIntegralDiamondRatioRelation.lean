import Dubon2026.SourceIntegralDiamondReducedOperations

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action.
The actual reduced diamond respects equality of arbitrary integral ratios,
including representatives of different even weights. Both cross-products
have weight k+l, so native multiplication/subtraction and the proved zero
equivalence replace weight casts and separate exponent-clearing machinery.
No relation-preservation hypothesis is assumed. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

theorem reducedDiamond_ratio_eq (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) {k l : ℤ} (hk : Even k) (hl : Even l) (δ : Gamma0 N)
    (f g : ModularForm (Gamma1 N) k) (f' g' : ModularForm (Gamma1 N) l)
    {pf pg pf' pg' : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hf' : IsIntegralQExp f' pf') (hg' : IsIntegralQExp g' pg')
    (hg0 : red ℓ pg ≠ 0) (hg'0 : red ℓ pg' ≠ 0)
    (he : red ℓ pf / red ℓ pg = red ℓ pf' / red ℓ pg') :
    reducedDiamond N ℓ hk δ f hf / reducedDiamond N ℓ hk δ g hg =
      reducedDiamond N ℓ hl δ f' hf' / reducedDiamond N ℓ hl δ g' hg' := by
  have hc : red ℓ (pf * pg' - pg * pf') = 0 := by
    rw [map_sub, map_mul, map_mul, sub_eq_zero]
    simpa only [mul_comm] using (div_eq_div_iff hg0 hg'0).mp he
  have hz := (reducedDiamond_zero_iff N ℓ hℓN (hk.add hl) δ
    (f.mul g' - g.mul f')
    (integralQExp_sub (f.mul g') (g.mul f')
      (integralQExp_mul f g' hf hg') (integralQExp_mul g f' hg hf'))).mpr hc
  rw [reducedDiamond_sub N ℓ hℓN (hk.add hl) δ (f.mul g') (g.mul f')
      (integralQExp_mul f g' hf hg') (integralQExp_mul g f' hg hf'),
    reducedDiamond_mul N ℓ hℓN hk hl δ f g' hf hg',
    reducedDiamond_mul N ℓ hℓN hk hl δ g f' hg hf', sub_eq_zero] at hz
  apply (div_eq_div_iff (reducedDiamond_ne_zero N ℓ hℓN hk δ g hg hg0)
    (reducedDiamond_ne_zero N ℓ hℓN hl δ g' hg' hg'0)).mpr
  simpa only [mul_comm] using hz

end
end Dubon2026.SourceFunctionField.IntegralDiamond
