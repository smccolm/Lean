import Dubon2026.SourceIntegralDiamondScalarNormalizedAction

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> actual toric-coordinate diamond action. Extend the already
proved prime-field action formula to arbitrary same-even-weight integral
ratios over the residue coefficient field. This is needed for the exact
weight-six B*E4/E6 and weight-four D/E4 ratios; normalized-generator
expansion is unnecessary here. The action and coefficient extension are
the existing proved objects. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne IntegralSlash ReducedDegreeTransport
open scoped MatrixGroups ModularForm
attribute [local instance] originalFieldScalarAlgebra

theorem reducedFieldActionOver_integral_ratio (K : Type*) [Field K] (N ℓ : ℕ)
    [NeZero N] [Fact ℓ.Prime] [Algebra (ZMod ℓ) K] (hℓN : ¬ ℓ ∣ N)
    (γ : Gamma0 N) {k : ℤ} (hk : Even k)
    (f g F G : ModularForm (Gamma1 N) k) {p q P Q : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (hq : IsIntegralQExp g q) (hq0 : red ℓ q ≠ 0)
    (hP : IsIntegralQExp F P) (hQ : IsIntegralQExp G Q)
    (hF : (f : ℍ → ℂ) ∣[k] (γ⁻¹).val = F)
    (hG : (g : ℍ → ℂ) ∣[k] (γ⁻¹).val = G)
    (x : qExpFunctionFieldC K (Gamma1 N))
    (hx : (x : LaurentSeries K) = intSeriesC K p / intSeriesC K q) :
    (reducedFieldActionOver K N ℓ hℓN γ x : LaurentSeries K) =
      intSeriesC K P / intSeriesC K Q := by
  have hq0' : intSeriesC (ZMod ℓ) q ≠ 0 := by simpa only [red_apply] using hq0
  let x₀ : qExpFunctionFieldC (ZMod ℓ) (Gamma1 N) :=
    ⟨intSeriesC (ZMod ℓ) p / intSeriesC (ZMod ℓ) q,
      div_mem_qExpFunctionFieldC f g hp hq hq0'⟩
  have hp' : IsIntegralQExp (scaledDiamond N γ⁻¹ 0 f) P := by
    rw [coe_scaledDiamond, pow_zero, one_smul]
    change IsIntegralQExp ((f : ℍ → ℂ) ∣[k] (γ⁻¹).val) P
    rw [hF]
    exact hP
  have hq' : IsIntegralQExp (scaledDiamond N γ⁻¹ 0 g) Q := by
    rw [coe_scaledDiamond, pow_zero, one_smul]
    change IsIntegralQExp ((g : ℍ → ℂ) ∣[k] (γ⁻¹).val) Q
    rw [hG]
    exact hQ
  have hprime : (reducedFieldAction N ℓ hℓN γ x₀ : LaurentSeries (ZMod ℓ)) =
      intSeriesC (ZMod ℓ) P / intSeriesC (ZMod ℓ) Q := by
    rw [reducedFieldAction_apply,
      reducedFieldPull_eq N ℓ hℓN γ⁻¹ x₀ hk f g hp hq hq0
        (by simp only [x₀, red_apply]),
      reducedDiamond_eq N ℓ hℓN hk γ⁻¹ f hp hp',
      reducedDiamond_eq N ℓ hℓN hk γ⁻¹ g hq hq',
      normalizedRed, normalizedRed, pow_zero, div_one, div_one, red_apply, red_apply]
  have he : originalFieldCoefficientHom (L := K) (Gamma1 N) x₀ = x := by
    apply Subtype.ext
    rw [originalFieldCoefficientHom_coe, hx]
    change coeffMap (algebraMap (ZMod ℓ) K)
      (intSeriesC (ZMod ℓ) p / intSeriesC (ZMod ℓ) q) = _
    rw [map_div₀, coeffMap_intSeries, coeffMap_intSeries]
  rw [← he, reducedFieldActionOver_coeff, originalFieldCoefficientHom_coe, hprime,
    map_div₀, coeffMap_intSeries, coeffMap_intSeries]

end
end Dubon2026.SourceFunctionField.IntegralDiamond
