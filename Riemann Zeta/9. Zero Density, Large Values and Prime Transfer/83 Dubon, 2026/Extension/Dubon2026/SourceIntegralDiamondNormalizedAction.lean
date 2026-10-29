import Dubon2026.SourceIntegralSlashNormalizedGenerators
import Dubon2026.SourceIntegralDiamondFieldAction

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> actual diamond-chart equivariance. Compute the
existing prime-field diamond action on the literal discriminant-normalized
generators. The discriminant is invariant under the full modular group; the
only scalar is the explicit inverse level power of an actual integral diamond
witness, which cancels the scalar in the reduced cusp chart. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne IntegralSlash
open scoped MatrixGroups ModularForm

theorem gammaOneDiscriminantPow_slash (N r : ℕ) (γ : SL(2, ℤ)) :
    (⇑(gammaOneDiscriminantPow N r) : ℍ → ℂ) ∣[12 * (r : ℤ)] γ =
      gammaOneDiscriminantPow N r := by
  rw [ModularForm.SL_slash]
  let F : ModularForm 𝒮ℒ (12 * (r : ℤ)) :=
    ((CuspForm.discriminant : ModularForm 𝒮ℒ 12).pow r).mcast (mul_comm _ _)
  have he : (⇑(gammaOneDiscriminantPow N r) : ℍ → ℂ) = F := by
    simp only [gammaOneDiscriminantPow, F, ModularForm.coe_mcast, ModularForm.coe_pow]
    rfl
  rw [he]
  exact SlashInvariantForm.slash_action_eqn F _ ⟨γ, rfl⟩

theorem reducedFieldAction_normalized (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    (hℓN : ¬ ℓ ∣ N) (γ : Gamma0 N) {r : ℕ}
    (f : ModularForm (Gamma1 N) (12 * (r : ℤ))) {p P : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (a : ℕ)
    (hP : IsIntegralQExp (scaledDiamond N γ⁻¹ a f) P) :
    (reducedFieldAction N ℓ hℓN γ
      ⟨intSeriesC (ZMod ℓ) p / intSeriesC (ZMod ℓ) discriminantSeries ^ r,
        normalizedGenerators_subset N (ZMod ℓ) ⟨r, f, p, hp, rfl⟩⟩ : LaurentSeries (ZMod ℓ)) =
      (intSeriesC (ZMod ℓ) P / intSeriesC (ZMod ℓ) discriminantSeries ^ r) /
        (N : LaurentSeries (ZMod ℓ)) ^ a := by
  let hk : Even (12 * (r : ℤ)) := (show Even (12 : ℤ) by decide).mul_right _
  have hd : red ℓ (discriminantSeries ^ r) ≠ 0 := by
    rw [red_apply, intSeriesC_pow_eq]
    exact pow_ne_zero _ (intSeriesC_discriminant_ne_zero (ZMod ℓ))
  rw [reducedFieldAction_apply,
    reducedFieldPull_eq N ℓ hℓN γ⁻¹ _ hk f (gammaOneDiscriminantPow N r) hp
      (integralQExp_gammaOneDiscriminantPow N r) hd
      (by rw [red_apply, red_apply, intSeriesC_pow_eq]),
    reducedDiamond_eq N ℓ hℓN hk γ⁻¹ f hp hP,
    reducedDiamond_of_invariant N ℓ hℓN hk γ⁻¹ (gammaOneDiscriminantPow N r)
      (integralQExp_gammaOneDiscriminantPow N r) (gammaOneDiscriminantPow_slash N r _),
    normalizedRed, red_apply, red_apply, intSeriesC_pow_eq, div_right_comm]

end
end Dubon2026.SourceFunctionField.IntegralDiamond
