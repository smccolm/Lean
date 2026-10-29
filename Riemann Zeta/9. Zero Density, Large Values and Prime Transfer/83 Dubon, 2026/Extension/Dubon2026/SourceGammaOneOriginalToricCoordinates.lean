import Dubon2026.SourceGammaOneToricCoordinateDiamond

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> marked-point chart. Assemble the two literal toric invariant
functions in the original Gamma1 field and their actual diamond action.
No field-element, integrality, Laurent-expansion, or action certificate is
assumed. The exact-order point and marked-point correspondence remain
separate required mathematical obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricCoordinates
noncomputable section
open CongruenceSubgroup HahnSeries ToricFourier IntegralDiamond ReducedDegreeTransport
attribute [local instance] originalFieldScalarAlgebra
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
  (K : Type*) [Field K] [Algebra (ZMod ℓ) K]

theorem exists_originalToricCoordinates (hN : 2 ≤ N) {ζ : K}
    (hζ : IsPrimitiveRoot ζ N) :
    ∃ w₁ w₂ : (ZMod N)ˣ → qExpFunctionFieldC K (Gamma1 N),
      (∀ t, (w₁ t : LaurentSeries K) =
        (tateLaurent K).c₄ *
          (1 + 12 * ofPowerSeries ℤ K (xS (ζ ^ (t : ZMod N).val))) /
            (tateLaurent K).c₆) ∧
      (∀ t, (w₂ t : LaurentSeries K) =
        (ofPowerSeries ℤ K (xS (ζ ^ (t : ZMod N).val)) +
          6 * ofPowerSeries ℤ K (xS (ζ ^ (t : ZMod N).val)) ^ 2 +
          2 * (tateLaurent K).a₄) / (tateLaurent K).c₄) ∧
      (∀ γ : Gamma0 N, ∀ t,
        reducedFieldActionOver K N ℓ hℓN γ (w₁ t) =
          w₁ (t * (gamma0Unit N γ)⁻¹)) ∧
      (∀ γ : Gamma0 N, ∀ t,
        reducedFieldActionOver K N ℓ hℓN γ (w₂ t) =
          w₂ (t * (gamma0Unit N γ)⁻¹)) := by
  exact ⟨w₁ N K ζ, w₂ N K ζ, coe_w₁ N hζ hN, coe_w₂ N hζ hN,
    fun γ t => reducedFieldActionOver_w₁ N K ℓ hℓN γ ζ t,
    fun γ t => reducedFieldActionOver_w₂ N K ℓ hℓN γ ζ t⟩

end
end Dubon2026.SourceFunctionField.GammaOne.ToricCoordinates
