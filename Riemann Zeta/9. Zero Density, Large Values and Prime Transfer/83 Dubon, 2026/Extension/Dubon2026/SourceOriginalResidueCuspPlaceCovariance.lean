import Dubon2026.SourceIntegralSlashFieldDiamondCovariance
import Dubon2026.SourceOriginalResidueCuspPlaceFamily
import Dubon2026.SourceOriginalResidueDiamondFixedField
import Dubon2026.SourceIntegralSlashFieldChartIdentities
import Dubon2026.SourceCurvePlaceTransport

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> residue cusp count -> descent to the existing signed translation orbits.
The actual cusp-place family is covariant for the original diamond action.
Its proved kernel gives left signed-Gamma1 invariance, and the literal Fourier
twist preserves place membership under every right integral translation. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open CongruenceSubgroup GammaOne IntegralDiamond SourceCurve
open scoped MatrixGroups
local notation "Zbar" => integralClosure ℤ ℂ
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
private local instance : Algebra kk (qExpFunctionFieldC kk (Gamma1 N)) :=
  (qExpFunctionFieldC kk (Gamma1 N)).toSubalgebra.algebra

theorem originalResidueCuspPlace_diamond_mul (hℓN : ¬ ℓ ∣ N) (φ : Zbar →+* kk)
    (β : SL(2, ℤ)) (γ : Gamma0 N) :
    originalResidueCuspPlace A N ℓ hℓN φ ((γ⁻¹).val * β) =
      (originalResidueCuspPlace A N ℓ hℓN φ β).comapEquiv
        (originalResidueDiamondAction A N ℓ hℓN γ) := by
  letI : Algebra (ZMod ℓ) kk := (ZMod.castHom (dvd_refl ℓ) kk).toAlgebra
  have hN : (N : kk) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff kk ℓ N).mp h)
  apply Place.ext
  ext x
  rw [originalResidueCuspPlace_mem_iff, Place.mem_comapEquiv_iff, originalResidueCuspPlace_mem_iff]
  rw [originalReducedSlashFieldHom_diamond_mul N ℓ hℓN φ hN β
    (originalResidueCuspHom A N ℓ hℓN φ β)
    (originalResidueCuspHom_normalized A N ℓ hℓN φ hN β) γ
    (originalResidueCuspHom A N ℓ hℓN φ ((γ⁻¹).val * β))
    (originalResidueCuspHom_normalized A N ℓ hℓN φ hN ((γ⁻¹).val * β))]
  rfl

theorem originalResidueCuspPlace_mul_left_signed (hℓN : ¬ ℓ ∣ N) (φ : Zbar →+* kk)
    (β γ : SL(2, ℤ)) (hγ : γ ∈ plusMinus (Gamma1 N)) :
    originalResidueCuspPlace A N ℓ hℓN φ (γ * β) = originalResidueCuspPlace A N ℓ hℓN φ β := by
  letI : Algebra (ZMod ℓ) kk := (ZMod.castHom (dvd_refl ℓ) kk).toAlgebra
  let δ : Gamma0 N := ⟨γ⁻¹, (Gamma0 N).inv_mem (signed_gammaOne_le_gammaZero N hγ)⟩
  have he : originalResidueDiamondAction A N ℓ hℓN δ = 1 :=
    (reducedFieldActionOver_eq_one_iff kk N ℓ hℓN δ).mpr ((plusMinus (Gamma1 N)).inv_mem hγ)
  have h := originalResidueCuspPlace_diamond_mul A N ℓ hℓN φ β δ
  have hδ : (δ⁻¹).val = γ := inv_inv γ
  rw [hδ, he] at h
  refine h.trans ?_
  apply Place.ext
  ext x
  rfl

theorem originalResidueCuspPlace_mul_T_zpow (hℓN : ¬ ℓ ∣ N) (φ : Zbar →+* kk)
    (ζ : kkˣ) (hφ : ∀ z : Zbar,
      (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N) → φ z = ζ)
    (β : SL(2, ℤ)) (j : ℤ) :
    originalResidueCuspPlace A N ℓ hℓN φ (β * ModularGroup.T ^ j) =
      originalResidueCuspPlace A N ℓ hℓN φ β := by
  have hN : (N : kk) ≠ 0 := fun h => hℓN ((CharP.cast_eq_zero_iff kk ℓ N).mp h)
  apply Place.ext
  ext x
  rw [originalResidueCuspPlace_mem_iff, originalResidueCuspPlace_mem_iff,
    originalReducedSlashFieldHom_mul_T_zpow N ℓ φ hN ζ hφ β j
      (originalResidueCuspHom A N ℓ hℓN φ β)
      (originalResidueCuspHom A N ℓ hℓN φ (β * ModularGroup.T ^ j))
      (originalResidueCuspHom_normalized A N ℓ hℓN φ hN β)
      (originalResidueCuspHom_normalized A N ℓ hℓN φ hN (β * ModularGroup.T ^ j))]
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · rw [laurent_order_qTwist _ _ (by simpa only [map_zero] using
      (originalResidueCuspHom A N ℓ hℓN φ β).injective.ne hx)]

end
end Dubon2026.SourceFunctionField.IntegralSlash
