import Dubon2026.SourceGammaOnePrimitiveCuspValues

/-! DUB-17/18 -> original all-weight association -> exact joint arithmetic
realization -> primitive two-term boundary Hecke formula. Native coset
equality shows that original Gamma1 conjugation preserves the primitive
width and loop. The existing integral unipotent formula then applies
with that width, without cancelling it in a torsion coefficient ring. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup SourceCuspBoundary
open scoped MatrixGroups

/-- The underlying integral matrix of the actual primitive cusp translation. -/
theorem primitiveCuspTranslation_unipMat (M : ℕ) (δ : SL(2, ℤ)) :
    (primitiveCuspTranslation M δ).val =
      unipMat (δ 0 0) (δ 1 0)
        (primitiveCuspWidth M ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M)) := by
  simpa only [zpow_natCast] using conj_T_zpow_eq_unipMat δ
    (primitiveCuspWidth M ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M))

/-- Original Gamma1 conjugation preserves the actual primitive return time. -/
theorem primitiveCuspWidth_conjugate (M : ℕ) (δ : SL(2, ℤ)) (r : Gamma1 M) :
    primitiveCuspWidth M (((r.val⁻¹ * δ)⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M) =
      primitiveCuspWidth M ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M) := by
  apply congrArg (primitiveCuspWidth M)
  apply QuotientGroup.eq.mpr
  change ((r.val⁻¹ * δ)⁻¹)⁻¹ * δ⁻¹ ∈ Gamma1 M
  rw [inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  exact (Gamma1 M).inv_mem r.property

/-- The primitive cusp loop itself respects original Gamma1 conjugation. -/
theorem primitiveCuspTranslation_conjugate (M : ℕ) (δ : SL(2, ℤ)) (r : Gamma1 M) :
    primitiveCuspTranslation M (r.val⁻¹ * δ) = r⁻¹ * primitiveCuspTranslation M δ * r := by
  apply Subtype.ext
  change (r.val⁻¹ * δ) * ModularGroup.T ^
      primitiveCuspWidth M (((r.val⁻¹ * δ)⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M) *
      (r.val⁻¹ * δ)⁻¹ =
    r.val⁻¹ * (δ * ModularGroup.T ^
      primitiveCuspWidth M ((δ⁻¹ : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 M) * δ⁻¹) * r.val
  rw [primitiveCuspWidth_conjugate]
  group

/-- Every original additive character has the same value on conjugate primitive cusp loops. -/
theorem primitiveCuspValue_conjugate (M : ℕ) {A : Type*} [AddCommGroup A]
    (φ : Additive (Gamma1 M) →+ A) (δ : SL(2, ℤ)) (r : Gamma1 M) :
    primitiveCuspValue M φ (r.val⁻¹ * δ) = primitiveCuspValue M φ δ := by
  change φ (Additive.ofMul (primitiveCuspTranslation M (r.val⁻¹ * δ))) =
    φ (Additive.ofMul (primitiveCuspTranslation M δ))
  rw [primitiveCuspTranslation_conjugate]
  simp only [ofMul_mul, ofMul_inv, map_add, map_neg]
  abel

end
end Dubon2026.SourceFunctionField.GammaOne
