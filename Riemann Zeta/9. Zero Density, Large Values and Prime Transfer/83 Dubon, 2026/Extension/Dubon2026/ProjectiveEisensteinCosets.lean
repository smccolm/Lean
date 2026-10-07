import Dubon2026.PrimitiveEisensteinCosets
import Dubon2026.Gamma0CosetUnfolding

/-! # The projective parabolic cosets identify exactly the two row signs -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup ModularGroup UpperHalfPlane
open scoped MatrixGroups

noncomputable section

/-- An integral central determinant-one matrix is precisely one of the two scalar signs. -/
theorem SL2_center_eq_one_or_neg_one (A : SL(2, ℤ))
    (hA : A ∈ Subgroup.center SL(2, ℤ)) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  simp only [Fintype.card_fin] at hr
  have hsign : r = 1 ∨ r = -1 := by
    rcases mul_eq_zero.mp (by nlinarith [hr] : (r - 1) * (r + 1) = 0) with h | h <;> omega
  rcases hsign with rfl | rfl
  · left
    ext i j
    simpa [Matrix.scalar] using (congrFun (congrFun he i) j).symm
  · right
    ext i j
    simpa [Matrix.scalar, coe_neg] using (congrFun (congrFun he i) j).symm

/-- Integer matrices have the same actual projective image exactly when they differ by a sign. -/
theorem SL2_projective_eq_iff (A B : SL(2, ℤ)) :
    (QuotientGroup.mk A : PSL(2, ℤ)) = QuotientGroup.mk B ↔ A = B ∨ A = -B := by
  rw [QuotientGroup.eq]
  constructor
  · intro h
    rcases SL2_center_eq_one_or_neg_one _ h with he | he
    · exact Or.inl (inv_mul_eq_one.mp he)
    · right
      have hb : B = A * (A⁻¹ * B) := by group
      rw [he, mul_neg, mul_one] at hb
      rw [hb, neg_neg]
  · rintro (rfl | he)
    · simp
    · have hb : B = -A := by rw [he, neg_neg]
      rw [hb, mul_neg, inv_mul_cancel]
      exact Subgroup.mem_center_iff.mpr (fun C => by simp)

/-- The actual homomorphism from Γ₀ to its projective image. -/
def gamma0Projectivize (Q : ℕ) : Gamma0 Q →* projectiveGamma0 Q where
  toFun A := ⟨QuotientGroup.mk A.val, A.val, A.property, rfl⟩
  map_one' := Subtype.ext (map_one (QuotientGroup.mk' _))
  map_mul' A B := Subtype.ext (map_mul (QuotientGroup.mk' _) A.val B.val)

/-- Every actual projective Γ₀ matrix has an integral level-preserving lift. -/
theorem gamma0Projectivize_surjective (Q : ℕ) : Function.Surjective (gamma0Projectivize Q) := by
  intro A
  obtain ⟨B, hB, he⟩ := A.property
  exact ⟨⟨B, hB⟩, Subtype.ext he⟩

/-- The integral and projective translation generators agree under the actual projection. -/
theorem gamma0Projectivize_translation (Q : ℕ) (n : ℤ) :
    gamma0Projectivize Q ⟨T ^ n, (Gamma0 Q).zpow_mem (modular_T_mem_gamma0 Q) n⟩ =
      gamma0ProjectiveT Q ^ n := by
  apply Subtype.ext
  change (QuotientGroup.mk' _ (T ^ n)) = _
  rw [map_zpow]
  rfl

/-- The actual parabolic coset of the inverse matrix, in the convention needed for unfolding. -/
def gamma0InverseParabolicCoset {Q : ℕ} (A : Gamma0 Q) :
    (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q :=
  QuotientGroup.mk ((gamma0Projectivize Q A)⁻¹)

/-- Equality of genuine projective parabolic cosets is exactly equality of bottom rows up to sign. -/
theorem gamma0InverseParabolicCoset_eq_iff {Q : ℕ} (A B : Gamma0 Q) :
    gamma0InverseParabolicCoset A = gamma0InverseParabolicCoset B ↔
      A.val.val 1 = B.val.val 1 ∨ A.val.val 1 = -(B.val.val 1) := by
  change (QuotientGroup.mk ((gamma0Projectivize Q A)⁻¹) :
    (projectiveGamma0 Q) ⧸ gamma0ProjectiveTranslations Q) =
      QuotientGroup.mk ((gamma0Projectivize Q B)⁻¹) ↔ _
  rw [QuotientGroup.eq, inv_inv]
  change gamma0Projectivize Q A * (gamma0Projectivize Q B)⁻¹ ∈
    Subgroup.zpowers (gamma0ProjectiveT Q) ↔ _
  rw [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    have hp : (QuotientGroup.mk (A.val * B.val⁻¹) : PSL(2, ℤ)) =
        QuotientGroup.mk (T ^ n) := by
      have h := congrArg Subtype.val hn.symm
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow,
        gamma0Projectivize, gamma0ProjectiveT, MonoidHom.coe_mk, OneHom.coe_mk,
        map_mul, map_inv, map_zpow] using h
    rcases (SL2_projective_eq_iff _ _).mp hp with he | he
    · left
      apply (SL2_bottom_row_eq_iff A.val B.val).mpr
      exact ⟨n, by rw [← he, inv_mul_cancel_right]⟩
    · right
      have ha : A.val = -(T ^ n * B.val) := by
        rw [← neg_mul, ← he, inv_mul_cancel_right]
      rw [ha, coe_neg]
      exact congrArg Neg.neg (T_pow_mul_apply_one n B.val)
  · rintro (h | h)
    · obtain ⟨n, hn⟩ := (SL2_bottom_row_eq_iff A.val B.val).mp h
      refine ⟨n, ?_⟩
      apply Subtype.ext
      change (QuotientGroup.mk' _ T) ^ n =
        (QuotientGroup.mk' _ A.val) * (QuotientGroup.mk' _ B.val)⁻¹
      rw [hn, map_mul, map_zpow, mul_inv_cancel_right]
    · have hneg : (-A.val).val 1 = B.val.val 1 := by
        change -(A.val.val 1) = _
        rw [h, neg_neg]
      obtain ⟨n, hn⟩ := (SL2_bottom_row_eq_iff (-A.val) B.val).mp hneg
      have ha : A.val = -(T ^ n * B.val) := by rw [← hn, neg_neg]
      have he : (QuotientGroup.mk A.val : PSL(2, ℤ)) = QuotientGroup.mk (T ^ n * B.val) :=
        (SL2_projective_eq_iff _ _).mpr (Or.inr ha)
      change (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) A.val =
        (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) (T ^ n * B.val) at he
      refine ⟨n, ?_⟩
      apply Subtype.ext
      change (QuotientGroup.mk' _ T) ^ n =
        (QuotientGroup.mk' _ A.val) * (QuotientGroup.mk' _ B.val)⁻¹
      rw [he, map_mul, map_zpow, mul_inv_cancel_right]

end
end Dubon2026
