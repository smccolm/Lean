import Dubon2026.SourceEllipticExceptionalDivision

/-! DUB-17/18 -> reverse genus -> exceptional j=0 census.
The actual cubic coordinate automorphism and the native addition law
discharge its quadratic action identity. Reuse the existing stabilizer
point equivalence and optional-coordinate identities.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the corresponding cubic
variable-change, addition and exceptional fixed-subgroup source solutions. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine SourceEllipticVariableChange
open SourceEllipticStabilizer Polynomial
noncomputable section
variable {L : Type*} [Field L]

theorem natDegree_Phi_sub_C_mul_X_mul_PsiSq_le (W : WeierstrassCurve L) (c : L) (m : ℕ) (hm : 1 ≤ m) :
    (W.Φ (m : ℤ) - C c * X * W.ΨSq (m : ℤ)).natDegree ≤ m ^ 2 := by
  have hm2 : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega))
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · have hΦ := W.natDegree_Φ_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΦ
    exact hΦ
  · refine (natDegree_mul_le).trans ?_
    have hΨ := W.natDegree_ΨSq_le (m : ℤ)
    simp only [Int.natAbs_natCast] at hΨ
    have hCX : (C c * X : L[X]).natDegree ≤ 1 := (natDegree_C_mul_le _ _).trans natDegree_X_le
    omega

/-- The actual short Weierstrass model with exceptional j-invariant zero. -/
abbrev EB (B : L) : WeierstrassCurve L := ⟨0, 0, 0, 0, B⟩

theorem EB_Δ (B : L) : (EB B).Δ = -432 * B ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]; ring

theorem isElliptic_EB (B : L) (hB : B ≠ 0) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0) : (EB B).IsElliptic := by
  refine ⟨?_⟩
  rw [EB_Δ, isUnit_iff_ne_zero]
  have h432 : (432 : L) ≠ 0 := by
    rw [show (432 : L) = 2 ^ 4 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  exact mul_ne_zero (neg_ne_zero.mpr h432) (pow_ne_zero 2 hB)

theorem cubic_change_fixes
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 3 = 1) (B : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, 0, B⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : ((u⁻¹ : Rˣ) : R) ^ 3 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 3 = ((u⁻¹ : Rˣ) : R) ^ 3 * (u : R) ^ 3 := by rw [hu, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 3 := by ring
      _ = 1 := by rw [h1, one_pow]
  have h6 : ((u⁻¹ : Rˣ) : R) ^ 6 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 6 = (((u⁻¹ : Rˣ) : R) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · ring
  · linear_combination B * h6

end
end Dubon2026.SourceEllipticExceptional
