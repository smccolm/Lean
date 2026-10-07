/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Selected adjugate-matrix identities from AdjointTheory.lean,
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
The integral consumer uses the existing local hyperbolic change-of-variables proof.
-/
import Dubon2026.PeterssonSlashTransport
import Dubon2026.HeckeTriangular

/-! # Genuine adjugate matrices and the Petersson slash transport identity -/

namespace Dubon2026

open Matrix.SpecialLinearGroup UpperHalfPlane MeasureTheory
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

variable {k : ℤ}

/-- The "Petersson adjoint" of a GL₂(ℝ) element: `α† = det(α) · α⁻¹ = adjugate(α)`. -/
noncomputable def peterssonAdj (α : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate (by
    rw [Matrix.det_adjugate]
    exact pow_ne_zero _ α.det_ne_zero)

/-- Coercion: `peterssonAdj α` as a matrix equals the adjugate of `α`. -/
lemma peterssonAdj_coe (α : GL (Fin 2) ℝ) :
    (peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ) =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate := rfl

/-- `det(peterssonAdj α) = det(α)` for 2×2 matrices (since det(adjugate) = det^{n-1}). -/
lemma peterssonAdj_det (α : GL (Fin 2) ℝ) :
    (peterssonAdj α).det = α.det :=
  Units.ext <| by simp [peterssonAdj_coe, Matrix.det_adjugate]

/-- `peterssonAdj` reverses products: `(αβ)† = β† · α†`. -/
lemma peterssonAdj_mul (α β : GL (Fin 2) ℝ) :
    peterssonAdj (α * β) = peterssonAdj β * peterssonAdj α :=
  Units.ext <| by simp [peterssonAdj_coe, Matrix.adjugate_mul_distrib]

/-- For an SL(2, ℤ) element cast to GL(2, ℝ), the `peterssonAdj` equals the group inverse.
Since SL elements have determinant 1, their adjugate equals their inverse. -/
lemma peterssonAdj_mapGL_SL_eq_inv (q : SL(2, ℤ)) :
    peterssonAdj ((mapGL ℝ q : GL (Fin 2) ℝ)) = (mapGL ℝ q : GL (Fin 2) ℝ)⁻¹ := by
  apply Units.ext
  rw [peterssonAdj_coe, Matrix.coe_units_inv]
  have hdet : (mapGL ℝ q : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, det_mapGL, Units.val_one]
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet, inv_one, one_smul]

private lemma GL_inv_entry (α : GL (Fin 2) ℝ) (i j : Fin 2) :
    (α⁻¹ : GL (Fin 2) ℝ) i j = (α.det.val)⁻¹ * (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j := by
  show (↑α⁻¹ : Matrix _ _ ℝ) i j = _
  rw [Matrix.coe_units_inv α, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    smul_eq_mul, Matrix.GeneralLinearGroup.val_det_apply]

private lemma peterssonAdj_entry (α : GL (Fin 2) ℝ) (i j : Fin 2) :
    (peterssonAdj α : Matrix _ _ ℝ) i j = (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j :=
  congrFun (congrFun (peterssonAdj_coe α) i) j

private lemma peterssonAdj_denom (α : GL (Fin 2) ℝ) (τ : ℍ) :
    UpperHalfPlane.denom (peterssonAdj α) τ = ↑(α.det.val) * UpperHalfPlane.denom α⁻¹ τ := by
  have hdet_ne : (α.det.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Units.ne_zero α.det)
  simp only [denom, peterssonAdj_entry, GL_inv_entry]
  push_cast
  field_simp

private lemma σ_peterssonAdj (α : GL (Fin 2) ℝ) : σ (peterssonAdj α) = σ α⁻¹ := by
  have hdet2 : (α⁻¹).det.val = (α.det.val)⁻¹ := by
    rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α]
    exact Units.val_inv_eq_inv_val _
  simp only [σ, congr_arg Units.val (peterssonAdj_det α), hdet2, inv_pos]

/-- `α†` and `α⁻¹` induce the same Möbius action on the upper half-plane. -/
lemma peterssonAdj_smul_eq (α : GL (Fin 2) ℝ) (τ : ℍ) :
    (peterssonAdj α) • τ = α⁻¹ • τ := by
  have hdet_ne : (α.det.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Units.ne_zero α.det)
  have hnum : num (peterssonAdj α) (τ : ℂ) = ↑α.det.val * num α⁻¹ (τ : ℂ) := by
    simp only [num, peterssonAdj_entry, GL_inv_entry]
    push_cast
    field_simp
  ext1
  simp only [coe_smul, σ_peterssonAdj]
  congr 1
  rw [hnum, peterssonAdj_denom, mul_div_mul_left _ _ hdet_ne]

/-- Pointwise: `g ∣[k] peterssonAdj α = |det α|^{k-2} • (g ∣[k] α⁻¹)`. -/
lemma slash_peterssonAdj_eq (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val) (g : ℍ → ℂ) :
    g ∣[k] peterssonAdj α = (↑(|α.det.val| ^ (k - 2)) : ℂ) • (g ∣[k] α⁻¹) := by
  have habs : |α.det.val| = α.det.val := abs_of_pos hα
  have hdet_eq : (peterssonAdj α).det.val = α.det.val := congr_arg Units.val (peterssonAdj_det α)
  have hdet_inv_abs : |(α⁻¹).det.val| = (α.det.val)⁻¹ := by
    rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α,
      Units.val_inv_eq_inv_val, abs_inv, habs]
  ext τ
  simp only [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul, peterssonAdj_smul_eq,
    σ_peterssonAdj, hdet_eq, peterssonAdj_denom, mul_zpow, hdet_inv_abs, habs]
  have hcd : (α.det.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  push_cast
  rw [inv_zpow']
  have h1 : (α.det.val : ℂ) ^ (k - 1) * (α.det.val : ℂ) ^ (-k) =
      (α.det.val : ℂ) ^ (k - 2) * (α.det.val : ℂ) ^ (-(k - 1)) := by
    rw [← zpow_add₀ hcd, ← zpow_add₀ hcd, show k - 1 + -k = k - 2 + -(k - 1) by ring]
  linear_combination σ α⁻¹ (g (α⁻¹ • τ)) * denom α⁻¹ (↑τ : ℂ) ^ (-k) * h1


/-- The actual adjugate matrix is the mixed Petersson adjoint after domain transport. -/
theorem peterssonInner_slash_adjugate (D : Set ℍ) (A : GL (Fin 2) ℝ)
    (hA : 0 < A.det.val) (f g : ℍ → ℂ) :
    peterssonInner k D (f ∣[k] A) g =
      peterssonInner k (A • D) f (g ∣[k] peterssonAdj A) := by
  have he : petersson k f (g ∣[k] peterssonAdj A) =
      fun τ => (A.det.val : ℂ) ^ (k - 2) * petersson k f (g ∣[k] A⁻¹) τ := by
    funext τ
    rw [slash_peterssonAdj_eq A hA g]
    simp only [petersson, Pi.smul_apply, smul_eq_mul, abs_of_pos hA, Complex.ofReal_zpow]
    ring
  unfold peterssonInner
  rw [he, integral_const_mul]
  exact peterssonIntegral_slash_left k f g A hA D

end
end Dubon2026
