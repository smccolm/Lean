import Dubon2026.CuspTwistFunction

/-! # Actual Fricke matrices and their determinant-normalized slash action -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- The actual Fricke matrix W_N = [[0,-1],[N,0]]. -/
def frickeMatrix (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  mapGL ℝ ModularGroup.S * levelRaiseMatrix N

/-- Exact entries of the Fricke matrix. -/
theorem frickeMatrix_val (N : ℕ) [NeZero N] :
    (frickeMatrix N).val = !![0, -1; (N : ℝ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [frickeMatrix, levelRaiseMatrix,
      Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix, ModularGroup.S]

/-- The Fricke determinant is the positive level. -/
theorem frickeMatrix_det_pos (N : ℕ) [NeZero N] : 0 < (frickeMatrix N).det.val := by
  rw [GeneralLinearGroup.val_det_apply, frickeMatrix_val]
  simpa using (Nat.cast_pos.mpr (Nat.pos_of_neZero N) : (0 : ℝ) < N)

/-- Fricke acts on the genuine upper half-plane by z ↦ -1/(Nz). -/
theorem frickeMatrix_smul (N : ℕ) [NeZero N] (τ : ℍ) :
    ((frickeMatrix N • τ : ℍ) : ℂ) = -1 / ((N : ℂ) * τ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (frickeMatrix_det_pos N)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, frickeMatrix_val]

/-- The exact slash factor for W_N in the pinned Mathlib convention. -/
theorem fricke_slash_apply (N : ℕ) [NeZero N] (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] frickeMatrix N) τ =
      (N : ℂ)⁻¹ * (τ : ℂ) ^ (-k) * f (frickeMatrix N • τ) := by
  have hσ : UpperHalfPlane.σ (frickeMatrix N) = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos (frickeMatrix_det_pos N)]
  have hdet : |(frickeMatrix N).det.val| = (N : ℝ) := by
    rw [abs_of_pos (frickeMatrix_det_pos N), GeneralLinearGroup.val_det_apply, frickeMatrix_val]
    simp
  have hden : UpperHalfPlane.denom (frickeMatrix N) (τ : ℂ) = (N : ℂ) * τ := by
    simp [UpperHalfPlane.denom, frickeMatrix_val]
  rw [ModularForm.slash_apply, hσ, ContinuousAlgEquiv.refl_apply, hdet, hden,
    Complex.ofReal_natCast, mul_zpow]
  calc
    _ = ((N : ℂ) ^ (k - 1) * (N : ℂ) ^ (-k)) * (τ : ℂ) ^ (-k) *
        f (frickeMatrix N • τ) := by ring
    _ = _ := by
      rw [← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne N)),
        show k - 1 + -k = (-1 : ℤ) by omega, _root_.zpow_neg_one]

/-- The equal diagonal Hecke point is precisely a rational horizontal translation. -/
theorem equalDiagonal_heckePoint (D : ℕ) [NeZero D] (a : ℕ) (τ : ℍ) :
    heckeUpperPoint D a (levelRaiseMatrix D • τ) = ((a : ℝ) / D) +ᵥ τ := by
  apply UpperHalfPlane.ext
  simp only [heckeUpperPoint, coe_mk, coe_levelRaiseMatrix_smul, coe_vadd]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne D)]
  ring

/-- A scalar D matrix acts by exactly D^(k-2), retaining the pinned slash normalization. -/
theorem scalarMatrix_slash (D : ℕ) [NeZero D] (k : ℤ) (f : ℍ → ℂ) :
    f ∣[k] heckeTriangularMatrix D D 0 = (D : ℂ) ^ (k - 2) • f := by
  funext τ
  rw [heckeTriangular_slash_apply, equalDiagonal_heckePoint]
  simp only [Nat.cast_zero, zero_div, zero_vadd, Pi.smul_apply, smul_eq_mul]
  rw [← _root_.zpow_neg_one, ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne D))]
  congr 2
  omega

/-- A rational translate is the exact scalar multiple of the actual equal-diagonal slash translate. -/
theorem rationalTranslation_slash (D : ℕ) [NeZero D] (a : ℕ) (k : ℤ) (f : ℍ → ℂ) :
    (fun τ : ℍ => f (((a : ℝ) / D) +ᵥ τ)) =
      (D : ℂ) ^ (2 - k) • (f ∣[k] heckeTriangularMatrix D D a) := by
  funext τ
  rw [Pi.smul_apply, heckeTriangular_slash_apply, equalDiagonal_heckePoint]
  simp only [smul_eq_mul]
  rw [← _root_.zpow_neg_one]
  symm
  calc
    _ = (D : ℂ) ^ ((2 - k) + (k - 1) + (-1)) * f (((a : ℝ) / D) +ᵥ τ) := by
      rw [zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne D)),
        zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne D))]
      ring
    _ = _ := by rw [show (2 - k) + (k - 1) + (-1) = (0 : ℤ) by omega, zpow_zero, one_mul]

end
end Dubon2026
