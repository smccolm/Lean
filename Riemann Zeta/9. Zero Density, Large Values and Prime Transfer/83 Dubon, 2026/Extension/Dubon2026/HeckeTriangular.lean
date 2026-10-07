import Dubon2026.ClassicalHeckeFunctions

/-! # The actual upper-triangular slash representatives for the classical Hecke sum -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

/-- The rational matrix [[a,b],[0,d]], for positive a and d. -/
def heckeTriangularRat (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero !![(a : ℚ), b; 0, d]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne a),
      Nat.cast_ne_zero.mpr (NeZero.ne d)])

/-- The same Hecke representative acting on the actual complex upper half-plane. -/
def heckeTriangularMatrix (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map (algebraMap ℚ ℝ) (heckeTriangularRat a d b)

/-- Exact real matrix entries of the rational Hecke representative. -/
theorem heckeTriangularMatrix_val (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) :
    (heckeTriangularMatrix a d b).val = !![(a : ℝ), b; 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeTriangularMatrix, heckeTriangularRat,
    GeneralLinearGroup.map, GeneralLinearGroup.mkOfDetNeZero]

/-- The determinant of an actual Hecke representative is positive. -/
theorem heckeTriangularMatrix_det_pos (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) :
    0 < (heckeTriangularMatrix a d b).det.val := by
  rw [GeneralLinearGroup.val_det_apply, heckeTriangularMatrix_val]
  simpa using mul_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero a) : (0 : ℝ) < a)
    (Nat.cast_pos.mpr (Nat.pos_of_neZero d) : (0 : ℝ) < d)

/-- The action is exactly z ↦ (az+b)/d. -/
theorem heckeTriangularMatrix_smul (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ) (τ : ℍ) :
    heckeTriangularMatrix a d b • τ = heckeUpperPoint d b (levelRaiseMatrix a • τ) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (heckeTriangularMatrix_det_pos a d b)]
  change UpperHalfPlane.num (heckeTriangularMatrix a d b) (τ : ℂ) /
    UpperHalfPlane.denom (heckeTriangularMatrix a d b) (τ : ℂ) =
      (((levelRaiseMatrix a • τ : ℍ) : ℂ) + b) / d
  rw [coe_levelRaiseMatrix_smul]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, heckeTriangularMatrix_val]

/-- The determinant-normalized slash factor is exactly a^(k-1)/d. -/
theorem heckeTriangular_slash_apply (a d : ℕ) [NeZero a] [NeZero d] (b : ℕ)
    (k : ℤ) (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] heckeTriangularMatrix a d b) τ =
      (a : ℂ) ^ (k - 1) * (d : ℂ)⁻¹ * f (heckeUpperPoint d b (levelRaiseMatrix a • τ)) := by
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hσ : UpperHalfPlane.σ (heckeTriangularMatrix a d b) = ContinuousAlgEquiv.refl ℝ ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos (heckeTriangularMatrix_det_pos a d b)]
  have hdet : |(heckeTriangularMatrix a d b).det.val| = (a : ℝ) * d := by
    rw [abs_of_pos (heckeTriangularMatrix_det_pos a d b), GeneralLinearGroup.val_det_apply,
      heckeTriangularMatrix_val]
    simp
  have hdenom : UpperHalfPlane.denom (heckeTriangularMatrix a d b) (τ : ℂ) = (d : ℂ) := by
    simp [UpperHalfPlane.denom, heckeTriangularMatrix_val]
  rw [ModularForm.slash_apply, hσ, ContinuousAlgEquiv.refl_apply, hdet, hdenom,
    heckeTriangularMatrix_smul, Complex.ofReal_mul, Complex.ofReal_natCast,
    Complex.ofReal_natCast, mul_zpow]
  calc
    _ = (a : ℂ) ^ (k - 1) * ((d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k)) *
        f (heckeUpperPoint d b (levelRaiseMatrix a • τ)) := by ring
    _ = _ := by
      rw [← zpow_add₀ hd, show k - 1 + -k = (-1 : ℤ) by omega, zpow_neg_one]

end
end Dubon2026
