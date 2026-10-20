import Dubon2026.SymmetricDualityIntertwining

/-! An original odd rank-two involution turns the explicitly constructed
symmetric-power duality into a symmetric CM polarization matrix. This
discharges the matrix symmetry input of DUB-17's actual CM extension. -/

namespace Dubon2026
open Matrix
noncomputable section

variable {K : Type*} [Field K]

/-- The original real-place matrix times the actual symmetric-power duality matrix. -/
def symmetricRealPolarization (n : ℕ) (hn : (n.factorial : K) ≠ 0)
    (c : GeneralLinearGroup (Fin 2) K) : GeneralLinearGroup (Fin (n + 1)) K :=
  homogeneousSymmetricGL n c * symmetricDualityGL n hn

/-- Oddness of the original rank-two involution cancels the exact degree parity of symmetric-power duality. -/
theorem symmetricRealPolarization_symmetric (n : ℕ) (hn : (n.factorial : K) ≠ 0)
    (c : GeneralLinearGroup (Fin 2) K) (hc : c ^ 2 = 1) (hd : c.val.det = -1) :
    (symmetricRealPolarization n hn c).val.transpose = (symmetricRealPolarization n hn c).val := by
  let S := homogeneousSymmetricGL n c
  have hss : S.val * S.val = 1 := by
    have he : S ^ 2 = 1 := by
      change (homogeneousSymmetricGL n c) ^ 2 = 1
      rw [← map_pow, hc, map_one]
    exact congrArg (fun u : GeneralLinearGroup (Fin (n + 1)) K => u.val) (by simpa only [pow_two] using he)
  have hcov := symmetricDualityMatrix_covariance n c
  rw [hd] at hcov
  change S.val * symmetricDualityMatrix n * S.val.transpose = (-1 : K) ^ n • symmetricDualityMatrix n at hcov
  have hb : symmetricDualityMatrix n * S.val.transpose =
      (-1 : K) ^ n • (S.val * symmetricDualityMatrix n) := by
    calc
      _ = (S.val * S.val) * (symmetricDualityMatrix n * S.val.transpose) := by rw [hss, one_mul]
      _ = S.val * (S.val * symmetricDualityMatrix n * S.val.transpose) := by simp only [mul_assoc]
      _ = _ := by rw [hcov, Matrix.mul_smul]
  have hs : (-1 : K) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  change (S.val * (symmetricDualityGL n hn).val).transpose = S.val * (symmetricDualityGL n hn).val
  rw [symmetricDualityGL_val, Matrix.transpose_mul, symmetricDualityMatrix_transpose,
    Matrix.smul_mul, hb, smul_smul, hs, one_smul]

/-- The constructed real-place matrix gives the exact conjugate-duality identity on every original symmetric power. -/
theorem symmetricRealPolarization_conjugate (n : ℕ) (hn : (n.factorial : K) ≠ 0)
    (c g : GeneralLinearGroup (Fin 2) K) :
    homogeneousSymmetricGL n (c * g * c⁻¹) = symmetricRealPolarization n hn c *
      (GeneralLinearGroup.scalar (Fin (n + 1)) ((GeneralLinearGroup.det g) ^ n) *
        polarizedContragredient (homogeneousSymmetricGL n g)) *
          (symmetricRealPolarization n hn c)⁻¹ := by
  rw [map_mul, map_mul, map_inv]
  conv_lhs => arg 1; arg 2; rw [symmetricDualityGL_conjugate n hn g]
  unfold symmetricRealPolarization
  group

end
end Dubon2026
