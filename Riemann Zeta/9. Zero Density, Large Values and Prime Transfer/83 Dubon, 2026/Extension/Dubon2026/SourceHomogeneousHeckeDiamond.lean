import Dubon2026.FiniteSymmetricRegularDiagonal

/-! DUB-17/18 -> original all-weight arithmetic association -> finite
Gamma1 Frobenius realization -> the original homogeneous coefficient
factor in the Hecke/Frobenius quadratic relation. Reuse the native
monomial-basis action over rings; no scalar coefficient substitute.
-/
namespace Dubon2026
noncomputable section
variable {R : Type*} [CommRing R]

theorem homogeneousHeckeDiamond_square (w : ℕ) (a d : R) (h : d * a = 1) :
    (homogeneousMatrixAction w (Matrix.diagonal ![d, 1])).comp
        (homogeneousMatrixAction w (Matrix.diagonal ![d, 1])) =
      d ^ w • homogeneousMatrixAction w (Matrix.diagonal ![d, a]) := by
  apply (binaryHomogeneousMonomialBasis w).ext
  intro i
  simp only [LinearMap.comp_apply, binaryHomogeneousMonomialBasis_diagonal_ring,
    one_pow, mul_one, map_smul, LinearMap.smul_apply, smul_smul]
  congr 1
  have hi : i.val ≤ w := Nat.le_of_lt_succ i.isLt
  calc
    d ^ i.val * d ^ i.val = d ^ i.val * d ^ i.val * (d * a) ^ (w - i.val) := by
      rw [h, one_pow, mul_one]
    _ = d ^ w * (d ^ i.val * a ^ (w - i.val)) := by
      have hw : d ^ w = d ^ i.val * d ^ (w - i.val) := by
        rw [← pow_add, Nat.add_sub_of_le hi]
      rw [mul_pow, hw]
      ring

end
end Dubon2026
