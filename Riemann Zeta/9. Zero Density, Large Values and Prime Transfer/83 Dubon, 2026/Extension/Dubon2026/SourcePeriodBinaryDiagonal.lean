import Dubon2026.SourcePeriodBinaryEquivalence
import Dubon2026.HomogeneousSatakeEuler

/-! The original coefficient comparison respects the actual Hecke diagonal.
DUB-17/18 -> residual modular Galois association -> the original nonzero
column-binary H1 Hecke eigenclass. Reuse the actual monomial basis and
binomial duality to compute the coefficient comparison, without changing
the original polynomial representation or its normalization.
-/

namespace Dubon2026
noncomputable section
open Matrix Matrix.SpecialLinearGroup MvPolynomial
open scoped MatrixGroups

/-- The genuine modular S inverse reverses the original monomials with the exact sign. -/
theorem sourceModularSinv_binaryMonomial (n : ℕ) (j : Fin (n + 1)) :
    homogeneousGLRepresentation n (mapGL ℂ (ModularGroup.S⁻¹))
        (binaryHomogeneousMonomialBasis n j) =
      (-1 : ℂ) ^ j.val • binaryHomogeneousMonomialBasis n j.rev := by
  apply Subtype.ext
  change matrixPolynomialAction (mapGL ℂ (ModularGroup.S⁻¹)).val
    (binaryHomogeneousMonomialBasis n j).val = _
  rw [binaryHomogeneousMonomialBasis_val]
  change matrixPolynomialAction (mapGL ℂ (ModularGroup.S⁻¹)).val
    (X 0 ^ j.val * X 1 ^ (n - j.val)) =
      (-1 : ℂ) ^ j.val • (binaryHomogeneousMonomialBasis n j.rev).val
  rw [binaryHomogeneousMonomialBasis_val]
  have hr : j.rev.val = n - j.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self (Nat.le_of_lt_succ j.isLt)]
  have hs : (mapGL ℂ (ModularGroup.S⁻¹)).val = !![(0 : ℂ), 1; -1, 0] := by
    change (((ModularGroup.S⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℂ)) = _
    rw [Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, Matrix.adjugate_fin_two]
    ext i l
    fin_cases i <;> fin_cases l <;> norm_num
  have hx : matrixPolynomialAction !![(0 : ℂ), 1; -1, 0] (X 0) = -X 1 := by
    simp [matrixPolynomialAction_X, Fin.sum_univ_two]
  have hy : matrixPolynomialAction !![(0 : ℂ), 1; -1, 0] (X 1) = X 0 := by
    simp [matrixPolynomialAction_X, Fin.sum_univ_two]
  rw [hs, map_mul, map_pow, map_pow, hx, hy, neg_pow, smul_eq_C_mul,
    map_pow, map_neg, map_one]
  ring

/-- The original coefficient intertwiner is the explicit diagonal of signed binomial coefficients. -/
theorem sourcePeriodBinaryIntertwiner_diagonal (n : ℕ) (hn : (n.factorial : ℂ) ≠ 0) :
    (sourcePeriodBinaryIntertwiner n hn).val =
      Matrix.diagonal (fun j : Fin (n + 1) => (-1 : ℂ) ^ n * (n.choose j.val : ℂ)) := by
  have hi : (homogeneousSymmetricGL n (mapGL ℂ ModularGroup.S)).inv =
      (homogeneousSymmetricGL n (mapGL ℂ (ModularGroup.S⁻¹))).val := by
    rw [map_inv, map_inv]
    rfl
  have hm (i j : Fin (n + 1)) :
      (homogeneousSymmetricGL n (mapGL ℂ (ModularGroup.S⁻¹))).val i j =
        if i = j.rev then (-1 : ℂ) ^ j.val else 0 := by
    change LinearMap.toMatrix (binaryHomogeneousMonomialBasis n)
      (binaryHomogeneousMonomialBasis n)
        (homogeneousGLRepresentation n (mapGL ℂ (ModularGroup.S⁻¹))) i j = _
    rw [LinearMap.toMatrix_apply, sourceModularSinv_binaryMonomial]
    simp [Finsupp.single_apply, eq_comm]
  change (homogeneousSymmetricGL n (mapGL ℂ ModularGroup.S)).inv *
    (symmetricDualityGL n hn).val = _
  rw [hi, symmetricDualityGL_val]
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j.rev]
  · rw [hm, symmetricDualityMatrix]
    simp only [Fin.rev_rev, ite_true]
    by_cases h : i = j
    · subst i
      rw [if_pos rfl, Matrix.diagonal_apply_eq]
      have hj : j.rev.val = n - j.val := by simp [Fin.val_rev]
      rw [hj, Nat.sub_sub_self (Nat.le_of_lt_succ j.isLt),
        Nat.choose_symm (Nat.le_of_lt_succ j.isLt)]
      calc
        _ = ((-1 : ℂ) ^ (n - j.val) * (-1) ^ j.val) * (n.choose j.val : ℂ) := by ring
        _ = _ := by rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ j.isLt)]
    · simp [h]
  · intro l _ hl
    have hj : j ≠ l.rev := by
      intro h
      apply hl
      rw [h, Fin.rev_rev]
    simp only [symmetricDualityMatrix, hj, if_false, mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end
end Dubon2026
