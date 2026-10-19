import Dubon2026.FiniteSymmetricRegularDiagonal
import Dubon2026.DistinctWeightSubmodule
import Mathlib.Algebra.MvPolynomial.Coeff

/-! Two literal unipotent orbit computations in the native homogeneous
model. Together with existing distinct-weight extraction, these give the
finite-characteristic irreducibility needed by DUB-17 residual-image and
dual-Selmer detection arguments. -/

namespace Dubon2026
noncomputable section
open MvPolynomial Module

variable {R : Type*} [CommRing R]

/-- The native binary basis has its literal two-variable monomial value. -/
theorem binaryHomogeneousMonomialBasis_val (n : ℕ) (i : Fin (n + 1)) :
    (binaryHomogeneousMonomialBasis (R := R) n i).val =
      X 0 ^ i.val * X 1 ^ (n - i.val) := by
  unfold binaryHomogeneousMonomialBasis
  rw [Basis.reindex_apply, homogeneousMonomialBasis_apply]
  change monomial _ (1 : R) = _
  rw [monomial_eq, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fin.prod_univ_two]
  change X 0 ^ (n - i.rev.val) * X 1 ^ i.rev.val = _
  have hr : i.rev.val = n - i.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)]

/-- Evaluation at the second coordinate vector is the native zeroth
monomial coordinate on the original fixed-degree space. -/
theorem homogeneous_eval_zero_one_eq_repr_zero (n : ℕ)
    (v : homogeneousSubmodule (Fin 2) R n) :
    aeval ![0, 1] v.val = (binaryHomogeneousMonomialBasis n).repr v 0 := by
  let b := binaryHomogeneousMonomialBasis (R := R) n
  have he : ((aeval ![0, 1] : MvPolynomial (Fin 2) R →ₐ[R] R).toLinearMap.comp
      (homogeneousSubmodule (Fin 2) R n).subtype) =
        (Finsupp.lapply (0 : Fin (n + 1))).comp b.repr.toLinearMap := by
    apply b.ext
    intro i
    change aeval ![0, 1] (b i).val = b.repr (b i) 0
    rw [Basis.repr_self, binaryHomogeneousMonomialBasis_val]
    by_cases hi : i = 0
    · subst i
      simp
    · have hn : i.val ≠ 0 := fun h => hi (Fin.ext h)
      simp [hi, hn]
  exact congrArg (fun L : homogeneousSubmodule (Fin 2) R n →ₗ[R] R => L v) he

/-- The lower unipotent sends every original basis monomial to a vector
whose zeroth coordinate is exactly one. -/
theorem homogeneous_lowerUnipotent_basis_repr_zero (n : ℕ) (i : Fin (n + 1)) :
    (binaryHomogeneousMonomialBasis n).repr
      (homogeneousMatrixAction n (ringLowerUnipotent (1 : R)).val
        (binaryHomogeneousMonomialBasis n i)) 0 = 1 := by
  rw [← homogeneous_eval_zero_one_eq_repr_zero, homogeneousMatrixAction_apply,
    binaryHomogeneousMonomialBasis_val]
  simp [matrixPolynomialAction_X, Fin.sum_univ_two,
    ringLowerUnipotent]

/-- The upper unipotent sends the original zeroth basis monomial to the
literal binomial polynomial, over the actual coefficient ring. -/
theorem homogeneous_upperUnipotent_basis_zero_val (n : ℕ) :
    (homogeneousMatrixAction n (ringUpperUnipotent (1 : R)).val
      (binaryHomogeneousMonomialBasis n 0)).val = (X 0 + X 1) ^ n := by
  rw [homogeneousMatrixAction_apply, binaryHomogeneousMonomialBasis_val]
  simp [matrixPolynomialAction_X, Fin.sum_univ_two,
    ringUpperUnipotent]

/-- Every coordinate of that native binomial orbit is the corresponding
actual binomial coefficient, with no characteristic-zero restriction. -/
theorem homogeneous_upperUnipotent_basis_zero_repr (n : ℕ) (i : Fin (n + 1)) :
    (binaryHomogeneousMonomialBasis n).repr
      (homogeneousMatrixAction n (ringUpperUnipotent (1 : R)).val
        (binaryHomogeneousMonomialBasis n 0)) i = (n.choose i.val : R) := by
  rw [binaryHomogeneousMonomialBasis_repr, homogeneous_upperUnipotent_basis_zero_val,
    coeff_add_pow]
  change ((if (n - i.rev.val, i.rev.val) ∈ Finset.antidiagonal n then
    n.choose (n - i.rev.val) else 0 : ℕ) : R) = _
  have hr : i.rev.val = n - i.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)]
  rw [if_pos (Finset.mem_antidiagonal.mpr (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)))]

end
end Dubon2026
