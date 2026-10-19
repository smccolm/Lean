import Dubon2026.HomogeneousSymmetricMatrix
import Dubon2026.RingSL2Elementary
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Finite.Basic

/-! Explicit regular elements in the original symmetric SL2 representation.
These supply the residual regularity required by DUB-17 auxiliary primes,
using the native homogeneous model rather than a separate Lie module. -/

namespace Dubon2026
noncomputable section
open MvPolynomial Matrix Module
open scoped MatrixGroups

/-- The native monomial weights hold over the actual arithmetic coefficient ring. -/
theorem binaryHomogeneousMonomialBasis_diagonal_ring {R : Type*} [CommRing R]
    (a b : R) (n : ℕ) (i : Fin (n + 1)) :
    homogeneousMatrixAction n (Matrix.diagonal ![a, b]) (binaryHomogeneousMonomialBasis n i) =
      (a ^ i.val * b ^ (n - i.val)) • binaryHomogeneousMonomialBasis n i := by
  unfold binaryHomogeneousMonomialBasis
  rw [Basis.reindex_apply, homogeneousMonomialBasis_apply, homogeneousMatrixAction_diagonal_monomial]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  change a ^ (n - i.rev.val) * b ^ i.rev.val = _
  have hr : i.rev.val = n - i.val := by simp [Fin.val_rev]
  rw [hr, Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)]

/-- The arithmetic monomial-basis matrix retains those exact diagonal weights. -/
theorem homogeneousDiagonal_toMatrix_ring {R : Type*} [CommRing R]
    (a b : R) (n : ℕ) :
    LinearMap.toMatrix (binaryHomogeneousMonomialBasis n) (binaryHomogeneousMonomialBasis n)
      (homogeneousMatrixAction n (Matrix.diagonal ![a, b])) =
        Matrix.diagonal (fun i : Fin (n + 1) => a ^ i.val * b ^ (n - i.val)) := by
  ext i j
  rw [LinearMap.toMatrix_apply, binaryHomogeneousMonomialBasis_diagonal_ring]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- Literal symmetric matrices of the native unit diagonal have the original weights. -/
theorem homogeneousSymmetricGL_unitDiagonal {K : Type*} [Field K]
    (u : Kˣ) (n : ℕ) :
    (homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))).val =
      Matrix.diagonal (fun i : Fin (n + 1) => (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val)) := by
  rw [homogeneousSymmetricGL_val]
  change LinearMap.toMatrix (binaryHomogeneousMonomialBasis n) (binaryHomogeneousMonomialBasis n)
    (homogeneousMatrixAction n (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)).val) = _
  have he : (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u)).val =
      Matrix.diagonal ![(u : K), (↑u⁻¹ : K)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [he]
  exact homogeneousDiagonal_toMatrix_ring (u : K) (↑u⁻¹ : K) n

/-- A unit of order larger than twice the symmetric degree gives distinct weights. -/
theorem symmetric_unit_weights_injective {K : Type*} [Field K]
    (u : Kˣ) (n : ℕ) (hu : 2 * n < orderOf u) :
    Function.Injective (fun i : Fin (n + 1) =>
      (u : K) ^ i.val * (↑u⁻¹ : K) ^ (n - i.val)) := by
  intro i j hij
  have hw (i : Fin (n + 1)) :
      (u ^ i.val * (u⁻¹) ^ (n - i.val)) * u ^ n = u ^ (2 * i.val) := by
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    calc
      (u ^ i.val * (u⁻¹) ^ (n - i.val)) * u ^ n =
          (u ^ i.val * (u ^ (n - i.val))⁻¹) * (u ^ (n - i.val) * u ^ i.val) := by
        rw [← inv_pow, ← pow_add, Nat.sub_add_cancel hi]
      _ = u ^ (2 * i.val) := by group
  have he : u ^ i.val * (u⁻¹) ^ (n - i.val) =
      u ^ j.val * (u⁻¹) ^ (n - j.val) := Units.ext (by simpa using hij)
  have he' := congrArg (fun x : Kˣ => x * u ^ n) he
  dsimp only at he'
  rw [hw, hw] at he'
  have hi : 2 * i.val < orderOf u := by omega
  have hj : 2 * j.val < orderOf u := by omega
  have h := pow_injOn_Iio_orderOf hi hj he'
  apply Fin.ext
  omega

/-- The actual higher symmetric matrix has separable characteristic polynomial. -/
theorem homogeneousSymmetricGL_unitDiagonal_separable {K : Type*} [Field K]
    (u : Kˣ) (n : ℕ) (hu : 2 * n < orderOf u) :
    ((homogeneousSymmetricGL n
      (Matrix.SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))).val.charpoly).Separable := by
  rw [homogeneousSymmetricGL_unitDiagonal, Matrix.charpoly_diagonal]
  exact Polynomial.separable_prod_X_sub_C_iff.mpr (symmetric_unit_weights_injective u n hu)

/-- A sufficiently large actual finite coefficient field supplies a regular
element in every required symmetric SL2 degree. -/
theorem finiteField_exists_symmetric_regular (K : Type*) [Field K] [Finite K]
    (n : ℕ) (hn : 2 * n < Nat.card K - 1) :
    ∃ g : SL(2, K),
      ((homogeneousSymmetricGL n (Matrix.SpecialLinearGroup.toGL g)).val.charpoly).Separable := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hu
  refine ⟨ringSL2UnitDiagonal u, homogeneousSymmetricGL_unitDiagonal_separable u n ?_⟩
  rwa [hu]

end
end Dubon2026
