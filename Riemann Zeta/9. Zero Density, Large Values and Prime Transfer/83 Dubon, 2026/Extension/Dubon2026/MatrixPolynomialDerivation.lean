import Dubon2026.MatrixPolynomialAction
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.RingTheory.Derivation.Lie

/-! # Genuine matrix derivations on the original polynomial algebra -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι]

/-- The original matrix induces its actual linear vector field on the polynomial generators. -/
def matrixPolynomialDerivation (a : Matrix ι ι ℂ) :
    Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) :=
  mkDerivation ℂ (fun i => ∑ j, a j i • X j)

/-- The genuine derivation differentiates each original variable into its original matrix column. -/
theorem matrixPolynomialDerivation_X (a : Matrix ι ι ℂ) (i : ι) :
    matrixPolynomialDerivation a (X i) = ∑ j, a j i • X j := mkDerivation_X _ _ _

/-- Two successive genuine derivations on a variable give the original matrix product column. -/
theorem matrixPolynomialDerivation_composition_X (a b : Matrix ι ι ℂ) (i : ι) :
    matrixPolynomialDerivation a (matrixPolynomialDerivation b (X i)) =
      ∑ j, (a * b) j i • X j := by
  simp only [matrixPolynomialDerivation_X, map_sum, Derivation.map_smul, Finset.smul_sum,
    smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_comm]

variable [DecidableEq ι]

/-- The genuine matrix commutator equals the commutator of the original polynomial derivations. -/
theorem matrixPolynomialDerivation_bracket (a b : Matrix ι ι ℂ) :
    matrixPolynomialDerivation ⁅a, b⁆ = ⁅matrixPolynomialDerivation a, matrixPolynomialDerivation b⁆ := by
  apply MvPolynomial.derivation_ext
  intro i
  rw [Derivation.commutator_apply, matrixPolynomialDerivation_composition_X,
    matrixPolynomialDerivation_composition_X]
  simp only [matrixPolynomialDerivation_X, LieRing.of_associative_ring_bracket,
    Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- The original matrix vector fields form a genuine complex Lie algebra homomorphism. -/
def matrixPolynomialDerivationLie :
    Matrix ι ι ℂ →ₗ⁅ℂ⁆ Derivation ℂ (MvPolynomial ι ℂ) (MvPolynomial ι ℂ) where
  toFun := matrixPolynomialDerivation
  map_add' a b := by
    apply MvPolynomial.derivation_ext
    intro i
    simp [matrixPolynomialDerivation_X, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply MvPolynomial.derivation_ext
    intro i
    simp [matrixPolynomialDerivation_X, smul_smul, Finset.smul_sum]
  map_lie' {a b} := matrixPolynomialDerivation_bracket a b

/-- The genuine matrix infinitesimal acts by the original derivation as an actual linear endomorphism. -/
def matrixPolynomialLieAction : Matrix ι ι ℂ →ₗ⁅ℂ⁆ Module.End ℂ (MvPolynomial ι ℂ) where
  toFun a := (matrixPolynomialDerivationLie a).toLinearMap
  map_add' a b := congrArg Derivation.toLinearMap (map_add matrixPolynomialDerivationLie a b)
  map_smul' c a := congrArg Derivation.toLinearMap (map_smul matrixPolynomialDerivationLie c a)
  map_lie' {a b} := congrArg Derivation.toLinearMap (matrixPolynomialDerivationLie.map_lie a b)

end
end Dubon2026
