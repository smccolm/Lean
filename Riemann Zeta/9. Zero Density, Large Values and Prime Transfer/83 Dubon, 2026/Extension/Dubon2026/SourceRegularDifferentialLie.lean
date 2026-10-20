import Dubon2026.SourceRegularDifferential

/-! The actual infinitesimal right action is a Lie algebra homomorphism.
Equality of derivations is reduced to the original matrix coordinates via
the already proved universal property of the determinant localization.
This avoids any extra localization-derivation framework on the source
coefficient irreducibility dependency chain.
-/

namespace Dubon2026
noncomputable section
open Matrix TrivSqZeroExt

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Encoding a derivation of the original regular-function algebra by its exact dual-number lift. -/
private def sourceRegularDerivationLift
    (D : Derivation R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n)) :
    GeneralLinearRegularFunctions R n →ₐ[R] DualNumber (GeneralLinearRegularFunctions R n) where
  toFun p := inl p + inr (D p)
  map_zero' := by simp
  map_one' := by simp
  map_add' p q := by ext <;> simp
  map_mul' p q := by ext <;> simp [Derivation.leibniz, mul_comm]
  commutes' r := by
    simp only [Derivation.map_algebraMap, inr_zero, add_zero]
    rfl

/-- Derivations of the original determinant localization are determined by their values on the original matrix coordinates. -/
theorem sourceRegular_derivation_ext
    {D E : Derivation R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n)}
    (h : ∀ i j : Fin n,
      D (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) =
        E (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j)))) : D = E := by
  have he : sourceRegularDerivationLift D = sourceRegularDerivationLift E := by
    apply generalLinearRegular_algHom_ext
    intro i j
    simp only [sourceRegularDerivationLift, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk, h i j]
  apply Derivation.ext
  intro p
  have hp := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun he p)
  simpa [sourceRegularDerivationLift] using hp

/-- The differential of the original right action is additive in the original matrix. -/
theorem sourceRegularDifferential_add (X Y : Matrix (Fin n) (Fin n) R) :
    sourceRegularDifferential (X + Y) = sourceRegularDifferential X + sourceRegularDifferential Y := by
  apply sourceRegular_derivation_ext
  intro i j
  simp [sourceRegularDifferential_X, mul_add, Finset.sum_add_distrib]

/-- The differential of the original right action is linear over the original coefficient ring. -/
theorem sourceRegularDifferential_smul (r : R) (X : Matrix (Fin n) (Fin n) R) :
    sourceRegularDifferential (r • X) = r • sourceRegularDifferential X := by
  apply sourceRegular_derivation_ext
  intro i j
  simp only [sourceRegularDifferential_X, Derivation.smul_apply, Matrix.smul_apply,
    smul_eq_mul, map_mul]
  simp [Algebra.smul_def, Finset.mul_sum, mul_left_comm]

/-- Differentiating the original generic matrix multiplied by a constant matrix gives its product with the same infinitesimal matrix in the original action order. -/
theorem sourceRegularDifferential_generic_mul (X Y : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) :
    sourceRegularDifferential X
      (((generalLinearRegularGeneric R n).val * Y.map
        (algebraMap R (GeneralLinearRegularFunctions R n))) i j) =
      ((generalLinearRegularGeneric R n).val * X.map (algebraMap R (GeneralLinearRegularFunctions R n)) *
        Y.map (algebraMap R (GeneralLinearRegularFunctions R n))) i j := by
  simp [Matrix.mul_apply, generalLinearRegularGeneric_apply, sourceRegularDifferential_X,
    Derivation.leibniz, mul_comm]

/-- The coordinate differential in its exact matrix-product form. -/
theorem sourceRegularDifferential_X_matrix (X : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    sourceRegularDifferential X
      (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) =
      ((generalLinearRegularGeneric R n).val *
        X.map (algebraMap R (GeneralLinearRegularFunctions R n))) i j :=
  sourceRegularDifferential_X X i j

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual differential respects the original matrix Lie bracket, with the right-translation action order proved on the original coordinates. -/
theorem sourceRegularDifferential_lie (X Y : Matrix (Fin n) (Fin n) R) :
    sourceRegularDifferential ⁅X, Y⁆ = ⁅sourceRegularDifferential X, sourceRegularDifferential Y⁆ := by
  apply sourceRegular_derivation_ext
  intro i j
  rw [Derivation.commutator_apply, sourceRegularDifferential_X_matrix,
    sourceRegularDifferential_X_matrix, sourceRegularDifferential_X_matrix,
    sourceRegularDifferential_generic_mul, sourceRegularDifferential_generic_mul]
  change ((generalLinearRegularGeneric R n).val *
    (algebraMap R (GeneralLinearRegularFunctions R n)).mapMatrix (X * Y - Y * X)) i j = _
  simp only [map_sub, map_mul, mul_sub, Matrix.sub_apply, Matrix.mul_assoc]
  rfl

/-- The Lie algebra of original matrices acts by derivations of the original regular-function algebra, obtained by differentiating the exact right action. -/
def sourceRegularDifferentialLieHom :
    Matrix (Fin n) (Fin n) R →ₗ⁅R⁆
      Derivation R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n) where
  toFun := sourceRegularDifferential
  map_add' := sourceRegularDifferential_add
  map_smul' := sourceRegularDifferential_smul
  map_lie' {X Y} := sourceRegularDifferential_lie X Y

end
end Dubon2026
