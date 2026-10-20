import Dubon2026.GeneralLinearRegularTranslation
import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Lie

/-! The exact infinitesimal right action on the original determinant localization.
This constructs the differential needed to apply the checked special-linear
complement theorem to the source induced coefficient module. Evaluation at the
original generic matrix times `1 + ε X` supplies the derivative; no abstract
representation or compatibility certificate is assumed.
-/

namespace Dubon2026
noncomputable section
open Matrix TrivSqZeroExt

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The original matrix `1 + ε X` is invertible over the dual numbers, with inverse `1 - ε X`. -/
def sourceInfinitesimalMatrix (X : Matrix (Fin n) (Fin n) R) :
    GeneralLinearGroup (Fin n) (DualNumber R) := by
  let N := (DualNumber.eps : DualNumber R) • X.map (algebraMap R (DualNumber R))
  have hN : N * N = 0 := by
    dsimp only [N]
    rw [smul_mul_smul_comm, DualNumber.eps_mul_eps, zero_smul]
  exact
    { val := 1 + N
      inv := 1 - N
      val_inv := by simp [mul_sub, add_mul, hN]
      inv_val := by simp [sub_mul, mul_add, hN] }

/-- Reducing the actual infinitesimal matrix modulo `ε` gives the identity matrix. -/
theorem sourceInfinitesimalMatrix_fst (X : Matrix (Fin n) (Fin n) R) :
    GeneralLinearGroup.map (fstHom R R R).toRingHom (sourceInfinitesimalMatrix X) = 1 := by
  apply Units.ext
  ext i j
  by_cases h : i = j <;> simp [sourceInfinitesimalMatrix, h]

/-- The actual generic matrix translated by the original infinitesimal matrix. -/
def sourceRegularInfinitesimalPoint (X : Matrix (Fin n) (Fin n) R) :
    GeneralLinearGroup (Fin n) (DualNumber (GeneralLinearRegularFunctions R n)) :=
  GeneralLinearGroup.map
    (inlAlgHom R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n)).toRingHom
      (generalLinearRegularGeneric R n) *
    sourceInfinitesimalMatrix (X.map (algebraMap R (GeneralLinearRegularFunctions R n)))

/-- The constant term of the original translated generic matrix is the original generic matrix. -/
theorem sourceRegularInfinitesimalPoint_fst (X : Matrix (Fin n) (Fin n) R) :
    GeneralLinearGroup.map
      (fstHom R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n)).toRingHom
      (sourceRegularInfinitesimalPoint X) = generalLinearRegularGeneric R n := by
  rw [sourceRegularInfinitesimalPoint, map_mul]
  have h : GeneralLinearGroup.map
      (fstHom R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n)).toRingHom
      (sourceInfinitesimalMatrix (X.map (algebraMap R (GeneralLinearRegularFunctions R n)))) = 1 :=
    sourceInfinitesimalMatrix_fst _
  rw [h, mul_one]
  apply Units.ext
  ext i j
  rfl

/-- Evaluation at the original infinitesimally translated generic matrix. -/
def sourceRegularInfinitesimalEval (X : Matrix (Fin n) (Fin n) R) :
    GeneralLinearRegularFunctions R n →ₐ[R] DualNumber (GeneralLinearRegularFunctions R n) :=
  generalLinearRegularEval (R := R) (A := DualNumber (GeneralLinearRegularFunctions R n))
    (sourceRegularInfinitesimalPoint X)

/-- Taking the constant term after the actual infinitesimal translation recovers the same original function. -/
theorem sourceRegularInfinitesimalEval_fst (X : Matrix (Fin n) (Fin n) R)
    (p : GeneralLinearRegularFunctions R n) :
    (sourceRegularInfinitesimalEval X p).fst = p := by
  have h := generalLinearRegularEval_natural (R := R)
    (A := DualNumber (GeneralLinearRegularFunctions R n)) (B := GeneralLinearRegularFunctions R n)
    (fstHom R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n))
    (sourceRegularInfinitesimalPoint X)
  rw [sourceRegularInfinitesimalPoint_fst, generalLinearRegularEval_generic] at h
  exact AlgHom.congr_fun h p

/-- The actual infinitesimal right-translation derivation of original regular functions. -/
def sourceRegularDifferential (X : Matrix (Fin n) (Fin n) R) :
    Derivation R (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n) where
  toLinearMap :=
    ((sndHom (GeneralLinearRegularFunctions R n) (GeneralLinearRegularFunctions R n)).restrictScalars R).comp
      (sourceRegularInfinitesimalEval X).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, sndHom_apply, map_mul,
      DualNumber.snd_mul, sourceRegularInfinitesimalEval_fst, smul_eq_mul]
    ring

/-- On every original matrix coordinate the differential is precisely the corresponding entry of the product of the original generic matrix with `X`. -/
theorem sourceRegularDifferential_X (X : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    sourceRegularDifferential X
      (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) =
      ∑ k, generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, k)) *
        algebraMap R (GeneralLinearRegularFunctions R n) (X k j) := by
  change (sourceRegularInfinitesimalEval X
    (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j)))).snd = _
  rw [sourceRegularInfinitesimalEval, generalLinearRegularEval_X]
  simp [sourceRegularInfinitesimalPoint, sourceInfinitesimalMatrix, Matrix.mul_apply,
    TrivSqZeroExt.snd_sum, generalLinearRegularGeneric_apply,
    Matrix.one_apply, apply_ite, TrivSqZeroExt.algebraMap_eq_inl]

end
end Dubon2026
