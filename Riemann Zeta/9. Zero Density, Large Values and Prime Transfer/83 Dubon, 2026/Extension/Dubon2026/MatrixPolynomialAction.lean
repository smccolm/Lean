import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic
import Mathlib.Analysis.Complex.Basic

/-! # The actual matrix substitution action on homogeneous polynomials -/

namespace Dubon2026

noncomputable section
open MvPolynomial

variable {R ι : Type*} [CommSemiring R] [Fintype ι]

/-- The genuine matrix action on each polynomial generator is its original column linear form. -/
def matrixPolynomialAction (g : Matrix ι ι R) : MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  aeval (fun i => ∑ j, g j i • X j)

/-- Substitution sends each original variable to the exact column linear form. -/
theorem matrixPolynomialAction_X (g : Matrix ι ι R) (i : ι) :
    matrixPolynomialAction g (X i) = ∑ j, g j i • X j := aeval_X _ i

/-- The actual identity matrix induces the identity polynomial substitution. -/
theorem matrixPolynomialAction_one [DecidableEq ι] :
    matrixPolynomialAction (1 : Matrix ι ι R) = AlgHom.id R (MvPolynomial ι R) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [matrixPolynomialAction_X, Matrix.one_apply]

/-- Matrix multiplication agrees with composition of the genuine polynomial substitutions. -/
theorem matrixPolynomialAction_mul (g h : Matrix ι ι R) :
    matrixPolynomialAction (g * h) = (matrixPolynomialAction g).comp (matrixPolynomialAction h) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [matrixPolynomialAction_X, AlgHom.comp_apply, map_sum, map_smul,
    Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_comm]

/-- Every genuine linear matrix substitution preserves the original homogeneous degree. -/
theorem matrixPolynomialAction_homogeneous (g : Matrix ι ι R) {n : ℕ}
    {p : MvPolynomial ι R} (hp : p.IsHomogeneous n) : (matrixPolynomialAction g p).IsHomogeneous n := by
  have hg : ∀ i, (∑ j, g j i • (X j : MvPolynomial ι R)).IsHomogeneous 1 := by
    intro i
    apply IsHomogeneous.sum
    intro j _
    exact (homogeneousSubmodule ι R 1).smul_mem (g j i) (isHomogeneous_X R j)
  have h := hp.aeval (fun i => ∑ j, g j i • X j) hg
  simpa only [one_mul] using h

/-- Restrict actual matrix substitution to the genuine space of homogeneous degree n polynomials. -/
def homogeneousMatrixAction (n : ℕ) (g : Matrix ι ι R) :
    Module.End R (homogeneousSubmodule ι R n) :=
  (matrixPolynomialAction g).toLinearMap.restrict
    (fun _ hp => matrixPolynomialAction_homogeneous g hp)

/-- The restricted action retains the exact original polynomial substitution. -/
theorem homogeneousMatrixAction_apply (n : ℕ) (g : Matrix ι ι R)
    (p : homogeneousSubmodule ι R n) :
    (homogeneousMatrixAction n g p).val = matrixPolynomialAction g p.val := rfl

/-- All original matrices act on the actual homogeneous space as a genuine monoid representation. -/
def homogeneousMatrixRepresentation [DecidableEq ι] (n : ℕ) :
    Representation R (Matrix ι ι R) (homogeneousSubmodule ι R n) where
  toFun := homogeneousMatrixAction n
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact AlgHom.congr_fun matrixPolynomialAction_one p.val
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    exact AlgHom.congr_fun (matrixPolynomialAction_mul g h) p.val

/-- The genuine general linear group over the original coefficient ring acts by the original homogeneous polynomial substitution. -/
def homogeneousGLRepresentation [DecidableEq ι] (n : ℕ) :
    Representation R (Matrix.GeneralLinearGroup ι R) (homogeneousSubmodule ι R n) :=
  (homogeneousMatrixRepresentation n).comp (Units.coeHom (Matrix ι ι R))

end
end Dubon2026
