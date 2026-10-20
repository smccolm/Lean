import Dubon2026.GeneralLinearIntegralPolynomialStages
import Mathlib.Data.Fin.Rev

/-! The central character of the literal integral induced functions.
After clearing a determinant denominator this fixes the numerator's
scaling weight, the degree input to the uniform polynomial-stage bound.
No denominator bound or finite generation of the full module is claimed.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

/-- An original scalar unit is an actual element of the source upper Borel. -/
def generalLinearBorelScalar (u : Rˣ) : generalLinearBorel R n :=
  ⟨GeneralLinearGroup.scalar (Fin n) u, Matrix.blockTriangular_diagonal _⟩

/-- Every diagonal unit of the original Borel scalar is the same original scalar unit. -/
theorem generalLinearBorelScalar_diagonal (u : Rˣ) (i : Fin n) :
    generalLinearBorelDiagonalUnit (generalLinearBorelScalar (n := n) u) i = u := by
  apply Units.ext
  change Matrix.scalar (Fin n) (u : R) i i = u
  simp

/-- The original reversed-weight Borel character restricts to the central character with exponent equal to the sum of the original weights. -/
theorem generalLinearBorelWeight_scalar (lam : Fin n → ℤ) (u : Rˣ) :
    generalLinearBorelWeight lam (generalLinearBorelScalar u) = u ^ (∑ i, lam i) := by
  rw [generalLinearBorelWeight_apply]
  simp_rw [generalLinearBorelScalar_diagonal]
  have hprod (s : Finset (Fin n)) :
      ∏ i ∈ s, u ^ lam i.rev = u ^ (∑ i ∈ s, lam i.rev) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, ih, zpow_add]
  rw [hprod]
  congr 1
  exact Equiv.sum_comp Fin.revPerm lam

/-- The actual integral induced functions have the exact source central scaling law over every coefficient algebra. -/
theorem generalLinearIntegralInduced_scalar (lam : Fin n → ℤ)
    {p : GeneralLinearRegularFunctions R n}
    (hp : p ∈ generalLinearIntegralInducedSubmodule R n lam)
    (A : Type u) [CommRing A] [Algebra R A]
    (u : Aˣ) (g : GeneralLinearGroup (Fin n) A) :
    generalLinearRegularEval (GeneralLinearGroup.scalar (Fin n) u * g) p =
      ((u ^ (∑ i, lam i) : Aˣ) : A) * generalLinearRegularEval g p := by
  simpa only [generalLinearBorelWeight_scalar] using hp A g (generalLinearBorelScalar u)

/-- Clearing an actual determinant denominator fixes the original numerator's central scaling weight to sum(lambda) + n*d. -/
theorem generalLinearIntegralInduced_numerator_scalar (lam : Fin n → ℤ)
    (d : ℕ) (P : MvPolynomial (Fin n × Fin n) R)
    (hP : generalLinearRegularFractionMap R n d P ∈
      generalLinearIntegralInducedSubmodule R n lam)
    (A : Type u) [CommRing A] [Algebra R A]
    (u : Aˣ) (g : GeneralLinearGroup (Fin n) A) :
    MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      (GeneralLinearGroup.scalar (Fin n) u * g).val ij.1 ij.2) P =
      ((u ^ ((∑ i, lam i) + (n : ℤ) * d) : Aˣ) : A) *
        MvPolynomial.aeval (fun ij : Fin n × Fin n => g.val ij.1 ij.2) P := by
  have h := generalLinearIntegralInduced_scalar (fun i => lam i + (d : ℤ))
    (generalLinearIntegralInduced_polynomial_numerator R n lam d P hP) A u g
  simpa only [generalLinearRegularEval_polynomial, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h

end
end Dubon2026
