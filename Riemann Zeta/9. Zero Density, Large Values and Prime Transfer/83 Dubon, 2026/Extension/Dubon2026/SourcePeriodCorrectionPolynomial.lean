import Dubon2026.SourcePeriodCocycle
import Dubon2026.SourcePeriodPolynomialBound
import Dubon2026.FiniteSymmetricMonomialOrbit

/-! The actual polynomial correction of an original period coboundary.
DUB-17/18 -> higher symmetric-power continuation -> modular Galois
association -> original H1 injectivity -> scalar Eichler correction.
Reuse the original binary monomial basis and the convergent period map.
The correction is explicitly polynomial, so cusp periodicity can discharge
boundedness using SourcePeriodPolynomialBound. Injectivity is not yet asserted.
-/

namespace Dubon2026
noncomputable section
open MvPolynomial SourceModularSymbols
open scoped BigOperators

/-- The original degree-n Eichler kernel as a homogeneous binary form. -/
def sourceEichlerBinaryForm (n : ℕ) (z : ℂ) :
    homogeneousSubmodule (Fin 2) ℂ n :=
  ⟨(X 0 - C z * X 1) ^ n, by
    simpa using ((isHomogeneous_X ℂ (0 : Fin 2)).sub (isHomogeneous_C_mul_X z 1)).pow n⟩

/-- Evaluating the Eichler kernel gives the original scalar integral kernel. -/
theorem sourceEichlerBinaryForm_periodIntegrand (f : UpperHalfPlane → ℂ)
    (n : ℕ) (z : ℂ) :
    periodIntegrand f (sourceEichlerBinaryForm n z) =
      fun τ => f τ * ((τ : ℂ) - z) ^ n := by
  funext τ
  simp [sourceEichlerBinaryForm]

/-- The literal binomial expansion in the already proved binary monomial basis. -/
theorem sourceEichlerBinaryForm_eq_sum (n : ℕ) (z : ℂ) :
    sourceEichlerBinaryForm n z =
      ∑ i : Fin (n + 1), ((n.choose i.val : ℂ) * (-z) ^ (n - i.val)) •
        binaryHomogeneousMonomialBasis n i := by
  apply Subtype.ext
  simp only [sourceEichlerBinaryForm, Submodule.coe_sum, Submodule.coe_smul,
    binaryHomogeneousMonomialBasis_val, smul_eq_C_mul]
  rw [sub_eq_add_neg, ← neg_mul, ← map_neg, add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow]
  simp only [map_mul, map_pow, map_natCast]
  ring

/-- A dual binary vector gives an explicit polynomial in the Eichler argument. -/
def sourcePeriodCorrectionPolynomial (n : ℕ)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n)) : Polynomial ℂ :=
  ∑ i : Fin (n + 1),
    Polynomial.C ((n.choose i.val : ℂ) * L (binaryHomogeneousMonomialBasis n i)) *
      (-Polynomial.X) ^ (n - i.val)

/-- The correction polynomial evaluates to the actual dual coefficient vector. -/
theorem sourcePeriodCorrectionPolynomial_eval (n : ℕ)
    (L : Module.Dual ℂ (homogeneousSubmodule (Fin 2) ℂ n)) (z : ℂ) :
    (sourcePeriodCorrectionPolynomial n L).eval z = L (sourceEichlerBinaryForm n z) := by
  rw [sourceEichlerBinaryForm_eq_sum, map_sum]
  simp only [sourcePeriodCorrectionPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_neg, Polynomial.eval_X, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end Dubon2026
