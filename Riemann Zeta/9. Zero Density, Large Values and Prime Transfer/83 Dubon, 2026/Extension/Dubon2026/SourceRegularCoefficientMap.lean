import Dubon2026.GeneralLinearRegularPoints
import Mathlib.RingTheory.Localization.Basic

/-! Original regular-function coefficient change for the integral generic fibre.
The map evaluates the original coordinates at the generic matrix over the
extended coefficient ring. Its polynomial formula and compatibility with
every extended-algebra point keep the original functions and covariance.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

/-- Coefficient change on the original determinant-localized regular functions. -/
def sourceRegularCoefficientMap :
    GeneralLinearRegularFunctions R n →+* GeneralLinearRegularFunctions B n :=
  (generalLinearRegularEval (R := R) (generalLinearRegularGeneric B n)).toRingHom

/-- Original coordinate entries are preserved by actual coefficient change. -/
theorem sourceRegularCoefficientMap_X (i j : Fin n) :
    sourceRegularCoefficientMap R B n
      (generalLinearRegularPolynomialMap R n (MvPolynomial.X (i, j))) =
        generalLinearRegularPolynomialMap B n (MvPolynomial.X (i, j)) := by
  exact generalLinearRegularEval_X (R := R) (generalLinearRegularGeneric B n) i j

/-- Actual scalar coefficients change by the given coefficient-ring map. -/
theorem sourceRegularCoefficientMap_algebraMap (r : R) :
    sourceRegularCoefficientMap R B n (algebraMap R (GeneralLinearRegularFunctions R n) r) =
      algebraMap B (GeneralLinearRegularFunctions B n) (algebraMap R B r) := by
  rw [← IsScalarTower.algebraMap_apply R B (GeneralLinearRegularFunctions B n)]
  exact (generalLinearRegularEval (R := R) (generalLinearRegularGeneric B n)).commutes r

/-- Coefficient change sends every original polynomial numerator to that same polynomial with changed coefficients. -/
theorem sourceRegularCoefficientMap_polynomial (P : MvPolynomial (Fin n × Fin n) R) :
    sourceRegularCoefficientMap R B n (generalLinearRegularPolynomialMap R n P) =
      generalLinearRegularPolynomialMap B n (MvPolynomial.map (algebraMap R B) P) := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.map_C]
    simpa only [← MvPolynomial.algebraMap_eq, AlgHom.commutes] using
      sourceRegularCoefficientMap_algebraMap R B n r
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
    simp only [map_mul, MvPolynomial.map_X, hp,
      sourceRegularCoefficientMap_X R B n ij.1 ij.2]

variable {A : Type*} [CommRing A] [Algebra R A] [Algebra B A] [IsScalarTower R B A]

/-- Evaluating a changed original function at an extended-algebra point is exactly its original evaluation at that same point. -/
theorem sourceRegularCoefficientMap_eval (g : GeneralLinearGroup (Fin n) A)
    (p : GeneralLinearRegularFunctions R n) :
    generalLinearRegularEval (R := B) g (sourceRegularCoefficientMap R B n p) =
      generalLinearRegularEval (R := R) g p := by
  have he : ((generalLinearRegularEval (R := B) g).restrictScalars R).comp
      (generalLinearRegularEval (R := R) (generalLinearRegularGeneric B n)) =
      generalLinearRegularEval (R := R) g := by
    apply generalLinearRegular_algHom_ext
    intro i j
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      generalLinearRegularEval_X, generalLinearRegularGeneric_apply]
  exact congrArg (fun f => f p) he

end
end Dubon2026
