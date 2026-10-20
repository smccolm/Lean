import Dubon2026.GeneralLinearIntegralPolynomialStages
import Dubon2026.MatrixPolynomialDensity

/-! Original field-valued matrix evaluations separate integral regular
functions. The adapted polynomial identity theorem on GL is reused after
clearing the actual determinant denominator. This is the faithful
evaluation embedding needed for continuity of the source coefficient
action in its finite-module topology.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R E : Type u) [CommRing R] [Field E] [Algebra R E] (n : ℕ)

/-- Every original regular function is evaluated at the actual general linear matrices over the original coefficient field. -/
def generalLinearRegularFieldEvaluation :
    GeneralLinearRegularFunctions R n →ₗ[R] (GeneralLinearGroup (Fin n) E → E) where
  toFun p g := generalLinearRegularEval g p
  map_add' p q := funext fun g => map_add (generalLinearRegularEval g) p q
  map_smul' a p := funext fun g => (generalLinearRegularEval g).toLinearMap.map_smul a p

/-- If every actual invertible matrix over the coefficient field evaluates an integral regular function to zero, that same original regular function is zero. -/
theorem generalLinearRegular_eq_zero_of_field_eval [Infinite E]
    (hRE : Function.Injective (algebraMap R E)) (p : GeneralLinearRegularFunctions R n)
    (hp : ∀ g : GeneralLinearGroup (Fin n) E, generalLinearRegularEval g p = 0) : p = 0 := by
  obtain ⟨d, P, rfl⟩ := generalLinearRegular_exists_fraction R n p
  have hc : generalLinearRegularPolynomialMap R n P =
      ((generalLinearRegularDeterminantUnit ^ d : (GeneralLinearRegularFunctions R n)ˣ) :
        GeneralLinearRegularFunctions R n) * generalLinearRegularFractionMap R n d P := by
    simp only [generalLinearRegularFractionMap, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, ← mul_assoc, Units.mul_inv, one_mul]
  have hP (g : GeneralLinearGroup (Fin n) E) :
      MvPolynomial.aeval (fun ij : Fin n × Fin n => g.val ij.1 ij.2) P = 0 := by
    rw [← generalLinearRegularEval_polynomial, hc, map_mul, hp g, mul_zero]
  have hQ : MvPolynomial.map (algebraMap R E) P = 0 := by
    apply MvPolynomial.eq_of_eval_eq_on_gl
    intro g
    simpa only [MvPolynomial.eval_map, ← MvPolynomial.aeval_def, map_zero] using hP g
  have hP0 : P = 0 := (MvPolynomial.map_injective (algebraMap R E) hRE)
    (hQ.trans (map_zero _).symm)
  rw [hP0, map_zero]

/-- The literal family of original coefficient-field evaluations is injective on the original integral regular-function ring. -/
theorem generalLinearRegularFieldEvaluation_injective [Infinite E]
    (hRE : Function.Injective (algebraMap R E)) :
    Function.Injective (generalLinearRegularFieldEvaluation R E n) := by
  apply (generalLinearRegularFieldEvaluation R E n).ker_eq_bot.mp
  apply LinearMap.ker_eq_bot.mpr
  intro p q hpq
  have hz : p - q = 0 := generalLinearRegular_eq_zero_of_field_eval R E n hRE (p - q) (by
    intro g
    have he := congrFun hpq g
    change generalLinearRegularEval g p = generalLinearRegularEval g q at he
    rw [map_sub, he, sub_self])
  exact sub_eq_zero.mp hz

end
end Dubon2026
