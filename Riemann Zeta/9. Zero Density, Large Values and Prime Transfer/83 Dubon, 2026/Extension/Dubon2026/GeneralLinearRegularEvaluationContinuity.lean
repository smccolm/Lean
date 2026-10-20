import Dubon2026.GeneralLinearIntegralPolynomialStages
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Field

/-! Original regular functions are continuous on the original coefficient
field's general linear group. The exact determinant fraction is evaluated;
native polynomial continuity and the nonzero original determinant give
continuity without putting an artificial topology on the coordinate ring.
This serves the source integral induced action's module-topology proof.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R E : Type u) [CommRing R] [Field E] [Algebra R E] (n : ℕ)

/-- Evaluation of the actual original determinant fraction has its literal field-valued denominator and numerator. -/
theorem generalLinearRegularFractionMap_eval (d : ℕ)
    (P : MvPolynomial (Fin n × Fin n) R) (g : GeneralLinearGroup (Fin n) E) :
    generalLinearRegularEval g (generalLinearRegularFractionMap R n d P) =
      (g.val.det ^ d)⁻¹ * MvPolynomial.aeval (fun ij : Fin n × Fin n => g.val ij.1 ij.2) P := by
  have hd : generalLinearRegularEval (R := R) g
      (generalLinearRegularDeterminantUnit (R := R) (n := n) : GeneralLinearRegularFunctions R n) =
      g.val.det := by
    simpa only [zpow_one] using generalLinearRegularEval_determinant_zpow (R := R) g 1
  change generalLinearRegularEval g
    ((((generalLinearRegularDeterminantUnit ^ d)⁻¹ : (GeneralLinearRegularFunctions R n)ˣ) :
        GeneralLinearRegularFunctions R n) *
      generalLinearRegularPolynomialMap R n P) = _
  rw [map_mul, map_units_inv, Units.val_pow_eq_pow_val, map_pow, hd,
    generalLinearRegularEval_polynomial]

/-- Every original integral regular function is continuous when evaluated on the original coefficient-field matrices. -/
theorem generalLinearRegularEval_continuous
    [TopologicalSpace E] [IsTopologicalDivisionRing E] (p : GeneralLinearRegularFunctions R n) :
    Continuous (fun g : GeneralLinearGroup (Fin n) E => generalLinearRegularEval g p) := by
  obtain ⟨d, P, rfl⟩ := generalLinearRegular_exists_fraction R n p
  simp_rw [generalLinearRegularFractionMap_eval R E n]
  have hv : Continuous (fun g : GeneralLinearGroup (Fin n) E => g.val) := Units.continuous_val
  have hd : Continuous (fun g : GeneralLinearGroup (Fin n) E => g.val.det) := hv.matrix_det
  apply ((hd.pow d).inv₀ (fun g => pow_ne_zero d (GeneralLinearGroup.det_ne_zero g))).mul
  have hc : Continuous (fun g : GeneralLinearGroup (Fin n) E =>
      fun ij : Fin n × Fin n => g.val ij.1 ij.2) :=
    continuous_pi fun ij => (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp hv)
  simpa only [MvPolynomial.eval_map, ← MvPolynomial.aeval_def] using
    (MvPolynomial.continuous_eval (MvPolynomial.map (algebraMap R E) P)).comp hc

end
end Dubon2026
