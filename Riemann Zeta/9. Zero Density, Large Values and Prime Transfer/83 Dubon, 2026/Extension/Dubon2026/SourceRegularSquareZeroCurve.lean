import Dubon2026.SourceSquareZeroLine

/-! Polynomial curves of the actual right action along elementary unipotent directions.
These are polynomials with coefficients in the original regular-function
ring, obtained by evaluation of the same original function. They supply
the finite exponential argument needed to recover group-stability from
the already constructed source Lie action.
-/

namespace Dubon2026
noncomputable section
open Matrix Polynomial

universe u v
variable {R : Type u} [CommRing R] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions R n

/-- The original generic matrix multiplied by the actual polynomial square-zero line. -/
def sourceSquareZeroCurvePoint (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) :
    GeneralLinearGroup (Fin n) (Polynomial S) :=
  GeneralLinearGroup.map (algebraMap S (Polynomial S)) (generalLinearRegularGeneric R n) *
    sourceSquareZeroLine (X.map (algebraMap R (Polynomial S)))
      (sourceSquareZeroMatrix_map (algebraMap R (Polynomial S)) X hX) Polynomial.X

/-- The actual original regular function along the polynomial square-zero right orbit. -/
def sourceRegularSquareZeroCurve (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) :
    S →ₐ[R] Polynomial S :=
  generalLinearRegularEval (R := R) (A := Polynomial S) (sourceSquareZeroCurvePoint X hX)

variable {B : Type v} [CommRing B] [Algebra R B]
  [Algebra (GeneralLinearRegularFunctions R n) B]
  [IsScalarTower R (GeneralLinearRegularFunctions R n) B]

/-- Substituting the actual polynomial parameter gives the same original matrix orbit over the coefficient algebra. -/
theorem sourceSquareZeroCurvePoint_aeval (X : Matrix (Fin n) (Fin n) R)
    (hX : X * X = 0) (t : B) :
    GeneralLinearGroup.map (aeval t).toRingHom (sourceSquareZeroCurvePoint X hX) =
      GeneralLinearGroup.map (algebraMap S B) (generalLinearRegularGeneric R n) *
        sourceSquareZeroLine (X.map (algebraMap R B))
          (sourceSquareZeroMatrix_map (algebraMap R B) X hX) t := by
  rw [sourceSquareZeroCurvePoint, map_mul, sourceSquareZeroLine_map]
  have ht : (aeval t).toRingHom (Polynomial.X : Polynomial S) = t := aeval_X t
  rw [ht]
  congr 1
  · apply Units.ext
    apply Matrix.ext
    intro i j
    exact (aeval t).commutes _
  · apply Units.ext
    apply Matrix.ext
    intro i j
    change (1 + t • (X.map (algebraMap R (Polynomial S))).map (aeval t)) i j =
      (1 + t • X.map (algebraMap R B)) i j
    have hc : (X.map (algebraMap R (Polynomial S))).map (aeval t) =
        X.map (algebraMap R B) := by
      ext a b
      exact ((aeval t).restrictScalars R).commutes (X a b)
    rw [hc]

/-- Evaluating the exact orbit polynomial equals evaluating the original function at the actual parameterized matrix. -/
theorem sourceRegularSquareZeroCurve_aeval (X : Matrix (Fin n) (Fin n) R)
    (hX : X * X = 0) (t : B) (p : S) :
    aeval t (sourceRegularSquareZeroCurve X hX p) =
      generalLinearRegularEval (R := R)
        (GeneralLinearGroup.map (algebraMap S B) (generalLinearRegularGeneric R n) *
          sourceSquareZeroLine (X.map (algebraMap R B))
            (sourceSquareZeroMatrix_map (algebraMap R B) X hX) t) p := by
  have h := AlgHom.congr_fun (generalLinearRegularEval_natural
    ((aeval t).restrictScalars R) (sourceSquareZeroCurvePoint X hX)) p
  change aeval t (sourceRegularSquareZeroCurve X hX p) =
    generalLinearRegularEval (R := R)
      (GeneralLinearGroup.map (aeval t).toRingHom (sourceSquareZeroCurvePoint X hX)) p at h
  rw [sourceSquareZeroCurvePoint_aeval] at h
  exact h

/-- The constant coefficient of the original orbit polynomial is the same original function. -/
theorem sourceRegularSquareZeroCurve_zero (X : Matrix (Fin n) (Fin n) R)
    (hX : X * X = 0) (p : S) :
    (sourceRegularSquareZeroCurve X hX p).coeff 0 = p := by
  have h := sourceRegularSquareZeroCurve_aeval X hX (0 : S) p
  rw [sourceSquareZeroLine_zero, mul_one] at h
  simpa only [← coeff_zero_eq_aeval_zero, Algebra.algebraMap_self,
    GeneralLinearGroup.map_id, MonoidHom.id_apply, generalLinearRegularEval_generic,
    AlgHom.id_apply] using h

end
end Dubon2026
