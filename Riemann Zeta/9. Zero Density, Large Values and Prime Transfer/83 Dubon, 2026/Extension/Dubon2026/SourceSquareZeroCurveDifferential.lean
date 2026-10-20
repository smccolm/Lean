import Dubon2026.SourceRegularSquareZeroCurve

/-! The exact differential equation of the source unipotent orbit polynomial.
The original matrix identity for a square-zero direction gives parameter
addition over dual numbers. Native polynomial Taylor expansion then
identifies the derivative with the original differentiated right action.
-/

namespace Dubon2026
noncomputable section
open Matrix Polynomial TrivSqZeroExt

variable {R : Type*} [CommRing R] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions R n
local notation "P" => Polynomial S
local notation "B" => DualNumber P

/-- The native polynomial semiring, using its commutative-ring projection to keep the original evaluation maps definitionally aligned. -/
local instance sourceCurvePolynomialSemiring :
    Semiring (Polynomial (GeneralLinearRegularFunctions R n)) :=
  (inferInstance : CommRing (Polynomial (GeneralLinearRegularFunctions R n))).toSemiring

/-- The native dual-number semiring, using the same commutative-ring projection as the original general-linear point maps. -/
local instance sourceCurveDualSemiring :
    Semiring (DualNumber (Polynomial (GeneralLinearRegularFunctions R n))) :=
  (inferInstance : CommRing (DualNumber (Polynomial (GeneralLinearRegularFunctions R n)))).toSemiring

/-- Adding the infinitesimal parameter to an actual square-zero matrix orbit agrees with its exact dual-number translate. -/
theorem sourceSquareZeroLine_infinitesimalPoint
    {A : Type*} [CommRing A] [Algebra R A]
    (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0)
    (g : GeneralLinearGroup (Fin n) A) (t : A) :
    sourceInfinitesimalPointAt X
      (g * sourceSquareZeroLine (X.map (algebraMap R A))
        (sourceSquareZeroMatrix_map (algebraMap R A) X hX) t) =
      GeneralLinearGroup.map (inlAlgHom R A A).toRingHom g *
        sourceSquareZeroLine (X.map (algebraMap R (DualNumber A)))
          (sourceSquareZeroMatrix_map (algebraMap R (DualNumber A)) X hX)
          (inl t + DualNumber.eps) := by
  have hZ : (X.map (algebraMap R A)).map (inlAlgHom R A A).toRingHom =
      X.map (algebraMap R (DualNumber A)) := by
    ext i j <;> rfl
  have hline : GeneralLinearGroup.map (inlAlgHom R A A).toRingHom
      (sourceSquareZeroLine (X.map (algebraMap R A))
        (sourceSquareZeroMatrix_map (algebraMap R A) X hX) t) =
      sourceSquareZeroLine (X.map (algebraMap R (DualNumber A)))
        (sourceSquareZeroMatrix_map (algebraMap R (DualNumber A)) X hX) (inl t) := by
    rw [sourceSquareZeroLine_map]
    apply Units.ext
    change 1 + inl t • (X.map (algebraMap R A)).map (inlAlgHom R A A).toRingHom =
      1 + inl t • X.map (algebraMap R (DualNumber A))
    rw [hZ]
  have hinf : sourceInfinitesimalMatrix (X.map (algebraMap R A)) =
      sourceSquareZeroLine (X.map (algebraMap R (DualNumber A)))
        (sourceSquareZeroMatrix_map (algebraMap R (DualNumber A)) X hX)
        DualNumber.eps := by
    apply Units.ext
    rfl
  rw [sourceInfinitesimalPointAt, map_mul, hline,
    hinf, mul_assoc, ← sourceSquareZeroLine_add]

/-- The actual dual-number parameter shift of the original orbit polynomial. -/
def sourcePolynomialDualShift : P →ₐ[R] B :=
  (aeval (R := S) (inl (Polynomial.X : P) + (DualNumber.eps : B))).restrictScalars R

/-- The infinitesimal translate of the actual polynomial orbit is its substitution at `t + ε`. -/
theorem sourceSquareZeroCurve_infinitesimalPoint
    (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) :
    sourceInfinitesimalPointAt (R := R) (A := P) X (sourceSquareZeroCurvePoint X hX) =
      GeneralLinearGroup.map (sourcePolynomialDualShift (R := R) (n := n)).toRingHom
        (sourceSquareZeroCurvePoint X hX) := by
  have he := sourceSquareZeroCurvePoint_aeval (R := R) (n := n) («B» := B)
    X hX (inl (Polynomial.X : P) + (DualNumber.eps : B))
  have hg := sourceSquareZeroLine_infinitesimalPoint (R := R) (A := P) X hX
    (GeneralLinearGroup.map (algebraMap S P) (generalLinearRegularGeneric R n)) Polynomial.X
  exact hg.trans he.symm

/-- Native Taylor expansion extracts the actual polynomial derivative from the epsilon coefficient at `t + ε`. -/
theorem sourcePolynomial_derivative_dual (q : P) :
    (aeval (inl (Polynomial.X : P) + (DualNumber.eps : B)) q).snd = q.derivative := by
  have he : (DualNumber.eps : B) ^ 2 = 0 := by
    rw [pow_two, DualNumber.eps_mul_eps]
  rw [aeval_add_of_sq_eq_zero q (inl (Polynomial.X : P) : B) (DualNumber.eps : B) he]
  have ha (f : P) : aeval (inl (Polynomial.X : P) : B) f = inl f := by
    change aeval ((inlAlgHom S P P) Polynomial.X) f = (inlAlgHom S P P) f
    rw [aeval_algHom, AlgHom.comp_apply, aeval_X_left_apply]
  rw [ha, ha]
  simp

/-- The actual source orbit polynomial satisfies `d/dt f(g(1+tX)) = (D_X f)(g(1+tX))`. -/
theorem sourceRegularSquareZeroCurve_derivative
    (X : Matrix (Fin n) (Fin n) R) (hX : X * X = 0) (p : S) :
    (sourceRegularSquareZeroCurve X hX p).derivative =
      sourceRegularSquareZeroCurve X hX (sourceRegularDifferential X p) := by
  rw [← sourcePolynomial_derivative_dual]
  have h := AlgHom.congr_fun (generalLinearRegularEval_natural (R := R) (A := P) («B» := B)
    (sourcePolynomialDualShift (R := R) (n := n))
    (sourceSquareZeroCurvePoint X hX)) p
  change aeval (inl (Polynomial.X : P) + (DualNumber.eps : B))
      (sourceRegularSquareZeroCurve X hX p) =
    generalLinearRegularEval (R := R) (A := B)
      (GeneralLinearGroup.map (sourcePolynomialDualShift (R := R) (n := n)).toRingHom
        (sourceSquareZeroCurvePoint X hX)) p at h
  rw [h, ← sourceSquareZeroCurve_infinitesimalPoint]
  exact (sourceRegularDifferential_eval X (sourceSquareZeroCurvePoint X hX) p).symm

end
end Dubon2026
