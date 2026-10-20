import Dubon2026.SourceSquareZeroOrbitExponential

/-! Exact all-algebra elementary invariance from the original differential.
The actual orbit polynomial is constant, so evaluation over any original
coefficient algebra gives the same original regular function.
-/

namespace Dubon2026
noncomputable section
open Matrix Polynomial

universe u v
variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions K n

/-- An original infinitesimal invariant has a constant actual square-zero orbit polynomial. -/
theorem sourceSquareZeroCurve_constant
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (p : S)
    (hp : sourceRegularDifferential X p = 0) :
    sourceRegularSquareZeroCurve X hX p = Polynomial.C p := by
  apply Polynomial.ext
  intro k
  cases k with
  | zero => simp only [sourceRegularSquareZeroCurve_zero, coeff_C_zero]
  | succ k =>
    rw [sourceSquareZeroCurve_coeff,
      pow_succ (sourceRegularDifferential X).toLinearMap, Module.End.mul_apply]
    change (((k + 1).factorial : K)⁻¹) •
      ((sourceRegularDifferential X).toLinearMap ^ k) (sourceRegularDifferential X p) =
        (Polynomial.C p).coeff (k + 1)
    rw [hp, map_zero, smul_zero]
    simp

/-- Original differential invariance gives original square-zero group invariance over every coefficient algebra, with its original parameter and original matrix evaluation. -/
theorem sourceSquareZero_allAlgebra_invariant
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (p : S)
    (hp : sourceRegularDifferential X p = 0)
    {A : Type v} [CommRing A] [Algebra K A]
    (g : GeneralLinearGroup (Fin n) A) (t : A) :
    generalLinearRegularEval (R := K)
      (g * sourceSquareZeroLine (X.map (algebraMap K A))
        (sourceSquareZeroMatrix_map (algebraMap K A) X hX) t) p =
      generalLinearRegularEval (R := K) g p := by
  let f : S →ₐ[K] A := generalLinearRegularEval g
  letI : Algebra S A := f.toRingHom.toAlgebra
  letI : IsScalarTower K S A := IsScalarTower.of_algHom f
  have he := sourceRegularSquareZeroCurve_aeval (B := A) X hX t p
  have hg : GeneralLinearGroup.map (algebraMap S A) (generalLinearRegularGeneric K n) = g :=
    generalLinearRegularGeneric_eval K n g
  rw [hg, sourceSquareZeroCurve_constant X hX p hp, aeval_C] at he
  exact he.symm

end
end Dubon2026
