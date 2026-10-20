import Dubon2026.SourceSquareZeroCurveDifferential

/-! The finite exponential formula for the original source right action.
The exact orbit polynomial and its proved differential equation identify
every coefficient with the corresponding power of the actual derivative.
This is the required bridge from Lie-stability to elementary group-stability.
-/

namespace Dubon2026
noncomputable section
open Matrix Polynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions K n

omit [CharZero K] in
/-- The actual square-zero orbit coefficients satisfy the exact differential recurrence. -/
theorem sourceSquareZeroCurve_coeff_succ
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (p : S) (k : ℕ) :
    ((k + 1 : ℕ) : K) • (sourceRegularSquareZeroCurve X hX p).coeff (k + 1) =
      (sourceRegularSquareZeroCurve X hX (sourceRegularDifferential X p)).coeff k := by
  have h := congrArg (fun q : Polynomial S => q.coeff k)
    (sourceRegularSquareZeroCurve_derivative X hX p)
  dsimp only at h
  rw [coeff_derivative] at h
  simpa only [Algebra.smul_def, map_natCast, mul_comm] using h

/-- Every coefficient of the original orbit polynomial is the exact factorial-scaled iterate of the original differential. -/
theorem sourceSquareZeroCurve_coeff
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (p : S) (k : ℕ) :
    (sourceRegularSquareZeroCurve X hX p).coeff k =
      ((k.factorial : K)⁻¹) • ((sourceRegularDifferential X).toLinearMap ^ k) p := by
  induction k generalizing p with
  | zero =>
    simp only [sourceRegularSquareZeroCurve_zero, Nat.factorial_zero, Nat.cast_one,
      inv_one, pow_zero, Module.End.one_apply, one_smul]
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
    calc
      (sourceRegularSquareZeroCurve X hX p).coeff (k + 1) =
          ((k + 1 : ℕ) : K)⁻¹ •
            (((k + 1 : ℕ) : K) • (sourceRegularSquareZeroCurve X hX p).coeff (k + 1)) := by
              rw [smul_smul, inv_mul_cancel₀ hk, one_smul]
      _ = ((k + 1 : ℕ) : K)⁻¹ •
          (sourceRegularSquareZeroCurve X hX (sourceRegularDifferential X p)).coeff k := by
            rw [sourceSquareZeroCurve_coeff_succ]
      _ = (((k + 1).factorial : K)⁻¹) •
          ((sourceRegularDifferential X).toLinearMap ^ (k + 1)) p := by
            rw [ih, smul_smul, Nat.factorial_succ, Nat.cast_mul, mul_inv, pow_succ,
              Module.End.mul_apply]
            rfl

omit [CharZero K] in
/-- The actual orbit polynomial evaluates to the original right action of the same square-zero matrix. -/
theorem sourceSquareZeroCurve_eval_action
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (t : K) (p : S) :
    (sourceRegularSquareZeroCurve X hX p).eval (algebraMap K S t) =
      generalLinearRegularRightTranslate (sourceSquareZeroLine X hX t) p := by
  have h := sourceRegularSquareZeroCurve_aeval X hX (algebraMap K S t) p
  rw [← sourceSquareZeroLine_map] at h
  simpa only [Algebra.algebraMap_self, GeneralLinearGroup.map_id, MonoidHom.id_apply,
    coe_aeval_eq_eval, generalLinearRegularRightTranslate] using h

/-- The original elementary right action is a finite exponential of its actual derivative, with the truncation justified by the original orbit polynomial's degree. -/
theorem sourceSquareZero_action_eq_finite_exp
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (t : K) (p : S)
    {N : ℕ} (hN : (sourceRegularSquareZeroCurve X hX p).natDegree < N) :
    generalLinearRegularRightTranslate (sourceSquareZeroLine X hX t) p =
      ∑ k ∈ Finset.range N,
        (t ^ k * (k.factorial : K)⁻¹) • ((sourceRegularDifferential X).toLinearMap ^ k) p := by
  rw [← sourceSquareZeroCurve_eval_action, eval_eq_sum_range' hN]
  apply Finset.sum_congr rfl
  intro k _
  rw [sourceSquareZeroCurve_coeff]
  simp only [Algebra.smul_def, map_mul, map_pow]
  ring

end
end Dubon2026
