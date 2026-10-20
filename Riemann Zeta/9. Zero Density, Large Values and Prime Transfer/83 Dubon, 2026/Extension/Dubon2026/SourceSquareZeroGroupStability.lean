import Dubon2026.SourceSquareZeroOrbitExponential

/-! Actual elementary group-stability from the original infinitesimal action.
The finite exponential has been proved for the same regular functions and
the same right action. Consequently an original differential-stable
subspace is stable under the corresponding actual square-zero subgroup.
This is a required step toward group-stability of the source Lie complements.
-/

namespace Dubon2026
noncomputable section
open Matrix

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions K n

omit [CharZero K] in
/-- The powers of the exact source differential preserve every subspace stable under that differential. -/
theorem sourceRegularDifferential_pow_mem
    (X : Matrix (Fin n) (Fin n) K) (W : Submodule K S)
    (hW : ∀ p ∈ W, sourceRegularDifferential X p ∈ W)
    {p : S} (hp : p ∈ W) (k : ℕ) :
    ((sourceRegularDifferential X).toLinearMap ^ k) p ∈ W := by
  induction k with
  | zero => simpa only [pow_zero, Module.End.one_apply] using hp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hW _ ih

/-- Every original subspace stable under the exact differential is stable under the actual corresponding square-zero one-parameter subgroup. -/
theorem sourceSquareZero_action_mem_of_differential
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (W : Submodule K S)
    (hW : ∀ p ∈ W, sourceRegularDifferential X p ∈ W)
    (t : K) {p : S} (hp : p ∈ W) :
    generalLinearRegularRightTranslate (sourceSquareZeroLine X hX t) p ∈ W := by
  rw [sourceSquareZero_action_eq_finite_exp X hX t p
    (Nat.lt_succ_self (sourceRegularSquareZeroCurve X hX p).natDegree)]
  apply W.sum_mem
  intro k _
  exact W.smul_mem _ (sourceRegularDifferential_pow_mem X W hW hp k)

/-- An original function annihilated by the exact differential is fixed by the actual corresponding square-zero subgroup. -/
theorem sourceSquareZero_action_eq_of_differential_zero
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (t : K) (p : S)
    (hp : sourceRegularDifferential X p = 0) :
    generalLinearRegularRightTranslate (sourceSquareZeroLine X hX t) p = p := by
  rw [sourceSquareZero_action_eq_finite_exp X hX t p
    (Nat.lt_succ_self (sourceRegularSquareZeroCurve X hX p).natDegree)]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [pow_succ (sourceRegularDifferential X).toLinearMap, Module.End.mul_apply]
    change (t ^ (j + 1) * ((j + 1).factorial : K)⁻¹) •
      ((sourceRegularDifferential X).toLinearMap ^ j) (sourceRegularDifferential X p) = 0
    rw [hp, map_zero, smul_zero]
  · simp

end
end Dubon2026
