import Dubon2026.SourcePolynomialCoefficientSubmodule
import Dubon2026.SourceSquareZeroGroupStability
import Mathlib.Algebra.CharZero.Infinite

/-! Recovering original differential stability from actual elementary orbits.
Coefficient extraction applies to the proved finite exponential of the same
original regular function, rather than to a supplied representation model.
-/

namespace Dubon2026
noncomputable section
open Matrix
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}
local notation "S" => GeneralLinearRegularFunctions K n

/-- A subspace stable under the original square-zero one-parameter subgroup is stable under its actual source differential. -/
theorem sourceSquareZero_differential_mem_of_group
    (X : Matrix (Fin n) (Fin n) K) (hX : X * X = 0) (W : Submodule K S)
    (hW : ∀ t : K, ∀ p ∈ W,
      generalLinearRegularRightTranslate (sourceSquareZeroLine X hX t) p ∈ W)
    (p : S) (hp : p ∈ W) : sourceRegularDifferential X p ∈ W := by
  have h := sourcePolynomial_coeff_mem_of_values_mem W
    (N := (sourceRegularSquareZeroCurve X hX p).natDegree + 2)
    (fun k => ((k.factorial : K)⁻¹) • ((sourceRegularDifferential X).toLinearMap ^ k) p)
    (fun t => by
      have hm := hW t p hp
      rw [sourceSquareZero_action_eq_finite_exp X hX t p
        (show (sourceRegularSquareZeroCurve X hX p).natDegree <
          (sourceRegularSquareZeroCurve X hX p).natDegree + 2 by omega)] at hm
      simpa only [smul_smul] using hm)
    (k := 1) (by omega)
  simpa using h

end
end Dubon2026
