import Dubon2026.SourceRegularDifferentialPowers
import Dubon2026.SourceRegularDeterminantDifferential

/-! Local nilpotence on the actual source determinant localization.
The original denominator is fixed, and every original polynomial numerator
is killed by a power of the same genuine differential. No finite-stage
replacement of the source regular-function ring is used.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

/-- Every trace-zero nilpotent original matrix acts locally nilpotently by its exact right-action differential on every original regular function. -/
theorem sourceRegularDifferential_locallyNilpotent
    (X : Matrix (Fin n) (Fin n) R) (hX : IsNilpotent X) (ht : X.trace = 0)
    (p : GeneralLinearRegularFunctions R n) :
    ∃ k : ℕ, ((sourceRegularDifferential X).toLinearMap ^ k) p = 0 := by
  obtain ⟨d, P, rfl⟩ := generalLinearRegular_exists_fraction R n p
  obtain ⟨k, hk⟩ := sourceRegularDifferential_polynomial_locallyNilpotent X hX P
  refine ⟨1 + k, ?_⟩
  change ((sourceRegularDifferential X).toLinearMap ^ (1 + k))
    ((((generalLinearRegularDeterminantUnit ^ d)⁻¹ :
      (GeneralLinearRegularFunctions R n)ˣ) : GeneralLinearRegularFunctions R n) *
      generalLinearRegularPolynomialMap R n P) = 0
  apply sourceDerivation_pow_mul_zero _ _ hk
  simpa only [pow_one] using
    sourceRegularDifferential_inverse_determinant_pow_zero X ht d

end
end Dubon2026
