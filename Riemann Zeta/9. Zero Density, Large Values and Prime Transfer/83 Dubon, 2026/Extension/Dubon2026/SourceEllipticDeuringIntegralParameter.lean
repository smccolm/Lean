import Dubon2026.SourceEllipticTorsionIntegralCoordinates
import Mathlib.Tactic

/-! The Deuring parameter is integral and its discriminant is a unit.
Adapted from TauCeti PotentialGoodReduction, Apache-2.0, commit
e177885ee120f8074a7610c3e60571ab00b20004. The monic degree-twelve
relation and discriminant divisor of 3^6 replace valuation growth
arguments. This is the DUB-17/18 characteristic-two good-model input. -/
namespace Dubon2026.SourceEllipticDeuring
open Polynomial
noncomputable section
variable {M : Type*} [Field M]

theorem exists_integral_deuring_parameter (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (j : A) {a : M} (hrel : (j : M) * (a ^ 3 - 27) = a ^ 3 * (a ^ 3 - 24) ^ 3) :
    ∃ α : A, (α : M) = a ∧ IsUnit (α ^ 3 - 27) := by
  have ha : a ∈ A := by
    apply SourceEllipticFunctionField.mem_valuationSubring_of_integral A
    refine ⟨X ^ 3 * (X ^ 3 - 24) ^ 3 - C j * (X ^ 3 - 27), ?_, ?_⟩
    · monicity!
    · simp only [eval₂_sub, eval₂_pow, eval₂_mul, eval₂_X, eval₂_C, eval₂_ofNat]
      exact sub_eq_zero.mpr hrel.symm
  let α : A := ⟨a, ha⟩
  have hd : (α ^ 3 - 27) * (j - (α ^ 9 - 45 * α ^ 6 + 513 * α ^ 3 + 27)) = 3 ^ 6 := by
    apply Subtype.val_injective
    change (a ^ 3 - 27) * ((j : M) - (a ^ 9 - 45 * a ^ 6 + 513 * a ^ 3 + 27)) = 3 ^ 6
    linear_combination hrel
  exact ⟨α, rfl, isUnit_of_mul_isUnit_left (hd ▸ h3.pow 6)⟩

end
end Dubon2026.SourceEllipticDeuring
