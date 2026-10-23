import Dubon2026.SourceCurveEffectiveDivisorSum
import Dubon2026.SourceModularCoefficientRiemannRoch
import Dubon2026.SourceModularCoefficientDerivativeOrders

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> Hurwitz.
The actual divisor of dj plus twice the pole divisor of j is effective.
Its degree is computed using the proved canonical-degree and separating
coordinate-degree formulas, in every characteristic. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The actual differential divisor corrected by twice the j-pole divisor. -/
def coeffHurwitzDivisor : Divisor K (modularFunctionFieldCoeff N K) :=
  coeffCanonicalDivisor N K (D_jCoeff_ne_zero N K) +
    2 • poleDivisor (jCoeff N K) (finite_coeff_divisor_support N K (jCoeff N K))

/-- The corrected divisor has the stated local differential and pole coefficients. -/
theorem coeffHurwitzDivisor_apply (v : Place K (modularFunctionFieldCoeff N K)) :
    coeffHurwitzDivisor N K v =
      v.ordDifferential (D K (modularFunctionFieldCoeff N K) (jCoeff N K)) +
        2 * max (-v.ord (jCoeff N K)) 0 := by
  simp only [coeffHurwitzDivisor, Finsupp.add_apply, Finsupp.smul_apply,
    coeffCanonicalDivisor_apply, poleDivisor_apply, nsmul_eq_mul, Nat.cast_ofNat]

/-- The corrected actual differential divisor is effective, including in wild characteristic. -/
theorem coeffHurwitzDivisor_nonneg (v : Place K (modularFunctionFieldCoeff N K)) :
    0 ≤ coeffHurwitzDivisor N K v := by
  rw [coeffHurwitzDivisor_apply]
  by_cases h : 0 ≤ v.ord (jCoeff N K)
  · have hd := coeff_place_integral_derivative_nonneg N K v (v.mem_of_ord_nonneg h)
    rw [max_eq_right (neg_nonpos.mpr h), mul_zero, add_zero]
    exact hd
  · have hd := coeff_place_ord_j_sub_one_le_D_j N K v
    rw [max_eq_left (by omega)]
    omega

/-- The corrected divisor has the actual Hurwitz degree over the j-coordinate field. -/
theorem degree_coeffHurwitzDivisor :
    Divisor.degree (coeffHurwitzDivisor N K) =
      2 * (genusFF K (modularFunctionFieldCoeff N K) : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin K {jCoeff N K})
          (modularFunctionFieldCoeff N K) : ℤ) := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  rw [coeffHurwitzDivisor, map_add, map_nsmul,
    coeff_canonical_degree_eq_genusFF N K,
    degree_poleDivisor_eq_finrank_separating (jCoeff N K) (transcendental_jCoeff N K)]
  rfl

end Dubon2026.SourceFunctionField
