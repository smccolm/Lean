import Dubon2026.CuspCoefficientMellin
import Dubon2026.PrimitiveRamifiedBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Entire continuation of the genuine normalized cusp L-series -/

namespace Dubon2026

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Topology

noncomputable section

/-- The genuine normalized cusp L-function obtained by removing the exact Gamma and exponential factors from its actual Mellin integral. -/
def normalizedCuspLFunction {Q : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (s + ((k : ℂ) - 1) / 2) *
    (Complex.Gamma (s + ((k : ℂ) - 1) / 2))⁻¹ *
      cuspCompletedLFunction f (s + ((k : ℂ) - 1) / 2)

/-- The actual normalized cusp L-function is entire; the reciprocal Gamma factor is entire even at the Gamma poles. -/
theorem normalizedCuspLFunction_differentiable {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 < k) :
    Differentiable ℂ (normalizedCuspLFunction f) := by
  have hz : Differentiable ℂ (fun s : ℂ => s + ((k : ℂ) - 1) / 2) := differentiable_id.add_const _
  have hc : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  exact ((hz.const_cpow (Or.inl hc)).mul (Complex.differentiable_one_div_Gamma.comp hz)).mul
    ((cuspCompletedLFunction_differentiable f hk).comp hz)

/-- The entire function agrees with the actual normalized coefficient L-series throughout Re(s)>1. -/
theorem normalizedCuspLFunction_eq_series {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (hk : 0 ≤ k)
    {s : ℂ} (hs : 1 < s.re) :
    normalizedCuspLFunction f s = LSeries (normalizedCuspCoefficients f) s := by
  have hz : 0 < (s + ((k : ℂ) - 1) / 2).re := by
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.sub_re, Complex.intCast_re, Complex.one_re]
    have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hG := Complex.Gamma_ne_zero_of_re_pos hz
  have hC : ((2 * Real.pi : ℝ) : ℂ) ^ (s + ((k : ℂ) - 1) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  rw [normalizedCuspLFunction, cuspCompletedLFunction_eq_normalized_series f hk hs, Complex.cpow_neg]
  let A := ((2 * Real.pi : ℝ) : ℂ) ^ (s + ((k : ℂ) - 1) / 2)
  let B := Complex.Gamma (s + ((k : ℂ) - 1) / 2)
  change A * B⁻¹ * (A⁻¹ * B * LSeries (normalizedCuspCoefficients f) s) = _
  calc
    _ = (A * A⁻¹) * (B⁻¹ * B) * LSeries (normalizedCuspCoefficients f) s := by ring
    _ = _ := by rw [mul_inv_cancel₀ hC, inv_mul_cancel₀ hG, one_mul, one_mul]

/-- Multiplying by exactly the actual ramified denominators gives an entire continuation of the genuine order-one incomplete symmetric Euler product. Nonvanishing on Re(s)=1 is still a separate obligation. -/
theorem primitive_first_symmetric_entire_continuation {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      Set.EqOn F (primitiveSymmetricLFunction f 1) {s | 1 < s.re} := by
  refine ⟨fun s => normalizedCuspLFunction f.toCuspForm s *
    ∏ p ∈ ramifiedPrimeSet Q, primitiveEulerDenominator f p s, ?_, ?_⟩
  · exact (normalizedCuspLFunction_differentiable f.toCuspForm hk).mul
      (fun _ => DifferentiableAt.fun_finsetProd (fun p _ => primitiveEulerDenominator_differentiable f p _))
  · intro s hs
    dsimp only
    rw [normalizedCuspLFunction_eq_series f.toCuspForm hk.le hs,
      primitive_first_symmetric_eq_cusp_lseries f hk.le hs]

end
end Dubon2026
