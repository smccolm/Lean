import Dubon2026.CuspPointwiseRankinBound
import Dubon2026.PrimitiveSecondContinuation

/-! # Nonvanishing of the genuine symmetric-square continuation at one -/

namespace Dubon2026

noncomputable section

/-- The proved Rankin pointwise bound puts every actual ramified square Euler coordinate inside the unit disk on Re(s)>3/5. -/
theorem norm_primitive_rankin_bad_term_lt_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {p : ℕ} (hp : Nat.Prime p) (hpQ : p ∣ Q)
    {s : ℂ} (hs : 3 / 5 < s.re) :
    ‖((‖normalizedCuspCoefficients f.toCuspForm p‖ ^ 2 : ℝ) : ℂ) * (p : ℂ) ^ (-s)‖ < 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc
    _ ≤ (p : ℝ) ^ (3 / 5 : ℝ) * (p : ℝ) ^ (-s.re) :=
      mul_le_mul_of_nonneg_right (primitive_bad_coefficient_norm_sq_le_three_fifths f hk hp hpQ)
        (Real.rpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (3 / 5 - s.re) := by rw [← Real.rpow_add hp0, sub_eq_add_neg]
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)

/-- The genuine finite ramified Rankin correction is nonzero throughout Re(s)>3/5. -/
theorem primitiveRankinBadCorrection_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) {s : ℂ} (hs : 3 / 5 < s.re) :
    primitiveRankinBadCorrection f s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hn := norm_primitive_rankin_bad_term_lt_one f hk p.property
    ((mem_ramifiedPrimeSet (Nat.pos_of_neZero Q) p).mp hp) hs
  intro hz
  have he := sub_eq_zero.mp hz
  rw [← he, norm_one] at hn
  exact lt_irrefl _ hn

/-- The genuine symmetric-square continuation at one has the exact Petersson residue and actual principal-character normalization. -/
theorem primitiveSecondContinuation_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 0 < k) :
    primitiveSecondContinuation f 1 =
      (cuspRankinResidue f.toCuspForm : ℂ) * primitiveRankinBadCorrection f 1 *
        DirichletCharacter.LFunctionTrivChar Q 2 /
          (∏ p ∈ Q.primeFactors, (1 - (p : ℂ)⁻¹)) := by
  rw [primitiveSecondContinuation, cuspRankinPoleNumerator_one f.toCuspForm hk]
  simp only [mul_one, DirichletCharacter.LFunctionTrivChar₁, Function.update_self]

/-- Positive Rankin residue and the proved nonzero ramified correction give nonvanishing of the actual symmetric-square continuation at one, without Deligne. -/
theorem primitiveSecondContinuation_one_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    primitiveSecondContinuation f 1 ≠ 0 := by
  rw [primitiveSecondContinuation, cuspRankinPoleNumerator_one f.toCuspForm (by omega), mul_one]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero
        (Complex.ofReal_ne_zero.mpr (cuspRankinResidue_pos f.toCuspForm (by omega)
          (primitiveCuspForm_ne_zero f)).ne')
        (primitiveRankinBadCorrection_ne_zero f hk (by norm_num))
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ Q)
        (.inr (by norm_num)) (by norm_num)
  · exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero Q

end
end Dubon2026
