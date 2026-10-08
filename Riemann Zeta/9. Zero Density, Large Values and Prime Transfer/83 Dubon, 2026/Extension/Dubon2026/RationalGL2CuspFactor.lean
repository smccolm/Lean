import Dubon2026.CanonicalAdelicGL2CuspLift
import Dubon2026.RealCyclicCuspidal

/-! # Actual integral-cusp and upper-triangular factors of rational positive GL2 matrices -/

namespace Dubon2026

noncomputable section
open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup OnePoint
open scoped MatrixGroups

/-- The original positive rational matrix has an actual integral cusp representative and upper-triangular right factor. -/
theorem positiveRationalGL2_integral_upper_factor (γ : GL(2, ℚ)⁺) :
    ∃ σ : SL(2, ℤ), ∃ b : GL(2, ℚ)⁺,
      γ = toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ) * b ∧
      b.val.val 1 0 = 0 := by
  obtain ⟨σ, hσ⟩ := (γ.val • (∞ : OnePoint ℚ)).exists_mem_SL2 ℤ
  let a : GL(2, ℚ)⁺ := toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ)
  have ha : a.val = mapGL ℚ σ := by
    apply Units.ext
    rfl
  refine ⟨σ, a⁻¹ * γ, ?_, ?_⟩
  · change γ = a * (a⁻¹ * γ)
    group
  · apply OnePoint.smul_infty_eq_self_iff.mp
    change (a.val⁻¹ * γ.val) • (∞ : OnePoint ℚ) = ∞
    rw [mul_smul, ← hσ, ← ha, inv_smul_smul]

/-- Original upper-triangular determinant-one matrices have a nonzero first diagonal entry. -/
theorem realSL2_upper_first_ne_zero (b : SL(2, ℝ)) (hb : b 1 0 = 0) : b 0 0 ≠ 0 := by
  have hd := b.property
  rw [Matrix.det_fin_two] at hd
  change b 0 0 * b 1 1 - b 0 1 * b 1 0 = 1 at hd
  rw [hb, mul_zero, sub_zero] at hd
  exact left_ne_zero_of_mul_eq_one hd

/-- The actual upper-triangular factor rescales the genuine unipotent parameter by the square of its first entry. -/
theorem realSL2_upper_unipotent (b : SL(2, ℝ)) (hb : b 1 0 = 0) (t : ℝ) :
    b * realUpperUnipotent t = realUpperUnipotent (b 0 0 ^ 2 * t) * b := by
  have hd := b.property
  rw [Matrix.det_fin_two] at hd
  change b 0 0 * b 1 1 - b 0 1 * b 1 0 = 1 at hd
  rw [hb, mul_zero, sub_zero] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      realUpperUnipotent, hb]
  linear_combination -(b 0 0 * t) * hd

/-- Actual rational-to-real coordinates preserve the original integral positive matrix embedding. -/
theorem rationalPositiveGL2ToReal_integral (σ : SL(2, ℤ)) :
    rationalPositiveGL2ToReal
      (toGLPos (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ) σ)) =
      toGLPos (integralToRealSL σ) := by
  apply Subtype.ext
  apply Units.ext
  funext i j
  exact map_intCast (Rat.castHom ℝ) (σ i j)

/-- The genuine positive-real normalization of an upper-triangular rational factor remains upper triangular. -/
theorem realPositiveNormalize_rational_upper (b : GL(2, ℚ)⁺)
    (hb : b.val.val 1 0 = 0) : realPositiveNormalize (rationalPositiveGL2ToReal b) 1 0 = 0 := by
  change ((realPositiveDetRoot (rationalPositiveGL2ToReal b))⁻¹ : ℝ) *
    (b.val.val 1 0 : ℝ) = 0
  rw [hb, Rat.cast_zero, mul_zero]

end
end Dubon2026
