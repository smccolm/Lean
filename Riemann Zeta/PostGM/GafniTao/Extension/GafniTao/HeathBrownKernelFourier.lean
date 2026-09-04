import GafniTao.HeathBrownTriangularKernel
import GafniTao.FordTentSeries

/-!
# Fourier expansion of Heath-Brown's triangular kernel

This file identifies the literal nearest-integer tent in Heath-Brown's
Section 3 with the already proved periodic tent Fourier series.  It then
forms the absolutely convergent two-dimensional product.  In particular,
the nonnegative coefficients below are the coefficients of the actual
kernel, rather than an independently chosen majorant.
-/

namespace GafniTao

noncomputable section

theorem heathBrownDistanceToInteger_eq_unitAddCircle_norm (x : ℝ) :
    heathBrownDistanceToInteger x = ‖(x : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  rfl

theorem heathBrownHat_eq_fordTent (B x : ℝ) :
    heathBrownHat B x = fordTent x B := by
  unfold heathBrownHat fordTent
  rw [heathBrownDistanceToInteger_eq_unitAddCircle_norm]
  simp only [div_eq_mul_inv]
  rw [mul_comm B⁻¹ ‖(x : UnitAddCircle)‖]
  rw [max_comm]

theorem heathBrownHatFourierCoefficient_eq_fordTent
    {B : ℝ} (hB : 0 < B) (r : ℤ) :
    (heathBrownHatFourierCoefficient B r : ℂ) =
      fordTentFourierCoefficient B r := by
  by_cases hr : r = 0
  · subst r
    simp [heathBrownHatFourierCoefficient_zero,
      fordTentFourierCoefficient_zero]
  · have harg : Real.pi * (r : ℝ) * B ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero Real.pi_ne_zero (Int.cast_ne_zero.mpr hr)) hB.ne'
    simp only [heathBrownHatFourierCoefficient,
      heathBrownSincCoefficient, hr, if_false,
      fordTentFourierCoefficient]
    rw [Real.sinc_of_ne_zero harg]

/-- The exact one-dimensional Fourier series of Heath-Brown's tent. -/
theorem hasSum_heathBrownHatFourierSeries
    {B : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2) (x : ℝ) :
    HasSum
      (fun r : ℤ => (heathBrownHatFourierCoefficient B r : ℂ) *
        fordAdditiveCharacter ((r : ℝ) * x))
      (heathBrownHat B x : ℂ) := by
  convert hasSum_fordTentFourierSeries hB hBHalf x using 1
  · ext r
    rw [heathBrownHatFourierCoefficient_eq_fordTent hB]
  · rw [heathBrownHat_eq_fordTent]

theorem summable_norm_heathBrownHatFourierTerm
    {B : ℝ} (hB : 0 < B) (x : ℝ) :
    Summable (fun r : ℤ =>
      ‖(heathBrownHatFourierCoefficient B r : ℂ) *
        fordAdditiveCharacter ((r : ℝ) * x)‖) := by
  have hs := summable_fordTentFourierCoefficient hB
  convert hs.norm using 1
  funext r
  rw [heathBrownHatFourierCoefficient_eq_fordTent hB, norm_mul]
  unfold fordAdditiveCharacter
  rw [Complex.norm_exp]
  simp

/-- The exact absolutely convergent two-dimensional Fourier expansion of
Heath-Brown's kernel `phi(x,y)`. -/
theorem hasSum_heathBrownTriangularFourierSeries
    {B C : ℝ} (hB : 0 < B) (hBHalf : B ≤ 1 / 2)
    (hC : 0 < C) (hCHalf : C ≤ 1 / 2) (x y : ℝ) :
    HasSum
      (fun rs : ℤ × ℤ =>
        (heathBrownTriangularFourierCoefficient B C rs.1 rs.2 : ℂ) *
          fordAdditiveCharacter ((rs.1 : ℝ) * x) *
          fordAdditiveCharacter ((rs.2 : ℝ) * y))
      (heathBrownTriangularKernel B C x y : ℂ) := by
  let f : ℤ → ℂ := fun r =>
    (heathBrownHatFourierCoefficient B r : ℂ) *
      fordAdditiveCharacter ((r : ℝ) * x)
  let g : ℤ → ℂ := fun s =>
    (heathBrownHatFourierCoefficient C s : ℂ) *
      fordAdditiveCharacter ((s : ℝ) * y)
  have hf : HasSum f (heathBrownHat B x : ℂ) :=
    hasSum_heathBrownHatFourierSeries hB hBHalf x
  have hg : HasSum g (heathBrownHat C y : ℂ) :=
    hasSum_heathBrownHatFourierSeries hC hCHalf y
  have habsF : Summable (fun r : ℤ => ‖f r‖) :=
    summable_norm_heathBrownHatFourierTerm hB x
  have habsG : Summable (fun s : ℤ => ‖g s‖) :=
    summable_norm_heathBrownHatFourierTerm hC y
  have hcross : Summable (fun rs : ℤ × ℤ => f rs.1 * g rs.2) :=
    summable_mul_of_summable_norm habsF habsG
  convert hf.mul hg hcross using 1
  · ext rs
    simp only [f, g, heathBrownTriangularFourierCoefficient]
    push_cast
    ring
  · simp only [heathBrownTriangularKernel]
    push_cast
    rfl

#print axioms heathBrownDistanceToInteger_eq_unitAddCircle_norm
#print axioms heathBrownHat_eq_fordTent
#print axioms heathBrownHatFourierCoefficient_eq_fordTent
#print axioms hasSum_heathBrownHatFourierSeries
#print axioms summable_norm_heathBrownHatFourierTerm
#print axioms hasSum_heathBrownTriangularFourierSeries

end

end GafniTao
