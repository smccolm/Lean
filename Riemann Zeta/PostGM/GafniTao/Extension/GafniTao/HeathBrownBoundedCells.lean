import GafniTao.HeathBrownBoundedBranch
import GafniTao.Section3Algebra

/-!
# Bounded-shell estimates in the three Heath--Brown cells

The bounded member of the logarithmic cover is harmless only after inserting
the correct ordinary zero-density theorem.  Ingham supplies the first two
cells; Huxley supplies the third.
-/

namespace GafniTao

noncomputable section

/-- Huxley's publication-facing theorem in the coefficient normalization of
`ZeroDensityEnvelope`. -/
theorem huxley_zeroDensityEnvelope
    {sigma : Real} (hsigmaLower : 3 / 4 ≤ sigma)
    (hsigmaUpper : sigma ≤ 1) :
    ZeroDensityEnvelope sigma (3 / (3 * sigma - 1)) := by
  have hHuxley := RiemannZeta.GuthMaynard.huxleyZeroDensity_published_native
    sigma hsigmaLower hsigmaUpper
  unfold ZeroDensityEnvelope EpsilonExponentBound
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hHuxley

theorem heathBrown_bounded_first_coefficient
    {sigma : Real} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 2 / 3) :
    2 * (3 / (2 - sigma)) ≤
      (10 - 11 * sigma) / ((2 - sigma) * (1 - sigma)) := by
  have hden1 : 0 < 2 - sigma := by linarith
  have hden2 : 0 < 1 - sigma := by linarith
  rw [show 2 * (3 / (2 - sigma)) = 6 / (2 - sigma) by ring]
  rw [div_le_div_iff₀ hden1 (mul_pos hden1 hden2)]
  nlinarith

theorem heathBrown_bounded_second_coefficient
    {sigma : Real} (hsigmaLower : 2 / 3 ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 4) :
    2 * (3 / (2 - sigma)) ≤
      (18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma)) := by
  have hden1 : 0 < 2 - sigma := by linarith
  have hden2 : 0 < 1 - sigma := by linarith
  have hdenLeft : 0 < 4 - 2 * sigma := by linarith
  have hden : 0 < (4 - 2 * sigma) * (1 - sigma) :=
    mul_pos hdenLeft hden2
  rw [show 2 * (3 / (2 - sigma)) = 6 / (2 - sigma) by ring]
  rw [div_le_div_iff₀ hden1 hden]
  nlinarith

theorem heathBrown_bounded_third_coefficient
    {sigma : Real} (hsigmaLower : 3 / 4 ≤ sigma)
    (hsigmaUpper : sigma < 1) :
    2 * (3 / (3 * sigma - 1)) ≤ 12 / (4 * sigma - 1) := by
  have hden1 : 0 < 3 * sigma - 1 := by linarith
  have hden2 : 0 < 4 * sigma - 1 := by linarith
  rw [show 2 * (3 / (3 * sigma - 1)) =
    6 / (3 * sigma - 1) by ring]
  rw [div_le_div_iff₀ hden1 hden2]
  nlinarith

theorem heathBrownBoundedShellMajorant_first_cell
    {sigma R0 : Real} (hsigmaLower : 1 / 2 ≤ sigma)
    (hsigmaUpper : sigma ≤ 2 / 3) :
    EpsilonExponentBound (heathBrownBoundedShellMajorant sigma R0)
      (((10 - 11 * sigma) /
        ((2 - sigma) * (1 - sigma))) * (1 - sigma)) := by
  have h := heathBrownBoundedShellMajorant_envelope
    (R0 := R0) (ingham_zeroDensityEnvelope hsigmaLower (by linarith))
  apply h.mono_exponent
  calc
    2 * (3 / (2 - sigma) * (1 - sigma)) =
        (2 * (3 / (2 - sigma))) * (1 - sigma) := by ring
    _ ≤ ((10 - 11 * sigma) / ((2 - sigma) * (1 - sigma))) *
        (1 - sigma) := mul_le_mul_of_nonneg_right
          (heathBrown_bounded_first_coefficient hsigmaLower hsigmaUpper)
          (by linarith)

theorem heathBrownBoundedShellMajorant_second_cell
    {sigma R0 : Real} (hsigmaLower : 2 / 3 ≤ sigma)
    (hsigmaUpper : sigma ≤ 3 / 4) :
    EpsilonExponentBound (heathBrownBoundedShellMajorant sigma R0)
      (((18 - 19 * sigma) /
        ((4 - 2 * sigma) * (1 - sigma))) * (1 - sigma)) := by
  have hhalf : 1 / 2 ≤ sigma := by linarith
  have h := heathBrownBoundedShellMajorant_envelope
    (R0 := R0) (ingham_zeroDensityEnvelope hhalf (by linarith))
  apply h.mono_exponent
  calc
    2 * (3 / (2 - sigma) * (1 - sigma)) =
        (2 * (3 / (2 - sigma))) * (1 - sigma) := by ring
    _ ≤ ((18 - 19 * sigma) / ((4 - 2 * sigma) * (1 - sigma))) *
        (1 - sigma) := mul_le_mul_of_nonneg_right
          (heathBrown_bounded_second_coefficient hsigmaLower hsigmaUpper)
          (by linarith)

theorem heathBrownBoundedShellMajorant_third_cell
    {sigma R0 : Real} (hsigmaLower : 3 / 4 < sigma)
    (hsigmaUpper : sigma < 1) :
    EpsilonExponentBound (heathBrownBoundedShellMajorant sigma R0)
      ((12 / (4 * sigma - 1)) * (1 - sigma)) := by
  have h := heathBrownBoundedShellMajorant_envelope
    (R0 := R0) (huxley_zeroDensityEnvelope hsigmaLower.le hsigmaUpper.le)
  apply h.mono_exponent
  calc
    2 * (3 / (3 * sigma - 1) * (1 - sigma)) =
        (2 * (3 / (3 * sigma - 1))) * (1 - sigma) := by ring
    _ ≤ (12 / (4 * sigma - 1)) * (1 - sigma) :=
      mul_le_mul_of_nonneg_right
        (heathBrown_bounded_third_coefficient hsigmaLower.le hsigmaUpper)
        (by linarith)

#print axioms huxley_zeroDensityEnvelope
#print axioms heathBrownBoundedShellMajorant_first_cell
#print axioms heathBrownBoundedShellMajorant_second_cell
#print axioms heathBrownBoundedShellMajorant_third_cell

end

end GafniTao
