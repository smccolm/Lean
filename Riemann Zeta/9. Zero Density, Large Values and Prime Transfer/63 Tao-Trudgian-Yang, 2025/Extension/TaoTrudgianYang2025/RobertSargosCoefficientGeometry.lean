import TaoTrudgianYang2025.RobertSargosDisplacement

/-! Complementary fixed-displacement geometry for Robert--Sargos (2002).
Every ratio and affine-band estimate follows from the actual source system. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_reduced_coefficient_factor {r q₁ q₂ h₁ h₂ d : ℝ}
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0) :
    robertSargosReduced r q₁ q₂ h₁ h₂ d =
      h₁*q₁*(q₁+d)-h₂*q₂*(q₂-d) := by
  rw [robertSargos_reduced_symmetric hlin]
  ring

theorem robertSargos_affine_residual_identity {r q₁ q₂ h₁ h₂ d : ℝ}
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0) :
    h₂*q₂*(q₁+2*d-q₂) =
      robertSargosReduced r q₁ q₂ h₁ h₂ d+r*d*(q₁+d) := by
  rw [robertSargos_reduced_coefficient_factor hlin]
  linear_combination -(q₁+d)*hlin

theorem robertSargos_coefficient_linear_ratio_gap {r q₁ q₂ h₁ h₂ d R D H Q : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hr : |r| ≤ R) (hd : |d| ≤ D)
    (hh₂ : H ≤ h₂) (hq₁ : Q ≤ |q₁|)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0) :
    |h₁/h₂-q₂/q₁| ≤ R*D/(H*Q) := by
  have hh₂p := hH.trans_le hh₂
  have hq₁p := hQ.trans_le hq₁
  have hq₁n := abs_pos.mp hq₁p
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have he : h₁/h₂-q₂/q₁ = -r*d/(h₂*q₁) := by
    field_simp
    nlinarith only [hlin]
  rw [he,abs_div,abs_mul,abs_neg,abs_mul,abs_of_pos hh₂p]
  have hnum : |r| * |d| ≤ R*D := mul_le_mul hr hd (abs_nonneg d) hR
  have hden : H*Q ≤ h₂*|q₁| := mul_le_mul hh₂ hq₁ hQ.le hh₂p.le
  exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
    (div_le_div_of_nonneg_left (mul_nonneg hR hD) (mul_pos hH hQ) hden)

theorem robertSargos_coefficient_conic_ratio_gap {r q₁ q₂ h₁ h₂ d H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hh₂ : H ≤ h₂) (hq₁ : Q ≤ |q₁|) (hsafe : 0 ≤ q₁*d)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |h₁/h₂-q₂*(q₂-d)/(q₁*(q₁+d))| ≤ δ := by
  have hh₂p := hH.trans_le hh₂
  have hq : Q^2 ≤ q₁*(q₁+d) := by
    have hs := (sq_le_sq₀ hQ.le (abs_nonneg q₁)).mpr hq₁
    rw [sq_abs] at hs
    nlinarith
  have hqp : 0 < q₁*(q₁+d) := (sq_pos_of_pos hQ).trans_le hq
  have hqn : q₁ ≠ 0 := (mul_ne_zero_iff.mp hqp.ne').1
  have hsn : q₁+d ≠ 0 := (mul_ne_zero_iff.mp hqp.ne').2
  have hdenp : 0 < h₂*(q₁*(q₁+d)) := mul_pos hh₂p hqp
  have hden : H*Q^2 ≤ h₂*(q₁*(q₁+d)) :=
    mul_le_mul hh₂ hq (sq_nonneg Q) hh₂p.le
  have he : h₁/h₂-q₂*(q₂-d)/(q₁*(q₁+d)) =
      robertSargosReduced r q₁ q₂ h₁ h₂ d/(h₂*(q₁*(q₁+d))) := by
    rw [robertSargos_reduced_coefficient_factor hlin]
    field_simp [hh₂p.ne',hqn,hsn]
  rw [he,abs_div,abs_of_pos hdenp]
  apply (div_le_iff₀ hdenp).mpr
  calc
    _ ≤ δ*H*Q^2 := hnear
    _ ≤ δ*(h₂*(q₁*(q₁+d))) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hden hδ

end TaoTrudgianYang2025
