import TaoTrudgianYang2025.RobertSargosCoefficientGeometry

/-! The narrow affine band in the remaining Robert--Sargos parameter cases. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_affine_band_of_displacement {r q₁ q₂ h₁ h₂ d R D H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hr : |r| ≤ R) (hd : |d| ≤ D)
    (hh₂ : H ≤ h₂) (hq₁ : |q₁| ≤ 2*Q) (hq₂ : Q ≤ |q₂|)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |2*d+q₁-q₂| ≤ δ*Q+R*D*(2*Q+D)/(H*Q) := by
  have hR : 0 ≤ R := (abs_nonneg r).trans hr
  have hD : 0 ≤ D := (abs_nonneg d).trans hd
  have hh₂p := hH.trans_le hh₂
  have hsum : |q₁+d| ≤ 2*Q+D :=
    (abs_add_le q₁ d).trans (add_le_add hq₁ hd)
  have hprod : |r*d*(q₁+d)| ≤ R*D*(2*Q+D) := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul hr hd (abs_nonneg d) hR) hsum
      (abs_nonneg (q₁+d)) (mul_nonneg hR hD)
  have hden : H*Q ≤ h₂*|q₂| := mul_le_mul hh₂ hq₂ hQ.le hh₂p.le
  have hbound : H*Q*|2*d+q₁-q₂| ≤ δ*H*Q^2+R*D*(2*Q+D) := by
    calc
      _ ≤ h₂*|q₂| * |2*d+q₁-q₂| :=
        mul_le_mul_of_nonneg_right hden (abs_nonneg _)
      _ = |h₂*q₂*(q₁+2*d-q₂)| := by
        rw [abs_mul,abs_mul,abs_of_pos hh₂p]
        congr 2
        ring
      _ = |robertSargosReduced r q₁ q₂ h₁ h₂ d+r*d*(q₁+d)| :=
        congrArg abs (robertSargos_affine_residual_identity hlin)
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hnear hprod)
  calc
    _ ≤ (δ*H*Q^2+R*D*(2*Q+D))/(H*Q) := by
      apply (le_div_iff₀ (mul_pos hH hQ)).mpr
      nlinarith only [hbound]
    _ = _ := by field_simp

theorem robertSargos_affine_band {r q₁ q₂ h₁ h₂ d R H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hδ : δ ≤ 1) (hr : |r| ≤ R)
    (hh₁ : h₁ ∈ Set.Icc H (2*H)) (hh₂ : h₂ ∈ Set.Icc H (2*H))
    (hq₁ : |q₁| ∈ Set.Icc Q (2*Q)) (hq₂ : |q₂| ∈ Set.Icc Q (2*Q))
    (hsign : 0 < q₁*q₂)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |2*d+q₁-q₂| ≤ δ*Q+99*R*Q/H := by
  have hdisp := robertSargos_displacement_same_sign hH hQ hh₁ hh₂ hq₁ hq₂
    hsign hlin hnear
  have hd : |d| ≤ 9*Q := by nlinarith
  have hb := robertSargos_affine_band_of_displacement hH hQ hr hd hh₂.1 hq₁.2
    hq₂.1 hlin hnear
  calc
    _ ≤ δ*Q+R*(9*Q)*(2*Q+9*Q)/(H*Q) := hb
    _ = _ := by field_simp; ring

end TaoTrudgianYang2025
