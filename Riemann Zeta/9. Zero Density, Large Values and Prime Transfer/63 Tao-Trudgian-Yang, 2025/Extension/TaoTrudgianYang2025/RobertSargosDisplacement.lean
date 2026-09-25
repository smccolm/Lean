import TaoTrudgianYang2025.RobertSargosFourthGeometry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Quantitative geometry of the literal Robert--Sargos counting system. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargosReduced_neg (r q₁ q₂ h₁ h₂ d : ℝ) :
    robertSargosReduced r (-q₁) (-q₂) h₁ h₂ (-d) =
      robertSargosReduced r q₁ q₂ h₁ h₂ d := by
  unfold robertSargosReduced
  ring

theorem robertSargos_displacement_positive {r q₁ q₂ h₁ h₂ d H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q)
    (hh₁ : h₁ ∈ Set.Icc H (2*H)) (hh₂ : h₂ ∈ Set.Icc H (2*H))
    (hq₁ : q₁ ∈ Set.Icc Q (2*Q)) (hq₂ : q₂ ∈ Set.Icc Q (2*Q))
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |d| ≤ (δ+8)*Q := by
  have hhp₁ : 0 ≤ h₁ := hH.le.trans hh₁.1
  have hhp₂ : 0 ≤ h₂ := hH.le.trans hh₂.1
  have hqp₁ : 0 ≤ q₁ := hQ.le.trans hq₁.1
  have hqp₂ : 0 ≤ q₂ := hQ.le.trans hq₂.1
  have hb₁ : 0 ≤ h₁*q₁^2 ∧ h₁*q₁^2 ≤ 8*H*Q^2 := by
    constructor
    · positivity
    · have hs := sq_le_sq₀ hqp₁ (by positivity : 0 ≤ 2*Q) |>.mpr hq₁.2
      have hm := mul_le_mul hh₁.2 hs (sq_nonneg q₁) (by positivity : 0 ≤ 2*H)
      nlinarith only [hm]
  have hb₂ : 0 ≤ h₂*q₂^2 ∧ h₂*q₂^2 ≤ 8*H*Q^2 := by
    constructor
    · positivity
    · have hs := sq_le_sq₀ hqp₂ (by positivity : 0 ≤ 2*Q) |>.mpr hq₂.2
      have hm := mul_le_mul hh₂.2 hs (sq_nonneg q₂) (by positivity : 0 ≤ 2*H)
      nlinarith only [hm]
  have htail : |h₁*q₁^2-h₂*q₂^2| ≤ 8*H*Q^2 := by
    apply abs_le.mpr
    constructor <;> linarith [hb₁.1,hb₁.2,hb₂.1,hb₂.2]
  have hsum : H*Q ≤ h₁*q₁+h₂*q₂ := by
    have hm := mul_le_mul hh₁.1 hq₁.1 hQ.le hhp₁
    nlinarith [mul_nonneg hhp₂ hqp₂]
  have hspos : 0 ≤ h₁*q₁+h₂*q₂ := by positivity
  have hprod : (h₁*q₁+h₂*q₂)*|d| ≤ (δ+8)*H*Q^2 := by
    calc
      _ = |(h₁*q₁+h₂*q₂)*d| := by rw [abs_mul,abs_of_nonneg hspos]
      _ = |robertSargosReduced r q₁ q₂ h₁ h₂ d-(h₁*q₁^2-h₂*q₂^2)| := by
        rw [robertSargos_reduced_symmetric hlin]
        congr 1
        ring
      _ ≤ |robertSargosReduced r q₁ q₂ h₁ h₂ d|+|h₁*q₁^2-h₂*q₂^2| :=
        abs_sub _ _
      _ ≤ _ := by nlinarith only [hnear,htail]
  apply (mul_le_mul_iff_left₀ (mul_pos hH hQ)).mp
  calc
    |d| * (H*Q) ≤ (h₁*q₁+h₂*q₂)*|d| := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hsum (abs_nonneg d)
    _ ≤ (δ+8)*H*Q^2 := hprod
    _ = ((δ+8)*Q)*(H*Q) := by ring

theorem robertSargos_displacement_same_sign {r q₁ q₂ h₁ h₂ d H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q)
    (hh₁ : h₁ ∈ Set.Icc H (2*H)) (hh₂ : h₂ ∈ Set.Icc H (2*H))
    (hq₁ : |q₁| ∈ Set.Icc Q (2*Q)) (hq₂ : |q₂| ∈ Set.Icc Q (2*Q))
    (hsign : 0 < q₁*q₂)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |d| ≤ (δ+8)*Q := by
  rcases mul_pos_iff.mp hsign with hp | hn
  · rw [abs_of_pos hp.1] at hq₁
    rw [abs_of_pos hp.2] at hq₂
    exact robertSargos_displacement_positive hH hQ hh₁ hh₂ hq₁ hq₂ hlin hnear
  · rw [abs_of_neg hn.1] at hq₁
    rw [abs_of_neg hn.2] at hq₂
    have hl : r*(-d)+h₁*(-q₁)-h₂*(-q₂) = 0 := by linarith only [hlin]
    have he : |robertSargosReduced r (-q₁) (-q₂) h₁ h₂ (-d)| ≤ δ*H*Q^2 := by
      rwa [robertSargosReduced_neg]
    simpa only [abs_neg] using
      robertSargos_displacement_positive hH hQ hh₁ hh₂ hq₁ hq₂ hl he

end TaoTrudgianYang2025
