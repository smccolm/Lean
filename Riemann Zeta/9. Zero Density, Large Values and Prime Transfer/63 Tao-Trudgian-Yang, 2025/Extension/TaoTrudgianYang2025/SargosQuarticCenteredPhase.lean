import TaoTrudgianYang2025.SargosQuarticLocalRemainder

/-! The actual normalized quartic carrier centered at its own critical point. -/

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology FourierTransform

namespace TaoTrudgianYang2025

def sargosQuarticCenteredPhase (ε r u : ℝ) : ℝ :=
  sargosQuarticPhase 1 ε u-sargosQuarticSlope 1 ε r*u

def sargosQuarticCenteredMode (χ : ℝ → ℝ) (ε r T : ℝ) : ℂ :=
  ∫ u : ℝ, (χ u : ℂ)*(𝐞 (T*sargosQuarticCenteredPhase ε r u) : ℂ)

theorem sargosQuarticCenteredPhase_contDiff (ε r : ℝ) :
    ContDiff ℝ ∞ (sargosQuarticCenteredPhase ε r) :=
  (contDiff_sargosQuarticPhase 1 ε).sub (contDiff_const.mul contDiff_id)

theorem sargosQuarticCenteredPhase_hasDerivAt (ε r u : ℝ) :
    HasDerivAt (sargosQuarticCenteredPhase ε r)
      (sargosQuarticSlope 1 ε u-sargosQuarticSlope 1 ε r) u := by
  simpa only [mul_one] using (sargosQuarticPhase_hasDerivAt 1 ε u).sub
    ((hasDerivAt_id u).const_mul (sargosQuarticSlope 1 ε r))

theorem sargosQuarticCenteredPhase_normalForm {ε r u : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hu : u ∈ Icc 0 3) :
    sargosQuarticCenteredPhase ε r u =
      sargosQuarticCenteredPhase ε r r+(sargosQuarticMorseCoordinate ε r u)^2/2 := by
  have hp := (sargosQuarticMorseCoefficient_bounds hε hr hu).1
  have h := sargosQuarticMorseCoordinate_normalForm
    (by linarith : 0 ≤ sargosQuarticMorseCoefficient ε r u)
  unfold sargosQuarticCenteredPhase
  linarith

theorem sargosQuarticCenteredPhase_inverse {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (hz : z ∈ sargosQuarticMorseRange ε r) :
    sargosQuarticCenteredPhase ε r (sargosQuarticMorseInverse ε r z) =
      sargosQuarticCenteredPhase ε r r+z^2/2 := by
  have hu := sargosQuarticMorseInverse_mem hε hr hz
  rw [sargosQuarticCenteredPhase_normalForm hε hr ⟨hu.1.le,hu.2.le⟩,
    sargosQuarticMorseCoordinate_inverse hz]

theorem sargosQuarticCenteredMode_eq_morse {χ : ℝ → ℝ} {ε r : ℝ}
    (hs : tsupport χ ⊆ Ioo (0 : ℝ) 3)
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (T : ℝ) :
    sargosQuarticCenteredMode χ ε r T =
      (𝐞 (T*sargosQuarticCenteredPhase ε r r) : ℂ)*
        ∫ z : ℝ, (sargosQuarticMorseWeight χ ε r z : ℂ)*(𝐞 ((T/2)*z^2) : ℂ) := by
  rw [sargosQuarticCenteredMode,sargosQuartic_integral_eq_global_morse hs hε hr,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ sargosQuarticMorseRange ε r
  · have hp : T*sargosQuarticCenteredPhase ε r (sargosQuarticMorseInverse ε r z) =
        T*sargosQuarticCenteredPhase ε r r+(T/2)*z^2 := by
      rw [sargosQuarticCenteredPhase_inverse hε hr hz]
      ring
    rw [hp,AddChar.map_add_eq_mul,Circle.coe_mul]
    ring
  · simp only [sargosQuarticMorseWeight_zero_of_not_mem hz,Complex.ofReal_zero,zero_mul,mul_zero]

theorem sargosQuarticFourierMode_eq_centered {χ : ℝ → ℝ} {N α γ y : ℝ}
    (hN : 0 < N) (hα : 0 < α) (hy : y ∈ sargosQuarticSlopeRange N α γ) :
    sargosQuarticFourierMode χ N α γ y =
      (N : ℂ)*sargosQuarticCenteredMode χ (γ*N^2/α)
        (sargosQuarticInverseSlope N α γ y/N) (α*N^2) := by
  rw [sargosQuarticFourierMode_eq_normalized χ hN α γ y,sargosQuarticCenteredMode]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  have hp := sargosQuarticPhase_normalize hN.ne' hα.ne' γ (N*u)
  rw [mul_div_cancel_left₀ _ hN.ne'] at hp
  have hq := sargosQuartic_normalized_stationary_slope hN.ne' hα.ne' hy
  unfold sargosQuarticCenteredPhase
  rw [hq]
  congr 2
  rw [mul_sub,hp]
  field_simp

end TaoTrudgianYang2025

