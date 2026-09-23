import TaoTrudgianYang2025.SargosQuarticMorseInverseJetBounds
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Exact integral and integrability transport by the actual quartic inverse. -/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace TaoTrudgianYang2025

theorem sargosQuarticMorseInverse_injOn (ε r : ℝ) :
    InjOn (sargosQuarticMorseInverse ε r) (sargosQuarticMorseRange ε r) := by
  intro z hz w hw he
  have h := congrArg (sargosQuarticMorseCoordinate ε r) he
  simpa only [sargosQuarticMorseCoordinate_inverse hz,sargosQuarticMorseCoordinate_inverse hw] using h

theorem sargosQuarticMorseInverse_image {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) :
    sargosQuarticMorseInverse ε r '' sargosQuarticMorseRange ε r = Ioo 0 3 := by
  apply Subset.antisymm
  · rintro u ⟨z,hz,rfl⟩
    exact sargosQuarticMorseInverse_mem hε hr hz
  · intro u hu
    exact ⟨sargosQuarticMorseCoordinate ε r u,⟨u,hu,rfl⟩,
      sargosQuarticMorseInverse_coordinate hε hr ⟨hu.1.le,hu.2.le⟩⟩

theorem sargosQuarticMorseInverse_deriv_pos {ε r z : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3)
    (hz : z ∈ sargosQuarticMorseRange ε r) :
    0 < deriv (sargosQuarticMorseInverse ε r) z := by
  have h := (sargosQuarticMorseInverse_deriv_bounds hε hr hz).1
  linarith

theorem sargosQuartic_integral_Ioo_eq_morseIntegral {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (g : ℝ → ℂ) :
    (∫ u in Ioo (0 : ℝ) 3, g u) =
      ∫ z in sargosQuarticMorseRange ε r,
        ((deriv (sargosQuarticMorseInverse ε r) z : ℝ) : ℂ)*
          g (sargosQuarticMorseInverse ε r z) := by
  have hd : ∀ z ∈ sargosQuarticMorseRange ε r,
      HasDerivWithinAt (sargosQuarticMorseInverse ε r)
        (deriv (sargosQuarticMorseInverse ε r) z) (sargosQuarticMorseRange ε r) z :=
    fun _ hz => (sargosQuarticMorseInverse_hasStrictDerivAt hε hr hz).hasDerivAt
      |>.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hs := (sargosQuarticMorseRange_isOpen hε hr).measurableSet
  have h := integral_image_eq_integral_abs_deriv_smul hs hd
    (sargosQuarticMorseInverse_injOn ε r) g
  rw [sargosQuarticMorseInverse_image hε hr] at h
  refine h.trans (setIntegral_congr_fun hs (fun z hz => ?_))
  rw [abs_of_pos (sargosQuarticMorseInverse_deriv_pos hε hr hz),Complex.real_smul]

theorem sargosQuartic_integrableOn_Ioo_iff_morseIntegral {ε r : ℝ}
    (hε : |ε| ≤ 1/96) (hr : r ∈ Icc 0 3) (g : ℝ → ℂ) :
    IntegrableOn g (Ioo (0 : ℝ) 3) ↔
      IntegrableOn (fun z => ((deriv (sargosQuarticMorseInverse ε r) z : ℝ) : ℂ)*
        g (sargosQuarticMorseInverse ε r z)) (sargosQuarticMorseRange ε r) := by
  have hd : ∀ z ∈ sargosQuarticMorseRange ε r,
      HasDerivWithinAt (sargosQuarticMorseInverse ε r)
        (deriv (sargosQuarticMorseInverse ε r) z) (sargosQuarticMorseRange ε r) z :=
    fun _ hz => (sargosQuarticMorseInverse_hasStrictDerivAt hε hr hz).hasDerivAt
      |>.differentiableAt.hasDerivAt.hasDerivWithinAt
  have hs := (sargosQuarticMorseRange_isOpen hε hr).measurableSet
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul hs hd
    (sargosQuarticMorseInverse_injOn ε r) g
  rw [sargosQuarticMorseInverse_image hε hr] at h
  apply h.trans
  apply integrableOn_congr_fun _ hs
  intro z hz
  dsimp only
  rw [abs_of_pos (sargosQuarticMorseInverse_deriv_pos hε hr hz),Complex.real_smul]

end TaoTrudgianYang2025

