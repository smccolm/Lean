import Dubon2026.CoefficientShift

/-! # Translation of the actual multiplicity-weighted open-strip count -/

namespace Dubon2026

open Complex
open scoped BigOperators

theorem zerosInOpenRectangleFinset_shiftedCoefficients {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (c l u T : ℝ) :
    zerosInOpenRectangleFinset (shiftedCoefficients a c) N hN
      (by rwa [shiftedCoefficients_one]) (l + c) (u + c) T =
        (zerosInOpenRectangleFinset a N hN ha l u T).image (fun s : ℂ => s + c) := by
  classical
  ext s
  rw [mem_zerosInOpenRectangleFinset, Finset.mem_image]
  constructor
  · rintro ⟨hl, hu, ht, hz⟩
    refine ⟨s - c, ?_, sub_add_cancel _ _⟩
    rw [mem_zerosInOpenRectangleFinset]
    rw [dirichletSum_shiftedCoefficients] at hz
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
    exact ⟨by linarith, by linarith, ht, hz⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_zerosInOpenRectangleFinset] at hw
    simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero,
      dirichletSum_shiftedCoefficients, add_sub_cancel_right]
    exact ⟨by linarith [hw.1], by linarith [hw.2.1], hw.2.2⟩

theorem verticalZeroCount_shiftedCoefficients {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) (c l u T : ℝ) :
    verticalZeroCount (shiftedCoefficients a c) N hN
      (by rwa [shiftedCoefficients_one]) (l + c) (u + c) T =
        verticalZeroCount a N hN ha l u T := by
  classical
  unfold verticalZeroCount
  rw [zerosInOpenRectangleFinset_shiftedCoefficients hN ha, Finset.sum_image]
  · simp only [zeroMultiplicity_shiftedCoefficients, add_sub_cancel_right]
  · intro s _ w _ he
    exact add_right_cancel he

end Dubon2026
