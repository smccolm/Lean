import GafniTao.SharpPerronLandauSetup

/-!
# Finiteness of the normalized Landau zero disk

The generic logarithmic-derivative theorem takes finiteness of its unit-disk
zero set as an explicit hypothesis.  Here that hypothesis is derived from the
actual finite zeta-zero rectangle in the frozen foundation.  No abstract
zero family is introduced.
-/

open Complex Set Metric
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

theorem sharpLandauMap_injective (t : ℝ) :
    Function.Injective (sharpLandauMap t) := by
  intro w₁ w₂ h
  have hm : ((7 / 4 : ℝ) : ℂ) * w₁ = ((7 / 4 : ℝ) : ℂ) * w₂ := by
    exact add_left_cancel (by simpa only [sharpLandauMap] using h)
  have hscale : ((7 / 4 : ℝ) : ℂ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ hscale hm

theorem sharpLandauNormalized_eq_zero_iff (t : ℝ) (w : ℂ) :
    sharpLandauNormalized t w = 0 ↔
      riemannZeta (sharpLandauMap t w) = 0 := by
  rw [sharpLandauNormalized, mul_eq_zero]
  simp only [inv_eq_zero, sharpLandauCenter_ne_zero t, false_or]

theorem sharpLandauMap_mem_zeroSet
    {T : ℝ} (hT : 8 ≤ T) {w : ℂ}
    (hw : w ∈ SetOfZeros 1 (sharpLandauNormalized T)) :
    sharpLandauMap T w ∈ zeroSet 0 (3 * T) := by
  have hwNorm : ‖w‖ ≤ 1 := hw.1
  have hzeta : riemannZeta (sharpLandauMap T w) = 0 :=
    (sharpLandauNormalized_eq_zero_iff T w).mp hw.2
  have hmapRe : (sharpLandauMap T w).re = 2 + (7 / 4 : ℝ) * w.re := by
    simp [sharpLandauMap, sharpLandauCenter]
  have hmapIm : (sharpLandauMap T w).im =
      T + 1 / 2 + (7 / 4 : ℝ) * w.im := by
    simp [sharpLandauMap, sharpLandauCenter]
  have hstrip := zeta_zero_re_mem_of_neg_one_le (by
    have hreLower : (1 / 4 : ℝ) ≤ (sharpLandauMap T w).re := by
      have hre := Complex.abs_re_le_norm w
      have hreLower := neg_abs_le w.re
      rw [hmapRe]
      nlinarith [hwNorm]
    linarith) hzeta
  have him : |(sharpLandauMap T w).im| ≤ 3 * T := by
    have himw := Complex.abs_im_le_norm w
    have himUpper : (sharpLandauMap T w).im ≤ 3 * T := by
      rw [hmapIm]
      have := le_abs_self w.im
      nlinarith
    have himLower : -(3 * T) ≤ (sharpLandauMap T w).im := by
      rw [hmapIm]
      have := neg_abs_le w.im
      nlinarith
    exact (abs_le).2 ⟨himLower, himUpper⟩
  change sharpLandauMap T w ∈
    RiemannZeta.GuthMaynard.zerosInRect 0 1 (-(3 * T)) (3 * T)
  rw [RiemannZeta.GuthMaynard.zerosInRect, Set.Finite.mem_toFinset,
    Set.mem_inter_iff]
  refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle
    0 1 (-(3 * T)) (3 * T) (sharpLandauMap T w)).2 ?_, hzeta⟩
  exact ⟨hstrip.1, hstrip.2, (abs_le.mp him).1, (abs_le.mp him).2⟩

theorem finite_sharpLandauNormalized_zeros
    {T : ℝ} (hT : 8 ≤ T) :
    (SetOfZeros 1 (sharpLandauNormalized T)).Finite := by
  let Z : Set ℂ := (zeroSet 0 (3 * T) : Finset ℂ)
  have hpre : ((sharpLandauMap T) ⁻¹' Z).Finite :=
    Set.Finite.preimage (sharpLandauMap_injective T).injOn
      (zeroSet 0 (3 * T)).finite_toSet
  exact hpre.subset (fun w hw => sharpLandauMap_mem_zeroSet hT hw)

end GafniTao
