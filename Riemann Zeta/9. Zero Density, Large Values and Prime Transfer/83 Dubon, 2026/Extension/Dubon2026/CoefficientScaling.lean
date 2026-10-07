import Dubon2026.DirichletZeros
import Dubon2026.JessenGeneralMass

/-! # Nonzero coefficient scaling of the actual polynomial and its Jessen measure

Multiplication by a nonzero complex scalar preserves the supported length,
analytic multiplicities and finite-height zero counts. The logarithmic potential
changes by the constant logarithm of its modulus, so its derivative measure is
unchanged. The logarithm identity is used only off the proved Haar-null zero set.
-/

namespace Dubon2026

open MeasureTheory Set

noncomputable section

theorem dirichletSum_scale (a : ℕ → ℂ) (N : ℕ) (c s : ℂ) :
    dirichletSum (fun n => c * a n) N s = c * dirichletSum a N s := by
  simp only [dirichletSum, Finset.mul_sum, mul_assoc]

theorem coefficientSupport_scale (a : ℕ → ℂ) (N : ℕ) {c : ℂ} (hc : c ≠ 0) :
    coefficientSupport (fun n => c * a n) N = coefficientSupport a N := by
  ext n
  simp only [mem_coefficientSupport, mul_ne_zero_iff]
  exact and_congr_right fun _ => and_congr_right fun _ => and_iff_right hc

theorem lastIndex_scale (a : ℕ → ℂ) (N : ℕ) {c : ℂ} (hc : c ≠ 0) :
    lastIndex (fun n => c * a n) N = lastIndex a N := by
  simp only [lastIndex, coefficientSupport_scale a N hc]

theorem zeroMultiplicity_scale (a : ℕ → ℂ) (N : ℕ) {c : ℂ} (hc : c ≠ 0) (s : ℂ) :
    zeroMultiplicity (fun n => c * a n) N s = zeroMultiplicity a N s := by
  have he : dirichletSum (fun n => c * a n) N = (fun _ : ℂ => c) * dirichletSum a N :=
    funext fun z => dirichletSum_scale a N c z
  have ho : analyticOrderAt (fun _ : ℂ => c) s = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hc)
  simp only [zeroMultiplicity, analyticOrderNatAt, he,
    analyticOrderAt_mul analyticAt_const (analyticAt_dirichletSum a N s), ho, zero_add]

theorem zerosInOpenRectangleFinset_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) (l u T : ℝ) :
    zerosInOpenRectangleFinset (fun n => c * a n) N hN (mul_ne_zero hc ha) l u T =
      zerosInOpenRectangleFinset a N hN ha l u T := by
  ext s
  simp only [mem_zerosInOpenRectangleFinset, dirichletSum_scale, mul_eq_zero,
    hc, false_or]

theorem verticalZeroCount_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) (l u T : ℝ) :
    verticalZeroCount (fun n => c * a n) N hN (mul_ne_zero hc ha) l u T =
      verticalZeroCount a N hN ha l u T := by
  simp only [verticalZeroCount, zerosInOpenRectangleFinset_scale hN ha hc,
    zeroMultiplicity_scale a N hc]

theorem bohrOnTorus_scale (a : ℕ → ℂ) (N : ℕ) (c : ℂ) (σ : ℝ) (z : PrimeTorus N) :
    bohrOnTorus (fun n => c * a n) N σ z = c * bohrOnTorus a N σ z := by
  simp only [bohrOnTorus_eq_fourier_sum, Finset.mul_sum, mul_assoc]

theorem haarLogPotential_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) (σ : ℝ) :
    haarLogPotential (fun n => c * a n) N σ = Real.log ‖c‖ + haarLogPotential a N σ := by
  unfold haarLogPotential
  calc
    _ = ∫ z, Real.log ‖c‖ + Real.log ‖bohrOnTorus a N σ z‖ ∂torusHaar N := by
      apply integral_congr_ae
      filter_upwards [bohrOnTorus_ne_zero_ae hN ha σ] with z hz
      rw [bohrOnTorus_scale, norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hc)
        (norm_ne_zero_iff.mpr hz)]
    _ = _ := by
      rw [integral_add (integrable_const _) (integrable_bohrOnTorus_log a N σ)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem jessenFunction_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    jessenFunction (fun n => c * a n) N = fun σ => Real.log ‖c‖ + jessenFunction a N σ := by
  funext σ
  rw [jessenFunction_eq_haar hN (mul_ne_zero hc ha), jessenFunction_eq_haar hN ha,
    haarLogPotential_scale hN ha hc]

theorem derivWithin_jessenFunction_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) (S : Set ℝ) (x : ℝ) :
    derivWithin (jessenFunction (fun n => c * a n) N) S x =
      derivWithin (jessenFunction a N) S x := by
  rw [jessenFunction_scale hN ha hc, derivWithin_const_add]

theorem jessenStieltjes_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    jessenStieltjes (a := fun n => c * a n) hN (mul_ne_zero hc ha) = jessenStieltjes hN ha := by
  ext x
  simp only [jessenStieltjes_apply, derivWithin_jessenFunction_scale hN ha hc]

theorem jessenMeasure_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    jessenMeasure (a := fun n => c * a n) hN (mul_ne_zero hc ha) = jessenMeasure hN ha := by
  rw [jessenMeasure, jessenStieltjes_scale hN ha hc]
  rfl

theorem scaledJessenMeasure_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    scaledJessenMeasure (a := fun n => c * a n) hN (mul_ne_zero hc ha) =
      scaledJessenMeasure hN ha := by
  simp only [scaledJessenMeasure, jessenMeasure_scale hN ha hc]

theorem normalizedJessenMeasure_scale {a : ℕ → ℂ} {N : ℕ}
    (hN : 1 ≤ N) (ha : a 1 ≠ 0) {c : ℂ} (hc : c ≠ 0) :
    normalizedJessenMeasure (a := fun n => c * a n) hN (mul_ne_zero hc ha) =
      normalizedJessenMeasure hN ha := by
  simp only [normalizedJessenMeasure, lastIndex_scale a N hc, jessenMeasure_scale hN ha hc]

end

end Dubon2026
