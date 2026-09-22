import TaoTrudgianYang2025.BetaLegendreModelCover
import TaoTrudgianYang2025.BetaStationaryPoint

/-!
# Physical dual scales and the actual stationary exponent

Canonical charts use a multiplicative scale A. Their dual length is A*T/N
and their phase parameter is A^(1-1/sigma)*T. The identities below connect
these parameters to the original critical point, including the additive
phase factor and the Fourier conjugation convention.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform

namespace TaoTrudgianYang2025

def modelPhaseDualScale (A T N : ℝ) : ℝ := A*T/N

def modelPhaseDualParameter (σ A T : ℝ) : ℝ := A^(1-σ⁻¹)*T

def modelPhaseDualOffset (F : ℝ → ℝ) (σ A w T : ℝ) : ℝ :=
  modelPhaseDualParameter σ A T * referenceModelPrimitive σ⁻¹ (w/A) -
    T * modelPhaseLegendreDual F w

theorem modelPhaseDualScale_pos {A T N : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hN : 0 < N) :
    0 < modelPhaseDualScale A T N :=
  div_pos (mul_pos hA hT) hN

theorem modelPhaseDualParameter_pos (σ : ℝ) {A T : ℝ}
    (hA : 0 < A) (hT : 0 < T) :
    0 < modelPhaseDualParameter σ A T :=
  mul_pos (Real.rpow_pos_of_pos hA _) hT

theorem modelPhaseDualScale_coordinate {A T N : ℝ}
    (hA : A ≠ 0) (hT : T ≠ 0) (hN : N ≠ 0) (r : ℝ) :
    r/modelPhaseDualScale A T N = (r*N/T)/A := by
  unfold modelPhaseDualScale
  field_simp

theorem modelPhaseDualParameter_cancel (σ : ℝ) {A : ℝ}
    (hA : 0 < A) (T : ℝ) :
    modelPhaseDualParameter σ A T * A^(σ⁻¹-1) = T := by
  have h : A^(1-σ⁻¹)*A^(σ⁻¹-1) = 1 := by
    rw [← Real.rpow_add hA,show 1-σ⁻¹+(σ⁻¹-1) = 0 by ring,Real.rpow_zero]
  unfold modelPhaseDualParameter
  calc
    A^(1-σ⁻¹)*T*A^(σ⁻¹-1) = (A^(1-σ⁻¹)*A^(σ⁻¹-1))*T := by ring
    _ = T := by rw [h,one_mul]

theorem modelPhaseDualScale_ratio (σ : ℝ) {A T N : ℝ}
    (hA : 0 < A) (hT : T ≠ 0) (hN : N ≠ 0) :
    modelPhaseDualScale A T N / modelPhaseDualParameter σ A T = A^σ⁻¹/N := by
  have hp : A^(1-σ⁻¹) ≠ 0 := (Real.rpow_pos_of_pos hA _).ne'
  have h : A^(1-σ⁻¹)*A^σ⁻¹ = A := by
    rw [← Real.rpow_add hA,show 1-σ⁻¹+σ⁻¹ = 1 by ring,Real.rpow_one]
  unfold modelPhaseDualScale modelPhaseDualParameter
  field_simp
  simpa only [one_div] using h.symm

theorem modelPhaseDualScale_le_parameter_iff (σ : ℝ) {A T N : ℝ}
    (hA : 0 < A) (hT : 0 < T) (hN : 0 < N) :
    modelPhaseDualScale A T N ≤ modelPhaseDualParameter σ A T ↔ A^σ⁻¹ ≤ N := by
  rw [← div_le_one (modelPhaseDualParameter_pos σ hA hT),
    modelPhaseDualScale_ratio σ hA hT.ne' hN.ne',div_le_one hN]

theorem one_le_modelPhaseDualScale_iff {A T N : ℝ} (hN : 0 < N) :
    1 ≤ modelPhaseDualScale A T N ↔ N ≤ A*T := by
  exact one_le_div hN

theorem modelPhaseStationaryPoint_canonical_phase
    {χ F : ℝ → ℝ} {σ A w T N r : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : 0 < r*N/T) (hχ : χ (r*N/T) = 1) :
    modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r) =
      modelPhaseDualOffset F σ A w T -
        modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N) := by
  rw [modelPhaseStationaryPoint_phase hT hN,
    modelPhaseDualScale_coordinate hA.ne' hT hN,
    canonicalLegendrePhase_agrees hA hw hv hχ]
  have h := modelPhaseDualParameter_cancel σ hA T
  unfold modelPhaseDualOffset
  rw [mul_add,← mul_assoc, h]
  ring

theorem modelPhaseStationaryPoint_canonical_fourier
    {χ F : ℝ → ℝ} {σ A w T N r : ℝ}
    (hA : 0 < A) (hw : 0 < w) (hT : T ≠ 0) (hN : N ≠ 0)
    (hv : 0 < r*N/T) (hχ : χ (r*N/T) = 1) :
    (𝐞 (modelPhaseFrequencyPhase F T N r (modelPhaseStationaryPoint F T N r)) : ℂ) =
      (𝐞 (modelPhaseDualOffset F σ A w T) : ℂ) *
        starRingEnd ℂ (𝐞 (modelPhaseDualParameter σ A T *
          canonicalLegendrePhase χ F σ A w (r/modelPhaseDualScale A T N))) := by
  rw [modelPhaseStationaryPoint_canonical_phase hA hw hT hN hv hχ,
    sub_eq_add_neg,AddChar.map_add_eq_mul,AddChar.map_neg_eq_inv,Circle.coe_mul,
    Circle.coe_inv_eq_conj]

end TaoTrudgianYang2025
