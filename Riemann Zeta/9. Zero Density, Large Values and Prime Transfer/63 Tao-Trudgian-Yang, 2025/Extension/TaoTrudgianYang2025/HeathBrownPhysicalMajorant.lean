import TaoTrudgianYang2025.HeathBrownPowerWindow

/-!
# From a derivative scale to the exact physical power majorant

The three-term source factor is monotone in the actual interval length
and reduces at lambda = c*T/N^k to the proved physical power majorant.
-/

noncomputable section

namespace TaoTrudgianYang2025

def heathBrownDerivativeMajorant (k : ℕ) (η L lambda : ℝ) : ℝ :=
  L^(1+η) * (lambda^(heathBrownDerivativeExponent k) +
    L^(-heathBrownDerivativeExponent k) +
    L^(-2*heathBrownDerivativeExponent k)*lambda^(-heathBrownInverseExponent k))

theorem heathBrownDerivativeMajorant_expand (k : ℕ) (η lambda : ℝ)
    {L : ℝ} (hL : 0 < L) :
    heathBrownDerivativeMajorant k η L lambda =
      L^(1+η)*lambda^(heathBrownDerivativeExponent k) +
      L^(1+η-heathBrownDerivativeExponent k) +
      L^(1+η-2*heathBrownDerivativeExponent k)*lambda^(-heathBrownInverseExponent k) := by
  unfold heathBrownDerivativeMajorant
  rw [show 1+η-heathBrownDerivativeExponent k =
      (1+η)+(-heathBrownDerivativeExponent k) by ring,
    show 1+η-2*heathBrownDerivativeExponent k =
      (1+η)+(-2*heathBrownDerivativeExponent k) by ring,
    Real.rpow_add hL (1+η) (-heathBrownDerivativeExponent k),
    Real.rpow_add hL (1+η) (-2*heathBrownDerivativeExponent k)]
  ring

theorem heathBrownDerivativeMajorant_mono_length {k : ℕ} (hk : 3 ≤ k)
    {η L N lambda : ℝ} (hη : 0 ≤ η) (hL : 0 < L) (hLN : L ≤ N) (hlambda : 0 < lambda) :
    heathBrownDerivativeMajorant k η L lambda ≤ heathBrownDerivativeMajorant k η N lambda := by
  have hN := hL.trans_le hLN
  rw [heathBrownDerivativeMajorant_expand k η lambda hL,
    heathBrownDerivativeMajorant_expand k η lambda hN]
  have hd := (heathBrownDerivativeExponent_bounds hk).2.2
  apply add_le_add
  · apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hL.le hLN (by linarith))
        (Real.rpow_nonneg hlambda.le _)
    · exact Real.rpow_le_rpow hL.le hLN (by linarith)
  · exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hL.le hLN (by linarith))
      (Real.rpow_nonneg hlambda.le _)

theorem heathBrownDerivativeMajorant_physical {k : ℕ} (hk : 3 ≤ k)
    {c T N : ℝ} (hc : 0 < c) (hT : 0 < T) (hN : 0 < N) (η : ℝ) :
    heathBrownDerivativeMajorant k η N (c*T/N^k) =
      N^η * (c^(heathBrownDerivativeExponent k)*T^(heathBrownDerivativeExponent k)*
        N^(1-(k : ℝ)*heathBrownDerivativeExponent k) +
        N^(1-heathBrownDerivativeExponent k) +
        c^(-heathBrownInverseExponent k)*N*T^(-heathBrownInverseExponent k)) := by
  rw [heathBrownDerivativeMajorant_expand k η _ hN]
  have h₁ := heathBrown_physical_monomial hc hT hN k η 0 (heathBrownDerivativeExponent k)
  have h₃ := heathBrown_physical_monomial hc hT hN k η
    (2*heathBrownDerivativeExponent k) (-heathBrownInverseExponent k)
  have he : 1-2*heathBrownDerivativeExponent k-(k : ℝ)*(-heathBrownInverseExponent k) = 1 := by
    have hi := heathBrownInverseExponent_identity hk
    nlinarith
  simp only [sub_zero] at h₁
  rw [he,Real.rpow_one] at h₃
  rw [h₁,h₃]
  have h₂ : N^(1+η-heathBrownDerivativeExponent k) =
      N^η*N^(1-heathBrownDerivativeExponent k) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  rw [h₂]
  ring

theorem heathBrownDerivativeMajorant_le_powerMajorant {k : ℕ} (hk : 3 ≤ k)
    {c T N : ℝ} (hc : 0 < c) (hT : 0 < T) (hN : 0 < N) (η : ℝ) :
    heathBrownDerivativeMajorant k η N (c*T/N^k) ≤
      (c^(heathBrownDerivativeExponent k)+1+c^(-heathBrownInverseExponent k))*
        heathBrownPowerMajorant k η T N := by
  rw [heathBrownDerivativeMajorant_physical hk hc hT hN η]
  unfold heathBrownPowerMajorant
  have h₁ : 0 ≤ c^(heathBrownDerivativeExponent k) := Real.rpow_nonneg hc.le _
  have h₃ : 0 ≤ c^(-heathBrownInverseExponent k) := Real.rpow_nonneg hc.le _
  have ha : 0 ≤ T^(heathBrownDerivativeExponent k)*N^(1-(k : ℝ)*heathBrownDerivativeExponent k) := by positivity
  have hb : 0 ≤ N^(1-heathBrownDerivativeExponent k) := by positivity
  have hd : 0 ≤ N*T^(-heathBrownInverseExponent k) := by positivity
  have hinner :
      c^(heathBrownDerivativeExponent k)*
          (T^(heathBrownDerivativeExponent k)*N^(1-(k : ℝ)*heathBrownDerivativeExponent k)) +
        N^(1-heathBrownDerivativeExponent k) +
        c^(-heathBrownInverseExponent k)*(N*T^(-heathBrownInverseExponent k)) ≤
      (c^(heathBrownDerivativeExponent k)+1+c^(-heathBrownInverseExponent k))*
        (T^(heathBrownDerivativeExponent k)*N^(1-(k : ℝ)*heathBrownDerivativeExponent k) +
          N^(1-heathBrownDerivativeExponent k) + N*T^(-heathBrownInverseExponent k)) := by
    nlinarith [mul_nonneg h₁ hb,mul_nonneg h₁ hd,
      mul_nonneg h₃ ha,mul_nonneg h₃ hb]
  have hm := mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg hN.le η)
  convert hm using 1 <;> ring

end TaoTrudgianYang2025
