import TaoTrudgianYang2025.BetaSourceChartBound
import TaoTrudgianYang2025.PointMeanLemmaThreeEdges

/-!
# Physical power-window transfer for each fixed dual chart

The original source length is allowed a half-sized exponent window.
For every sufficiently large original T, the exact dual length A*T/N
then lies in the requested window around exponent alpha at parameter k*T.
No logarithmic exponent is introduced independently of N and T.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology

namespace TaoTrudgianYang2025

theorem eventually_fixed_multiple_ge {k : ℝ} (hk : 0 < k) (C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C ≤ k*T := by
  filter_upwards [eventually_ge_atTop (C/k)] with T hT
  simpa only [mul_comm] using (div_le_iff₀ hk).mp hT

theorem eventually_reflected_power_windows {A k δ : ℝ}
    (hA : 0 < A) (hk : 0 < k) (hδ : 0 < δ) (α : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℝ, 0 < N →
      T^(1-α-δ/2) ≤ N → N ≤ T^(1-α+δ/2) →
      (k*T)^(α-δ) ≤ A*T/N ∧ A*T/N ≤ (k*T)^(α+δ) := by
  have hlower := eventually_const_mul_rpow_le_rpow
    (D := k^(α-δ)/A) (a := 1-δ/2) (b := 1) (by linarith)
  have hupper := eventually_const_mul_rpow_le_rpow
    (D := A/k^(α+δ)) (a := 1) (b := 1+δ/2) (by linarith)
  filter_upwards [hlower,hupper,eventually_gt_atTop (0 : ℝ)] with T hlo hhi hT
  intro N hN hlow hhigh
  have hklo : 0 < k^(α-δ) := Real.rpow_pos_of_pos hk _
  have hkhi : 0 < k^(α+δ) := Real.rpow_pos_of_pos hk _
  have hleft : k^(α-δ)*T^(1-δ/2) ≤ A*T := by
    have hh := mul_le_mul_of_nonneg_left hlo hA.le
    rw [Real.rpow_one] at hh
    convert hh using 1
    field_simp
  have hright : A*T ≤ k^(α+δ)*T^(1+δ/2) := by
    have hh := mul_le_mul_of_nonneg_left hhi hkhi.le
    rw [Real.rpow_one] at hh
    convert hh using 1
    field_simp
  constructor
  · apply (le_div_iff₀ hN).mpr
    calc
      (k*T)^(α-δ)*N ≤ (k*T)^(α-δ)*T^(1-α+δ/2) :=
        mul_le_mul_of_nonneg_left hhigh (Real.rpow_nonneg (mul_pos hk hT).le _)
      _ = k^(α-δ)*T^(1-δ/2) := by
        rw [Real.mul_rpow hk.le hT.le, mul_assoc,← Real.rpow_add hT]
        congr 2
        ring
      _ ≤ A*T := hleft
  · apply (div_le_iff₀ hN).mpr
    calc
      A*T ≤ k^(α+δ)*T^(1+δ/2) := hright
      _ = (k*T)^(α+δ)*T^(1-α-δ/2) := by
        rw [Real.mul_rpow hk.le hT.le,mul_assoc,← Real.rpow_add hT]
        congr 2
        ring
      _ ≤ (k*T)^(α+δ)*N :=
        mul_le_mul_of_nonneg_left hlow (Real.rpow_nonneg (mul_pos hk hT).le _)

theorem eventually_modelPhaseDual_power_windows {σ A δ : ℝ}
    (hA : 0 < A) (hδ : 0 < δ) (α C : ℝ) :
    ∀ᶠ T : ℝ in atTop, C ≤ modelPhaseDualParameter σ A T ∧
      ∀ N : ℝ, 0 < N →
        T^(1-α-δ/2) ≤ N → N ≤ T^(1-α+δ/2) →
        (modelPhaseDualParameter σ A T)^(α-δ) ≤ modelPhaseDualScale A T N ∧
        modelPhaseDualScale A T N ≤ (modelPhaseDualParameter σ A T)^(α+δ) := by
  have hk : 0 < A^(1-σ⁻¹) := Real.rpow_pos_of_pos hA _
  filter_upwards [eventually_fixed_multiple_ge hk C,
    eventually_reflected_power_windows hA hk hδ α] with T hTC hwindow
  exact ⟨hTC,hwindow⟩

end TaoTrudgianYang2025
