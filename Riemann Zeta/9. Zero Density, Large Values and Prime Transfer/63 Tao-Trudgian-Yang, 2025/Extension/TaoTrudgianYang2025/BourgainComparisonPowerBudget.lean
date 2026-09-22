import TaoTrudgianYang2025.BourgainCoefficientLosses
import TaoTrudgianYang2025.BourgainLinkedComparison

/-!
# Physical power factors in the linked comparison

The original-height integration factor and actual bin-count loss become
explicit powers without identifying local and global height exponents.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgain_sqrt_bin_coefficient {N G α E χ b m : ℝ}
    (hN : 0 < N) (hG : 0 < G) (hm : 0 < m) (hbin : m ≤ 2*N^χ)
    (hb : N^(-α-E/2)/Real.sqrt G ≤ b) :
    N^(-α-E/2-χ/2)/Real.sqrt (2*G) ≤ b/Real.sqrt m := by
  have hroot : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hbase : 0 ≤ N^(-α-E/2)/Real.sqrt G := by positivity
  have heq : N^(-α-E/2-χ/2)/Real.sqrt (2*G) =
      (N^(-α-E/2)/Real.sqrt G)/Real.sqrt (2*N^χ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_sub hN]
    have hs : Real.sqrt (N^χ) = N^(χ/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]
      congr 1
      ring
    rw [hs]
    ring
  rw [heq]
  exact (div_le_div_of_nonneg_left hbase hroot (Real.sqrt_le_sqrt hbin)).trans
    (div_le_div_of_nonneg_right hb hroot.le)

theorem bourgain_integration_power_factor {N T τ δ η θ M D : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hη : 0 ≤ η) (hθ : 0 ≤ θ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hcap : T ≤ N^(τ+δ)) :
    M*N^η*(2*(1+2*Real.pi*N^η)*D*T^θ) ≤
      (2*M*(1+2*Real.pi)*D)*N^(2*η+(τ+δ)*θ) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hp : 1 ≤ N^η := Real.one_le_rpow hN hη
  have hr : 1+2*Real.pi*N^η ≤ (1+2*Real.pi)*N^η := by nlinarith
  have ht : T^θ ≤ N^((τ+δ)*θ) := by
    calc
      _ ≤ (N^(τ+δ))^θ := Real.rpow_le_rpow hT hcap hθ
      _ = _ := (Real.rpow_mul hNp.le _ _).symm
  calc
    _ ≤ M*N^η*(2*((1+2*Real.pi)*N^η)*D*N^((τ+δ)*θ)) := by gcongr
    _ = (2*M*(1+2*Real.pi)*D)*N^(η+η+(τ+δ)*θ) := by
      rw [Real.rpow_add hNp, Real.rpow_add hNp]
      ring
    _ = _ := by congr 2; ring

/-- Explicit slack control: all terms in the coefficient loss can be made
small by the window, logarithmic and height-slack parameters. -/
theorem bourgain_comparison_loss_small {τ ε δ η z : ℝ}
    (hε : 0 ≤ ε) (hδ : δ ≤ 1)
    (hwindow : ε ≤ z/(4*(|τ|+2)))
    (hlog : η ≤ z/4) (hheight : δ ≤ z/4) :
    bourgainComparisonLoss τ ε δ η ≤ z := by
  have hden : 0 < 4*(|τ|+2) := by positivity
  have hmul := (le_div_iff₀ hden).mp hwindow
  have ht : (τ+δ)*ε ≤ (|τ|+1)*ε :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self τ]) hε
  unfold bourgainComparisonLoss
  nlinarith

end TaoTrudgianYang2025
