import TaoTrudgianYang2025.SargosSymmetricWindow
import TaoTrudgianYang2025.SargosSmallSixthMoment

/-! Consume the actual small-alpha estimate on its symmetric central window. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosQuartic_central_small_sixth {N : ℕ} (hN : 1 ≤ N) :
    (∫ α in Icc (-(1/Real.sqrt N)) (1/Real.sqrt N),
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^6) ≤
      89690996736*(1+Real.log N)^5 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply (sargosQuartic_central_power_le_positive N 6 (by positivity) (by positivity)).trans
  calc
    _ ≤ 2*(∫ α in Icc (0 : ℝ) (1/Real.sqrt N),
        ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
          (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) :=
      mul_le_mul_of_nonneg_left (sargosQuartic_fixed_power_le_maximal N 6 (fun _ => 1)
        0 (1/Real.sqrt N) _ _) (by norm_num)
    _ ≤ 2*(44845498368*(1+Real.log N)^5) :=
      mul_le_mul_of_nonneg_left (sargosQuartic_small_sixth_moment hN) (by norm_num)
    _ = _ := by ring

theorem sargosQuartic_central_small_sixth_source {N : ℕ} (hN : 2 ≤ N) :
    (∫ α in Icc (-(1/Real.sqrt N)) (1/Real.sqrt N),
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^6) ≤
      (89690996736*(1+1/Real.log 2)^6)*(Real.log N)^6 := by
  have hp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  apply (sargosQuartic_central_power_le_positive N 6 (by positivity) (by positivity)).trans
  calc
    _ ≤ 2*(∫ α in Icc (0 : ℝ) (1/Real.sqrt N),
        ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
          (sargosQuarticPrefixMaximum N (fun _ => 1) α γ)^6) :=
      mul_le_mul_of_nonneg_left (sargosQuartic_fixed_power_le_maximal N 6 (fun _ => 1)
        0 (1/Real.sqrt N) _ _) (by norm_num)
    _ ≤ 2*((44845498368*(1+1/Real.log 2)^6)*(Real.log N)^6) :=
      mul_le_mul_of_nonneg_left (sargosQuartic_small_sixth_moment_source hN) (by norm_num)
    _ = _ := by ring

end TaoTrudgianYang2025

