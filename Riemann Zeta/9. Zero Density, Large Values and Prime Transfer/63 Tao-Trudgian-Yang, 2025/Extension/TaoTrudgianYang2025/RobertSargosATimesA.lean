import TaoTrudgianYang2025.RobertSargosPlaneWeights

/-! Finite A-times-A inequality for an arbitrary actual rectangular
array, with the exact signed triangular correlations and an explicit
source-range constant. No correlation estimate is assumed. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem robertSargos_a_times_a_exact (a : ℤ → ℤ → ℂ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) :
    ‖∑ m ∈ Finset.Ico (0:ℤ) M, ∑ h ∈ Finset.Ico (0:ℤ) H, a m h‖^2 ≤
      (((M:ℝ)+Q)*((H:ℝ)+R)/((Q:ℝ)*R))*robertSargosWeightedCorrelations a M H Q R := by
  have hp : 0 < (Q:ℝ)*R := by positivity
  have ht := robertSargos_plane_averaging a M H Q R
  rw [robertSargos_plane_weighted_gram a M H Q R hQ hR] at ht
  simp only [Nat.cast_mul,Nat.cast_add] at ht
  apply (mul_le_mul_iff_right₀ (pow_pos hp 2)).mp
  calc
    _ ≤ ((M:ℝ)+Q)*((H:ℝ)+R)*
        ((Q:ℝ)*R*robertSargosWeightedCorrelations a M H Q R) := ht
    _ = _ := by
      field_simp

theorem robertSargos_a_times_a (a : ℤ → ℤ → ℂ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hQM : Q ≤ M) (hRH : R ≤ H) :
    ‖∑ m ∈ Finset.Ico (0:ℤ) M, ∑ h ∈ Finset.Ico (0:ℤ) H, a m h‖^2 ≤
      (4*(M:ℝ)*H/((Q:ℝ)*R))*robertSargosWeightedCorrelations a M H Q R := by
  apply (robertSargos_a_times_a_exact a M H Q R hQ hR).trans
  apply mul_le_mul_of_nonneg_right _
    (robertSargos_weighted_correlations_nonneg a M H Q R hQ hR)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hqm : (Q:ℝ) ≤ M := by exact_mod_cast hQM
  have hrh : (R:ℝ) ≤ H := by exact_mod_cast hRH
  calc
    ((M:ℝ)+Q)*((H:ℝ)+R) ≤ (2*(M:ℝ))*(2*(H:ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ = 4*(M:ℝ)*H := by ring

end TaoTrudgianYang2025
