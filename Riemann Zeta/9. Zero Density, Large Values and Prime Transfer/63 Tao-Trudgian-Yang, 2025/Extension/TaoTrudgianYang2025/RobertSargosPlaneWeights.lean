import TaoTrudgianYang2025.RobertSargosPlaneCorrelation
import TaoTrudgianYang2025.DoubleShiftWeights

/-! Exact product-triangular Gram identity for the source A-times-A
argument. Individual signed correlations need not be nonnegative. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

def robertSargosWeightedCorrelations (a : ℤ → ℤ → ℂ) (M H Q R : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
    (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*robertSargosPlaneCorrelation a M H q r

theorem robertSargos_plane_weighted_gram (a : ℤ → ℤ → ℂ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) :
    (∑ x ∈ Finset.Ico (-(Q:ℤ)) M ×ˢ Finset.Ico (-(R:ℤ)) H,
      ‖∑ t ∈ Finset.range Q ×ˢ Finset.range R,
        robertSargosPaddedPlane a M H (x.1+t.1) (x.2+t.2)‖^2) =
      (Q:ℝ)*R*robertSargosWeightedCorrelations a M H Q R := by
  have hQp : 0 < (Q:ℝ) := by exact_mod_cast hQ
  have hRp : 0 < (R:ℝ) := by exact_mod_cast hR
  calc
    _ = ∑ s ∈ Finset.range Q ×ˢ Finset.range R,
        ∑ t ∈ Finset.range Q ×ˢ Finset.range R,
          robertSargosPlaneCorrelation a M H ((s.1:ℤ)-t.1) ((t.2:ℤ)-s.2) := by
      rw [robertSargos_plane_gram]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      exact robertSargos_plane_gram_term a M H Q R s t hs ht
    _ = ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
        ((Q-q.natAbs:ℕ):ℝ)*((R-r.natAbs:ℕ):ℝ)*
          robertSargosPlaneCorrelation a M H q r :=
      sum_double_shift_differences Q R (robertSargosPlaneCorrelation a M H)
    _ = _ := by
      unfold robertSargosWeightedCorrelations
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [signed_shift_weight_real hq,signed_shift_weight_real hr]
      field_simp

theorem robertSargos_weighted_correlations_nonneg (a : ℤ → ℤ → ℂ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) :
    0 ≤ robertSargosWeightedCorrelations a M H Q R := by
  have hp : 0 < (Q:ℝ)*R := by positivity
  apply nonneg_of_mul_nonneg_right _ hp
  rw [← robertSargos_plane_weighted_gram a M H Q R hQ hR]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end TaoTrudgianYang2025
