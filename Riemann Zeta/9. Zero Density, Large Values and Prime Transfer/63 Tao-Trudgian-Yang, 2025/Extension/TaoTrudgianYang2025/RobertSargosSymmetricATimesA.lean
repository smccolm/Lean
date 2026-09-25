import TaoTrudgianYang2025.RobertSargosCorrelationSum

/-! A-times-A applied to the actual symmetric-phase array, with exact supports. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem robertSargos_symmetric_a_times_a (f : ℝ → ℝ) (M H Q R : ℕ)
    (hQ : 0 < Q) (hR : 0 < R) (hQM : Q ≤ M) (hRH : R ≤ 2*H) :
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      (8*(M:ℝ)*H/((Q:ℝ)*R))*
        ∑ q ∈ Finset.Ioo (-(Q:ℤ)) Q, ∑ r ∈ Finset.Ioo (-(R:ℤ)) R,
          (1-|(q:ℝ)|/Q)*(1-|(r:ℝ)|/R)*
            (robertSargosMixedCorrelation f M H q r).re := by
  have hs := robertSargos_source_a_times_a (robertSargosSymmetricArray f M H)
    M (2*H) Q R hQ hR hQM hRH
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      robertSargos_symmetric_array_support f M H)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hs
  rw [robertSargos_symmetric_array_sum] at hs
  simp_rw [robertSargos_symmetric_correlation_sum] at hs
  convert hs using 1
  ring

end TaoTrudgianYang2025
