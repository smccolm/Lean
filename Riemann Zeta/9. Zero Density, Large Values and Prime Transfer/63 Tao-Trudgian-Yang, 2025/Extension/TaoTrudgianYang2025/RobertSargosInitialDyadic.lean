import TaoTrudgianYang2025.RobertSargosDyadicSequence

/-! Actual dyadic selection after the initial conjugated A-process.
The selected doubled block is exactly the input of the source A-times-A theorem. -/

noncomputable section
open GafniTao
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem exists_robertSargos_weighted_dyadic (f : ℝ → ℝ) (M H : ℕ) (hH : 2 ≤ H) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖robertSargosWeightedSymmetricPhase f M H‖ ≤
        (Nat.clog 2 H:ℝ)*((M:ℝ)+‖robertSargosSymmetricSum f M k‖) := by
  obtain ⟨k,hk,hkH,hs⟩ := exists_doubled_block_weighted
    (robertSargosPhaseSequence f M) H hH
    (by simp [robertSargosPhaseSequence])
    (M:ℝ) (Nat.cast_nonneg M) (fun n _ => robertSargos_phase_sequence_norm f M n)
  rw [robertSargos_phase_sequence_weighted,
    robertSargos_phase_sequence_block f M k hk] at hs
  exact ⟨k,hk,hkH,hs⟩

theorem exists_robertSargos_initial_dyadic (f : ℝ → ℝ) (M H : ℕ)
    (hH : 2 ≤ H) (hHM : H ≤ M) :
    ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧
      ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
        (3+6*(Nat.clog 2 H:ℝ))*(M:ℝ)^2/H+
          (6*(M:ℝ)*(Nat.clog 2 H:ℝ)/H)*‖robertSargosSymmetricSum f M k‖ := by
  obtain ⟨k,hk,hkH,hs⟩ := exists_robertSargos_weighted_dyadic f M H hH
  refine ⟨k,hk,hkH,?_⟩
  calc
    _ ≤ 3*(M:ℝ)^2/H+(6*(M:ℝ)/H)*‖robertSargosWeightedSymmetricPhase f M H‖ :=
      robertSargos_initial_source_a_process_range f M H (by omega) hHM
    _ ≤ 3*(M:ℝ)^2/H+(6*(M:ℝ)/H)*
        ((Nat.clog 2 H:ℝ)*((M:ℝ)+‖robertSargosSymmetricSum f M k‖)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hs (by positivity)) _
    _ = _ := by ring

end TaoTrudgianYang2025
