import TaoTrudgianYang2025.SargosSymmetricSixth

/-! The assembled twelfth-power finite symmetric-differencing estimate. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargos_symmetric_twelfth_scaled (a : ℤ → ℂ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ∃ j < 2*H,
      (H:ℝ)^6*‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^12 ≤
        1492992*(M:ℝ)^6*(∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)^6+
        382205952*(M:ℝ)^11*(H:ℝ)^2*sargosSymmetricSextupleCorrelation a M H j := by
  obtain ⟨j,hj,hd⟩ := sargos_symmetric_differencing_scaled a hH hHM
  refine ⟨j,hj,?_⟩
  let E : ℝ := ∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2
  let A : ℝ := sargosPositiveCorrelation a M H j
  let Q : ℝ := sargosSymmetricSextupleCorrelation a M H j
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hA : 0 ≤ A := sargosPositiveCorrelation_nonneg a M H j
  have hpow := pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg H) (sq_nonneg ‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖)) hd 6
  have hadd := add_pow_le hE (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hA) 6
  norm_num only [Nat.reduceSub,Nat.reducePow,mul_pow] at hadd
  have h6 : A^6 ≤ 4*(M:ℝ)^5*(H:ℝ)^2*Q := sargosPositiveCorrelation_sixth a M hH j
  calc
    _ = ((H:ℝ)*‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2)^6 := by ring
    _ ≤ (6*(M:ℝ)*(E+2*A))^6 := hpow
    _ = (6*(M:ℝ))^6*(E+2*A)^6 := by ring
    _ ≤ (6*(M:ℝ))^6*(32*(E^6+64*A^6)) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ (6*(M:ℝ))^6*(32*(E^6+64*(4*(M:ℝ)^5*(H:ℝ)^2*Q))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h6 (by norm_num))
    _ = _ := by dsimp [E,Q]; ring

theorem sargos_symmetric_twelfth (a : ℤ → ℂ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ∃ j < 2*H,
      ‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^12 ≤
        1492992*((M:ℝ)/H)^6*(∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)^6+
        (382205952*(M:ℝ)^11/(H:ℝ)^4)*sargosSymmetricSextupleCorrelation a M H j := by
  obtain ⟨j,hj,h⟩ := sargos_symmetric_twelfth_scaled a hH hHM
  refine ⟨j,hj,?_⟩
  have hHpos : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  apply (mul_le_mul_iff_right₀ (pow_pos hHpos 6)).mp
  calc
    _ ≤ _ := h
    _ = _ := by field_simp

end TaoTrudgianYang2025
