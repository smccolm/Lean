import TaoTrudgianYang2025.SargosSymmetricSupport

/-! A proved finite symmetric-differencing inequality with an actual parity-fiber witness. -/

noncomputable section

open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosPositiveCorrelation (a : ℤ → ℂ) (M H j : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (0:ℤ) M,
    ‖∑ n ∈ sargosPositiveOffsets H j,
      sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n)‖

theorem sargosPositiveCorrelation_nonneg (a : ℤ → ℂ) (M H j : ℕ) :
    0 ≤ sargosPositiveCorrelation a M H j :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem sargos_symmetric_averaging (a : ℤ → ℂ) (M H : ℕ) :
    (H:ℝ)^2*‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2 ≤
      ((M:ℝ)+2*H)*∑ j ∈ Finset.range (2*H),
        ((∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)+2*sargosPositiveCorrelation a M H j) := by
  have h := sargos_even_shift_averaging a M H
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ m ∈ Finset.Ico (-(2*(H:ℤ))) M,
        ∑ j ∈ Finset.range (2*H),
          ‖∑ n ∈ sargosSymmetricOffsets H j,
            sargosPaddedSequence a M (m+j+n)*sargosPaddedSequence a M (m+j-n)‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact sargos_even_shift_norm_sq (sargosPaddedSequence a M) H m
    _ = ∑ j ∈ Finset.range (2*H),
        ∑ m ∈ Finset.Ico (0:ℤ) M,
          ‖∑ n ∈ sargosSymmetricOffsets H j,
            sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n)‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using
        sargos_symmetric_sum_shift a M (2*H) j (Finset.mem_range.mp hj)
          (sargosSymmetricOffsets H j)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ ∑ m ∈ Finset.Ico (0:ℤ) M,
            (‖sargosPaddedSequence a M m‖^2+
              2*‖∑ n ∈ sargosPositiveOffsets H j,
                sargosPaddedSequence a M (m+n)*sargosPaddedSequence a M (m-n)‖) := by
          apply Finset.sum_le_sum
          intro m hm
          exact sargosSymmetricOffsets_norm (sargosPaddedSequence a M) H j m
        _ = _ := by
          rw [Finset.sum_add_distrib,← Finset.mul_sum,sargos_padded_diagonal]
          rfl

theorem sargos_symmetric_differencing_scaled (a : ℤ → ℂ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ∃ j < 2*H,
      (H:ℝ)*‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2 ≤
        6*M*((∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)+
          2*sargosPositiveCorrelation a M H j) := by
  obtain ⟨j,hj,hmax⟩ := (Finset.range (2*H)).exists_max_image
    (sargosPositiveCorrelation a M H) (by
      exact ⟨0,Finset.mem_range.mpr (by omega)⟩)
  refine ⟨j,Finset.mem_range.mp hj,?_⟩
  let B : ℝ := (∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)+2*sargosPositiveCorrelation a M H j
  have hB : 0 ≤ B :=
    add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (mul_nonneg (by norm_num) (sargosPositiveCorrelation_nonneg a M H j))
  have hsum :
      (∑ k ∈ Finset.range (2*H),
        ((∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)+2*sargosPositiveCorrelation a M H k)) ≤
        2*(H:ℝ)*B := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (2*H), B := by
        apply Finset.sum_le_sum
        intro k hk
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hmax k hk) (by norm_num))
      _ = _ := by simp [Nat.cast_mul]
  have hHpos : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hMH : (M:ℝ)+2*H ≤ 3*M := by
    have hHM' : (H:ℝ) ≤ M := by exact_mod_cast hHM
    linarith
  have hbound : (H:ℝ)*(H*‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2) ≤
      H*(6*M*B) := by
    calc
      _ = (H:ℝ)^2*‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2 := by ring
      _ ≤ _ := sargos_symmetric_averaging a M H
      _ ≤ ((M:ℝ)+2*H)*(2*H*B) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (3*(M:ℝ))*(2*H*B) :=
        mul_le_mul_of_nonneg_right hMH (by positivity)
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hHpos).mp hbound

theorem sargos_symmetric_differencing (a : ℤ → ℂ) {M H : ℕ}
    (hH : 1 ≤ H) (hHM : H ≤ M) :
    ∃ j < 2*H,
      ‖∑ m ∈ Finset.Ico (0:ℤ) M, a m‖^2 ≤
        (6*M/(H:ℝ))*((∑ m ∈ Finset.Ico (0:ℤ) M, ‖a m‖^2)+
          2*sargosPositiveCorrelation a M H j) := by
  obtain ⟨j,hj,h⟩ := sargos_symmetric_differencing_scaled a hH hHM
  refine ⟨j,hj,?_⟩
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < H by omega))).mpr
  nlinarith [h]

end TaoTrudgianYang2025
