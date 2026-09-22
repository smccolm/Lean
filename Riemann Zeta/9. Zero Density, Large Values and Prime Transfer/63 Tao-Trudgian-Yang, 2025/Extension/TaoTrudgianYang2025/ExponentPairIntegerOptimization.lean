import TaoTrudgianYang2025.ExponentPairShiftChoice

/-! Faithful integer optimization of the source differencing estimate. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem integer_shift_optimization
    {X N M R q η C B : ℝ}
    (hN : 0 < N) (hM : 0 ≤ M) (hR : 0 < R) (hq : 0 ≤ q)
    (hRN : R ≤ N) (hη : 0 < η) (hη₁ : η ≤ 1)
    (hC : 1 ≤ C) (hB : 1 ≤ B)
    (hbalance : M*R^(q+1) = N)
    (htrivial : X^2 ≤ 9*N^2)
    (hbound : ∀ H : ℕ, 1 ≤ H → (H : ℝ) ≤ η*N →
      X^2 ≤ C*((N^2/(H : ℝ))*B+N*M*(H : ℝ)^q)) :
    X^2 ≤ (20*C/η)*(N^2/R)*B := by
  have hCpos := zero_lt_one.trans_le hC
  have hBpos := zero_lt_one.trans_le hB
  have hbase : 0 < N^2/R := by positivity
  have hproduct : 0 ≤ (N^2/R)*B := by positivity
  have hlargeC : 18/η ≤ 20*C/η :=
    div_le_div_of_nonneg_right (by linarith) hη.le
  have hlargeC' : C*(2/η+1) ≤ 20*C/η := by
    apply (le_div_iff₀ hη).mpr
    have he : C*(2/η+1)*η = C*(2+η) := by field_simp
    rw [he]
    nlinarith
  by_cases hlarge : 2 ≤ η*R
  · obtain ⟨H,hH,hHN,hlower,hupper⟩ :=
      exists_comparable_source_shift hη hη₁ hRN hlarge
    have hHpos : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
    have hinv : N^2/(H : ℝ) ≤ (2/η)*(N^2/R) := by
      calc
        _ ≤ N^2/(η*R/2) :=
          div_le_div_of_nonneg_left (sq_nonneg N) (by positivity) hlower
        _ = _ := by field_simp
    have hMR : M*R^q = N/R := by
      apply (eq_div_iff hR.ne').mpr
      calc
        _ = M*R^(q+1) := by rw [Real.rpow_add hR,Real.rpow_one]; ring
        _ = N := hbalance
    have hpower : N*M*(H : ℝ)^q ≤ N^2/R := by
      calc
        _ ≤ N*M*R^q := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hHpos.le hupper hq) (mul_nonneg hN.le hM)
        _ = N*(M*R^q) := by ring
        _ = _ := by rw [hMR]; ring
    calc
      _ ≤ C*((N^2/(H : ℝ))*B+N*M*(H : ℝ)^q) := hbound H hH hHN
      _ ≤ C*((2/η)*(N^2/R)*B+N^2/R) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_right hinv hBpos.le) hpower) hCpos.le
      _ ≤ C*(2/η+1)*((N^2/R)*B) := by
        have hh := mul_le_mul_of_nonneg_left hB hbase.le
        have hh' := mul_le_mul_of_nonneg_left hh hCpos.le
        nlinarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hlargeC' hproduct
        nlinarith
  · have hsmall : η*R ≤ 2 := le_of_not_ge hlarge
    have hinv : 9*N^2 ≤ (18/η)*(N^2/R) := by
      have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 9*N^2 by positivity)
      rw [show (18/η)*(N^2/R) = 18*N^2/(η*R) by ring]
      apply (le_div_iff₀ (mul_pos hη hR)).mpr
      nlinarith
    calc
      _ ≤ 9*N^2 := htrivial
      _ ≤ (18/η)*(N^2/R) := hinv
      _ ≤ (20*C/η)*(N^2/R) := mul_le_mul_of_nonneg_right hlargeC hbase.le
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hB

end TaoTrudgianYang2025
