import TaoTrudgianYang2025.RobertSargosDisplacementSums

/-! The exact double gcd weight and its uniform epsilon-dependent harmonic loss. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem sum_inverse_gcd_product (J K : ℕ) :
    (∑ j ∈ Finset.Icc 1 J, ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/((j:ℝ)*(k:ℝ))) =
      (harmonic J:ℝ)*(harmonic K:ℝ) := by
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [one_div,mul_inv]

theorem exists_robertSargos_gcd_harmonic_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ R H Q : ℝ, 1 ≤ R → 1 ≤ H → 1 ≤ Q →
      (harmonic ⌊R⌋₊:ℝ)*(harmonic ⌊2*Q⌋₊:ℝ) ≤ C*(R*H*Q)^ε := by
  let η := ε/2
  let K := 1+1/η
  have hη : 0 < η := by dsimp [η]; linarith
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K^2*(2:ℝ)^η,by positivity,?_⟩
  intro R H Q hR hH hQ
  have hRp : 0 < R := by linarith
  have hHp : 0 < H := by linarith
  have hQp : 0 < Q := by linarith
  have hB : 0 < R*H*Q := by positivity
  have hRB : R ≤ R*H*Q :=
    (le_mul_of_one_le_right hRp.le hH).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ R*H) hQ)
  have hQB : Q ≤ R*H*Q := by
    have hm := mul_le_mul_of_nonneg_right
      (one_le_mul_of_one_le_of_one_le hR hH) hQp.le
    nlinarith only [hm]
  have hJ : 1 ≤ ⌊R⌋₊ := (Nat.one_le_floor_iff R).mpr hR
  have hL : 1 ≤ ⌊2*Q⌋₊ := (Nat.one_le_floor_iff (2*Q)).mpr (by linarith)
  have hJbound : (⌊R⌋₊:ℝ) ≤ R*H*Q := (Nat.floor_le hRp.le).trans hRB
  have hLbound : (⌊2*Q⌋₊:ℝ) ≤ 2*(R*H*Q) :=
    (Nat.floor_le (by positivity : 0 ≤ 2*Q)).trans
      (mul_le_mul_of_nonneg_left hQB (by norm_num))
  have hfirst : (harmonic ⌊R⌋₊:ℝ) ≤ K*(R*H*Q)^η :=
    (harmonic_le_rpow_loss η hη hJ).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hJbound hη.le) hK.le)
  have hsecond : (harmonic ⌊2*Q⌋₊:ℝ) ≤ K*(2*(R*H*Q))^η :=
    (harmonic_le_rpow_loss η hη hL).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hLbound hη.le) hK.le)
  have hsq : (R*H*Q)^η*(R*H*Q)^η = (R*H*Q)^ε := by
    rw [← Real.rpow_add hB]
    congr 1
    dsimp [η]
    ring
  calc
    _ ≤ (K*(R*H*Q)^η)*(K*(2*(R*H*Q))^η) :=
      mul_le_mul hfirst hsecond
        (by
          simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
          exact Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
    _ = K^2*(2:ℝ)^η*((R*H*Q)^η*(R*H*Q)^η) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hB.le]
      ring
    _ = _ := by rw [hsq]

end TaoTrudgianYang2025
