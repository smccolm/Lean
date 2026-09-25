import TaoTrudgianYang2025.RobertSargosPhysicalShift

/-! The source squared small-branch estimate at the chosen physical floor scale. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_initial_floor_budget
    (M : ℕ) {C lam : ℝ} (hC : 0 ≤ C)
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192) (hM : lam^(-(8:ℝ)/13) ≤ M) :
    930*C*(Real.log (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ)/Real.log 2)*
        ((M:ℝ)^2/(⌊lam^(-(2:ℝ)/13)⌋₊:ℝ)) ≤
      1860*C*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) := by
  let H := ⌊lam^(-(2:ℝ)/13)⌋₊
  obtain ⟨hH,hHM,hhalf,_⟩ := robertSargos_physical_floor_shift M hlam hsmall hM
  have hHp : (0:ℝ) < H := by exact_mod_cast (show 0 < H by dsimp [H]; omega)
  have hHMreal : (H:ℝ) ≤ M := by dsimp only [H]; exact_mod_cast hHM
  have hlog : Real.log H ≤ Real.log M := Real.log_le_log hHp hHMreal
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogH : 0 ≤ Real.log H := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ H by dsimp [H]; omega))
  have hlogM : 0 ≤ Real.log M := hlogH.trans hlog
  have hR : 0 < lam^(-(2:ℝ)/13) := by positivity
  have hrec : 1/lam^(-(2:ℝ)/13) = lam^((2:ℝ)/13) := by
    rw [show -(2:ℝ)/13 = -((2:ℝ)/13) by ring,Real.rpow_neg hlam.le]
    simp
  have hbound : (M:ℝ)^2/(H:ℝ) ≤ 2*(M:ℝ)^2*lam^((2:ℝ)/13) := by
    have hi : 1/(H:ℝ) ≤ 2/lam^(-(2:ℝ)/13) := by
      apply (div_le_div_iff₀ hHp hR).mpr
      dsimp [H]
      linarith
    have he := mul_le_mul_of_nonneg_left hi (sq_nonneg (M:ℝ))
    rw [div_eq_mul_one_div 2,hrec] at he
    simpa only [div_eq_mul_inv,one_mul,mul_assoc,mul_comm,mul_left_comm] using he
  have hlogdiv := div_le_div_of_nonneg_right hlog hlog2.le
  have hprod := mul_le_mul hlogdiv hbound
    (by positivity : 0 ≤ (M:ℝ)^2/(H:ℝ)) (div_nonneg hlogM hlog2.le)
  have hall := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 930*C by positivity)
  dsimp [H] at hall
  convert hall using 1 <;> ring

end TaoTrudgianYang2025
