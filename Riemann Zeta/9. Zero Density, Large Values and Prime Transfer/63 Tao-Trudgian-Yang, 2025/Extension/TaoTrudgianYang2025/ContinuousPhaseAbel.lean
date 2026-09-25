import TaoTrudgianYang2025.SargosSlowAbel

/-! Finite Abel summation on an arbitrary real-origin integer range. -/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

theorem norm_weighted_range_of_prefix_bound
    (w a : ℕ → ℂ) (N : ℕ) {B V : ℝ} (hB : 0 ≤ B)
    (hp : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, a j‖ ≤ B)
    (hw : ‖w (N-1)‖ ≤ 1)
    (hv : ∑ j ∈ Finset.range (N-1), ‖w (j+1)-w j‖ ≤ V) :
    ‖∑ j ∈ Finset.range N, w j*a j‖ ≤ (1+V)*B := by
  calc
    _ ≤ ‖w (N-1)‖*‖∑ j ∈ Finset.range N, a j‖+
        ∑ j ∈ Finset.range (N-1), ‖w (j+1)-w j‖*‖∑ k ∈ Finset.range (j+1), a k‖ :=
      norm_sum_mul_le_discrete_parts w a N
    _ ≤ B+∑ j ∈ Finset.range (N-1), ‖w (j+1)-w j‖*B := by
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left (hp N le_rfl) (norm_nonneg _)).trans
          (by simpa using mul_le_mul_of_nonneg_right hw hB)
      · apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hp (j+1) (by
          have := Finset.mem_range.mp hj
          omega)) (norm_nonneg _)
    _ = (1+∑ j ∈ Finset.range (N-1), ‖w (j+1)-w j‖)*B := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (add_le_add le_rfl hv) hB

theorem continuous_character_range_variation
    (u u' : ℝ → ℝ) (A : ℝ) (N : ℕ) {K : ℝ} (hK : 0 ≤ K)
    (hu : ∀ x ∈ Icc A (A+N), HasDerivAt u (u' x) x)
    (hd : ∀ x ∈ Icc A (A+N), |u' x| ≤ K) :
    (∑ j ∈ Finset.range (N-1),
      ‖fordAdditiveCharacter (u (A+(j+1))) -
        fordAdditiveCharacter (u (A+j))‖) ≤ 2*Real.pi*K*N := by
  have hb (j : ℕ) (hj : j ∈ Finset.range (N-1)) :
      ‖fordAdditiveCharacter (u (A+(j+1))) -
        fordAdditiveCharacter (u (A+j))‖ ≤ 2*Real.pi*K := by
    have hjN : (j:ℝ)+1 ≤ N := by
      exact_mod_cast (show j+1 ≤ N by have := Finset.mem_range.mp hj; omega)
    have hx : A+j ∈ Icc A (A+N) := by
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]
    have hy : A+(j+1) ∈ Icc A (A+N) := by
      constructor <;> linarith [Nat.cast_nonneg (α := ℝ) j]
    have hs := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hu x hx).hasDerivWithinAt)
      (fun x hx => by simpa only [Real.norm_eq_abs] using hd x hx)
      (convex_Icc A (A+N)) hx hy
    have hsub : A+(j+1)-(A+j) = 1 := by ring
    simp only [Real.norm_eq_abs,hsub,abs_one,mul_one] at hs
    exact (sargos_character_sub_norm_le _ _).trans
      ((mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring))
  calc
    _ ≤ ∑ _j ∈ Finset.range (N-1), 2*Real.pi*K := Finset.sum_le_sum hb
    _ = ((N-1:ℕ):ℝ)*(2*Real.pi*K) := by simp
    _ ≤ (N:ℝ)*(2*Real.pi*K) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast (Nat.sub_le N 1)) (by positivity)
    _ = _ := by ring

theorem norm_continuous_perturbed_phase_prefix
    (g u u' : ℝ → ℝ) (A : ℝ) (N : ℕ) {B K : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hg : ∀ n ≤ N, ‖∑ j ∈ Finset.range n, fordAdditiveCharacter (g (A+j))‖ ≤ B)
    (hu : ∀ x ∈ Icc A (A+N), HasDerivAt u (u' x) x)
    (hd : ∀ x ∈ Icc A (A+N), |u' x| ≤ K) :
    ‖∑ j ∈ Finset.range N, fordAdditiveCharacter (g (A+j)+u (A+j))‖ ≤
      (1+2*Real.pi*K*N)*B := by
  have he : (∑ j ∈ Finset.range N, fordAdditiveCharacter (g (A+j)+u (A+j))) =
      ∑ j ∈ Finset.range N, fordAdditiveCharacter (u (A+j))*fordAdditiveCharacter (g (A+j)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [fordAdditiveCharacter_add,mul_comm]
  rw [he]
  exact norm_weighted_range_of_prefix_bound _ _ N hB hg
    (le_of_eq (sargos_character_norm _))
    (by simpa only [Nat.cast_add,Nat.cast_one] using
      continuous_character_range_variation u u' A N hK hu hd)

end TaoTrudgianYang2025
