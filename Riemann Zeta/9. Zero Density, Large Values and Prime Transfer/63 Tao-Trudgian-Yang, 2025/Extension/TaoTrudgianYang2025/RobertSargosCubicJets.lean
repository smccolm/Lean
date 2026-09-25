import TaoTrudgianYang2025.RobertSargosCubicPhase

/-! All four derivatives of the genuine cubic Taylor remainder,
under local C4 regularity and a fourth-derivative bound only. -/

noncomputable section
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem iteratedDeriv_four_cubic_polynomial (f : ℝ → ℝ) (m x : ℝ) :
    iteratedDeriv 4 (finiteTaylorPolynomial f 3 m) x = 0 := by
  have he : iteratedDeriv 3 (finiteTaylorPolynomial f 3 m) =
      fun _ => iteratedDeriv 3 f m := by
    funext y
    rw [iteratedDeriv_finiteTaylorPolynomial f m (by rfl : 3 ≤ 3)]
    simp [finiteTaylorPolynomial,taylor_within_zero_eval]
  rw [show 4 = 3+1 by rfl,iteratedDeriv_succ,he]
  exact deriv_const x _

theorem abs_iteratedDeriv_robertSargosCubicRemainder_le
    {f : ℝ → ℝ} {m y B : ℝ} {j : ℕ} (hj : j ≤ 3)
    (hf : ∀ x ∈ Set.uIcc m (m+y), ContDiffAt ℝ 4 f x)
    (hb : ∀ x ∈ Set.uIcc m (m+y), |iteratedDeriv 4 f x| ≤ B) :
    |iteratedDeriv j (robertSargosCubicRemainder f m) y| ≤ B*|y|^(4-j) := by
  change |iteratedDeriv j
    (fun z => (fun x => f x-finiteTaylorPolynomial f 3 m x) (m+z)) y| ≤ _
  rw [iteratedDeriv_comp_const_add j (fun x => f x-finiteTaylorPolynomial f 3 m x) m]
  simpa only [add_sub_cancel_left] using
    abs_iteratedDeriv_finiteTaylorPolynomial_remainder_le_finite
      (f := f) (a := m) (x := m+y) (M := B) (Q := 3) hj hf hb

theorem iteratedDeriv_four_robertSargosCubicRemainder
    {f : ℝ → ℝ} {m y : ℝ} (hf : ContDiffAt ℝ 4 f (m+y)) :
    iteratedDeriv 4 (robertSargosCubicRemainder f m) y = iteratedDeriv 4 f (m+y) := by
  change iteratedDeriv 4
    (fun z => (fun x => f x-finiteTaylorPolynomial f 3 m x) (m+z)) y = _
  rw [iteratedDeriv_comp_const_add 4 (fun x => f x-finiteTaylorPolynomial f 3 m x) m]
  dsimp only
  rw [iteratedDeriv_fun_sub hf
    ((finiteTaylorPolynomial_contDiff f 3 m).contDiffAt.of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 4)),
    iteratedDeriv_four_cubic_polynomial,sub_zero]

theorem robertSargos_cubic_remainder_radius_jets
    {f : ℝ → ℝ} {m y B L : ℝ} {j : ℕ} (hj : j ≤ 4)
    (hy : |y| ≤ L)
    (hf : ∀ x ∈ Set.uIcc m (m+y), ContDiffAt ℝ 4 f x)
    (hb : ∀ x ∈ Set.uIcc m (m+y), |iteratedDeriv 4 f x| ≤ B) :
    |iteratedDeriv j (robertSargosCubicRemainder f m) y| ≤ B*L^(4-j) := by
  by_cases hj₃ : j ≤ 3
  · have hB : 0 ≤ B := (abs_nonneg _).trans (hb m Set.left_mem_uIcc)
    exact (abs_iteratedDeriv_robertSargosCubicRemainder_le hj₃ hf hb).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy _) hB)
  · have he : j = 4 := by omega
    subst j
    rw [iteratedDeriv_four_robertSargosCubicRemainder (hf _ Set.right_mem_uIcc)]
    simpa only [Nat.sub_self,pow_zero,mul_one] using hb (m+y) Set.right_mem_uIcc

end TaoTrudgianYang2025
