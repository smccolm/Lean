import TaoTrudgianYang2025.BetaTaylorCutoffBudget

/-!
# A genuine smooth-transition consumer of Taylor loss cancellation

The transition is the existing Real.smoothTransition, with physical
width h and either orientation. Its derivative estimates are derived,
not supplied. The remaining Taylor data concern the original function.
-/

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

theorem smoothTransition_taylor_remainder_uniform_jets (Q : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (f : ℝ → ℝ) (a x h s t M : ℝ),
      0 < h → h ≤ 1 → |s| ≤ 1 → |x-a| ≤ h →
      (∀ y ∈ uIcc a x, ContDiffAt ℝ ∞ f y) →
      (∀ y ∈ uIcc a x, |iteratedDeriv (Q+1) f y| ≤ M) →
      ∀ n ≤ Q,
        |iteratedDeriv n (fun y => Real.smoothTransition (s*y/h+t)*
          (f y-finiteTaylorPolynomial f Q a y)) x| ≤ C*M := by
  obtain ⟨B,hB,hjets⟩ := smoothTransition_finite_jet_bound Q
  have hpow : 1 ≤ (2 : ℝ)^Q := one_le_pow₀ (by norm_num)
  refine ⟨(2 : ℝ)^Q*B,by nlinarith,?_⟩
  intro f a x h s t M hh hh₁ hs hx hf hb n hn
  let χ : ℝ → ℝ := fun y => Real.smoothTransition (s*y/h+t)
  have hχ : ContDiff ℝ ∞ χ := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hN : (n : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  have hχb : ∀ i ≤ n, |iteratedDeriv i χ x| ≤ B*(h⁻¹)^i := by
    intro i hi
    have he : χ = fun y => Real.smoothTransition ((s/h)*y+t) := by
      funext y
      dsimp [χ]
      congr 1
      ring
    rw [he,iteratedDeriv_smoothTransition_affine,abs_mul,abs_pow]
    have hscale : |s/h| ≤ h⁻¹ := by
      rw [abs_div,abs_of_pos hh]
      simpa only [one_div] using div_le_div_of_nonneg_right hs hh.le
    have h := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hscale i)
      (hjets ((s/h)*x+t) i (hi.trans hn)) (abs_nonneg _)
      (pow_nonneg (inv_nonneg.mpr hh.le) i)
    simpa only [mul_comm] using h
  have hrem := abs_iteratedDeriv_cutoff_taylor_remainder_le hn hh hx
    (hχ.contDiffAt.of_le hN) hf hχb hb
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb a left_mem_uIcc)
  have hsmall : h^(Q+1-n) ≤ 1 := pow_le_one₀ hh.le hh₁
  have hcoeff : 0 ≤ (2 : ℝ)^n*B*M := by positivity
  have hmono := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn
  calc
    _ ≤ (2 : ℝ)^n*B*M*h^(Q+1-n) := hrem
    _ ≤ (2 : ℝ)^n*B*M := (mul_le_mul_of_nonneg_left hsmall hcoeff).trans_eq (mul_one _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmono (zero_le_one.trans hB)) hM

end TaoTrudgianYang2025
