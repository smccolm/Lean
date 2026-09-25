import TaoTrudgianYang2025.FiniteSmoothTaylor
import TaoTrudgianYang2025.RobertSargosCubicPhase

/-! Symmetric cancellation in the actual quadratic Taylor polynomial. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_quadratic_polynomial (f : ℝ → ℝ) (x h : ℝ) :
    finiteTaylorPolynomial f 2 x (x+h) =
      f x+deriv f x*h+iteratedDeriv 2 f x*h^2/2 := by
  norm_num [finiteTaylorPolynomial,taylor_within_apply,Finset.sum_range_succ,
    iteratedDerivWithin_univ,iteratedDeriv_zero,iteratedDeriv_one,smul_eq_mul]
  ring_nf

theorem abs_symmetric_linear_remainder_le
    {f : ℝ → ℝ} {a b x h B : ℝ} (hh : 0 ≤ h)
    (ha : a ≤ x-h) (hb : x+h ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 3 f y)
    (hd : ∀ y ∈ Icc a b, |iteratedDeriv 3 f y| ≤ B) :
    |robertSargosSymmetricDifference f x h-2*h*deriv f x| ≤ B*h^3/3 := by
  have hp : uIcc x (x+h) ⊆ Icc a b := by
    intro y hy
    rw [uIcc_of_le (by linarith)] at hy
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hm : uIcc x (x-h) ⊆ Icc a b := by
    intro y hy
    rw [uIcc_of_ge (by linarith)] at hy
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hplus := abs_finiteTaylorPolynomial_remainder_le_finite
    (f := f) (a := x) (x := x+h) (M := B) 2
    (fun y hy => hf y (hp hy)) (fun y hy => hd y (hp hy))
  have hminus := abs_finiteTaylorPolynomial_remainder_le_finite
    (f := f) (a := x) (x := x-h) (M := B) 2
    (fun y hy => hf y (hm hy)) (fun y hy => hd y (hm hy))
  have he :
      robertSargosSymmetricDifference f x h-2*h*deriv f x =
        (f (x+h)-finiteTaylorPolynomial f 2 x (x+h))-
          (f (x-h)-finiteTaylorPolynomial f 2 x (x-h)) := by
    rw [robertSargos_quadratic_polynomial,
      show x-h = x+(-h) by ring_nf,robertSargos_quadratic_polynomial]
    unfold robertSargosSymmetricDifference
    ring_nf
  rw [he]
  have ht := abs_sub_le (f (x+h)-finiteTaylorPolynomial f 2 x (x+h)) 0
    (f (x-h)-finiteTaylorPolynomial f 2 x (x-h))
  simp only [sub_zero,zero_sub,abs_neg] at ht
  have hdpos : x+h-x = h := by ring_nf
  have hdneg : x-h-x = -h := by ring_nf
  norm_num only [hdpos,hdneg,abs_neg,abs_of_nonneg hh,Nat.factorial] at hplus hminus
  linarith

theorem abs_symmetric_first_jet_remainder_le
    {f : ℝ → ℝ} {a b x h B : ℝ} (hh : 0 ≤ h)
    (ha : a ≤ x-h) (hb : x+h ≤ b)
    (hf : ∀ y ∈ Icc a b, ContDiffAt ℝ 4 f y)
    (hd : ∀ y ∈ Icc a b, |iteratedDeriv 4 f y| ≤ B) :
    |robertSargosSymmetricDifference (iteratedDeriv 1 f) x h -
      2*h*iteratedDeriv 2 f x| ≤ B*h^3/3 := by
  have hg : ∀ y ∈ Icc a b, ContDiffAt ℝ 3 (iteratedDeriv 1 f) y := by
    intro y hy
    exact contDiffAt_iteratedDeriv_finite (n := 3) (j := 1) (by simpa using hf y hy)
  have hgd : ∀ y ∈ Icc a b, |iteratedDeriv 3 (iteratedDeriv 1 f) y| ≤ B := by
    intro y hy
    rw [iteratedDeriv_real_comp_order]
    exact hd y hy
  simpa only [← iteratedDeriv_succ] using abs_symmetric_linear_remainder_le hh ha hb hg hgd

end TaoTrudgianYang2025
