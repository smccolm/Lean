import TaoTrudgianYang2025.ContinuousThirdDerivativeSquare
import TaoTrudgianYang2025.ThirdDerivativeNormScale
import TaoTrudgianYang2025.ThirdDerivativeRpowScale

/-! The standard third-derivative test for literal finite exponential sums.

This is not the sharper Robert--Sargos Lemma 3. Its secondary term is
sqrt(N) times the inverse sixth root of the third-derivative scale.
-/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

theorem continuous_third_derivative_bound
    (F F' F'' F''' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C μ : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hF'' : ∀ x ∈ Icc A (A+N), HasDerivAt F'' (F''' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), μ ≤ F''' x)
    (hhi : ∀ x ∈ Icc A (A+N), F''' x ≤ C*μ) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤
      20*C*((N:ℝ)*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6)) := by
  obtain ⟨hR,hscale,hs,hi⟩ := third_derivative_rpow_scale hμ hμ1
  have hb := continuous_third_derivative_square_bound F F' F'' F''' A N
    hC hμ hR hscale hF hF' hF'' hlo hhi
  have hn := third_derivative_norm_of_square (Nat.cast_nonneg N)
    (zero_lt_one.trans_le hR) hC hb
  have he : (N:ℝ)/Real.sqrt (μ^(-(1:ℝ)/3)) = (N:ℝ)*μ^((1:ℝ)/6) := by
    rw [div_eq_mul_one_div,hi]
  rwa [he,hs] at hn

theorem norm_sum_fordAdditiveCharacter_neg_phase
    (F : ℝ → ℝ) (A : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (-F (A+n))‖ =
      ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ := by
  simp_rw [← conj_fordAdditiveCharacter]
  rw [← map_sum]
  exact norm_star _

theorem continuous_third_derivative_negative_bound
    (F F' F'' F''' : ℝ → ℝ) (A : ℝ) (N : ℕ) {C μ : ℝ}
    (hC : 1 ≤ C) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hF'' : ∀ x ∈ Icc A (A+N), HasDerivAt F'' (F''' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), -(C*μ) ≤ F''' x)
    (hhi : ∀ x ∈ Icc A (A+N), F''' x ≤ -μ) :
    ‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖ ≤
      20*C*((N:ℝ)*μ^((1:ℝ)/6)+Real.sqrt N*μ^(-(1:ℝ)/6)) := by
  have hb := continuous_third_derivative_bound
    (fun x => -F x) (fun x => -F' x) (fun x => -F'' x) (fun x => -F''' x)
    A N hC hμ hμ1
    (fun x hx => (hF x hx).neg)
    (fun x hx => (hF' x hx).neg)
    (fun x hx => (hF'' x hx).neg)
    (fun x hx => by linarith [hhi x hx])
    (fun x hx => by linarith [hlo x hx])
  rwa [norm_sum_fordAdditiveCharacter_neg_phase] at hb

end TaoTrudgianYang2025
