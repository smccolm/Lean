import TaoTrudgianYang2025.ExponentPairAllHeights
import TaoTrudgianYang2025.BetaTwistedLogPhase

/-! The exact logarithmic model and literal imaginary-power Dirichlet sums. -/

noncomputable section
open Expdb
open scoped FourierTransform
namespace TaoTrudgianYang2025

theorem log_approximateModel (P : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    IsApproximateModelPhaseFunction Real.log 1 P δ := by
  have he : twistedLogPhase 0 = Real.log := by
    funext u
    simp [twistedLogPhase]
  rw [← he]
  exact twistedLogPhase_approximate P (c:=0) (by simpa using hδ)

theorem cpow_im_logModel_identity {n : ℕ} (hn : 0 < n)
    {N : ℝ} (hN : 0 < N) (t : ℝ) :
    (n : ℂ)^((t : ℂ)*Complex.I) =
      (𝐞 ((t/(2*Real.pi))*Real.log N) : ℂ) *
        oscillatory Real.log (t/(2*Real.pi)) N n := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnp.le).symm
  rw [Complex.cpow_def_of_ne_zero hnz, hnlog,
    oscillatory,Real.fourierChar_apply,Real.fourierChar_apply,← Complex.exp_add,
    Real.log_div hnp.ne' hN.ne']
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

theorem cpow_neg_im_eq_star (n : ℕ) (t : ℝ) :
    (n : ℂ)^(-((t : ℂ)*Complex.I)) =
      star ((n : ℂ)^((t : ℂ)*Complex.I)) := by
  have ha : (n : ℂ).arg ≠ Real.pi := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from rfl,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  simpa using Complex.cpow_conj (n : ℂ) ((t : ℂ)*Complex.I) ha

theorem norm_sum_cpow_neg_im_eq_logModel {N : ℝ} (hN : 0 < N)
    (a b : ℕ) (ha : N ≤ (a : ℝ)) (t : ℝ) :
    ‖∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))‖ =
      ‖exponentialSumAt Real.log (t/(2*Real.pi)) N a b‖ := by
  have hp : (∑ n ∈ Finset.Icc a b, (n : ℂ)^((t : ℂ)*Complex.I)) =
      (𝐞 ((t/(2*Real.pi))*Real.log N) : ℂ) *
        exponentialSumAt Real.log (t/(2*Real.pi)) N a b := by
    rw [exponentialSumAt,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hnpos : 0 < n := by
      have hna : (a : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      exact_mod_cast hN.trans_le (ha.trans hna)
    exact cpow_im_logModel_identity hnpos hN t
  have hm : (∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))) =
      star (∑ n ∈ Finset.Icc a b, (n : ℂ)^((t : ℂ)*Complex.I)) := by
    simp only [cpow_neg_im_eq_star,star_sum]
  rw [hm,norm_star,hp,norm_mul]
  simp

/-- Every analytic exponent pair bounds the literal negative-imaginary
power sum at all positive heights, including scales above the height. -/
theorem ExponentPair.logarithmic_sum_bound {k l ε : ℝ}
    (h : ExponentPair k l) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (t N : ℝ) (a b : ℕ),
      0 < t → 1 ≤ N → N ≤ (a : ℝ) → (b : ℝ) ≤ 2*N →
      ‖∑ n ∈ Finset.Icc a b, (n : ℂ)^(-((t : ℂ)*Complex.I))‖ ≤
        C*((t/N)^(k+ε)*N^(l+ε)+2*Real.pi*N/t) := by
  obtain ⟨δ,hδ,P,_hP,C,hC,hbound⟩ := h.allPositiveHeight_bound (by norm_num : (0:ℝ) < 1) hε
  refine ⟨C,hC,?_⟩
  intro t N a b ht hN ha hb
  have hNp : 0 < N := zero_lt_one.trans_le hN
  rw [norm_sum_cpow_neg_im_eq_logModel hNp a b ha t]
  have hs := hbound (t/(2*Real.pi)) N Real.log a b (by positivity) hN ha hb
    (log_approximateModel P hδ.le)
  apply hs.trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  have hr : N/(t/(2*Real.pi)) = 2*Real.pi*N/t := by field_simp
  rw [hr]
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNp.le _)
  apply Real.rpow_le_rpow (by positivity)
  · apply div_le_div_of_nonneg_right _ hNp.le
    exact div_le_self ht.le (by linarith [Real.pi_gt_three])
  · linarith [h.inTriangle.1]

end TaoTrudgianYang2025
