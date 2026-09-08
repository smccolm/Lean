import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.MeanValueProof

open Complex Finset

namespace RiemannZeta.GuthMaynard


/--
The finite large-value counting consequence needed from the discrete mean-value
input: a uniform lower bound of size `V` at every point of a separated set
controls the cardinality of that set. The constant is absolute.
-/
def HalaszMontgomeryLemma : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) (T : ℝ) (V : ℝ) (W : Finset ℝ) (a : ℕ → ℂ),
      0 < N → 1 ≤ T → 0 < V →
      IsSeparated 1 W →
      InBaseInterval T W →
      (∀ t ∈ W, V ≤ ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖) →
      (W.card : ℝ) ≤
        C * (T + (N : ℝ)) * V^(-2 : ℝ) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2

lemma halasz_montgomery_rhs_nonneg (C : ℝ) (N : ℕ) (T V : ℝ) (a : ℕ → ℂ)
    (hC : 0 ≤ C) (hT : 0 < T) (hV : 0 < V) :
    0 ≤ C * (T + (N : ℝ)) * V^(-2 : ℝ) *
      ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := by
  have h1 : 0 ≤ T + (N : ℝ) := add_nonneg (le_of_lt hT) (Nat.cast_nonneg N)
  have h2 : 0 ≤ V^(-2 : ℝ) := Real.rpow_nonneg (le_of_lt hV) (-2)
  have h3 : 0 ≤ ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  positivity

lemma discrete_duality_cauchy_schwarz (R : ℕ) (a b : ℕ → ℝ) :
  (∑ r ∈ Ico 0 R, a r * b r)^2 ≤ (∑ r ∈ Ico 0 R, a r ^ 2) * (∑ r ∈ Ico 0 R, b r ^ 2) := by
  exact sum_mul_sq_le_sq_mul_sq (Ico 0 R) a b

theorem halasz_montgomery_lemma_of_mean_value
    (hMeanValue : MontgomeryMeanValue) : HalaszMontgomeryLemma := by
  rcases hMeanValue with ⟨C, hC, hMeanValue⟩
  refine ⟨C, hC, ?_⟩
  intro N T V W a hN hT hV hSep hTar hBound
  have h_mean := hMeanValue N T W a hN hT hSep hTar
  have h_bound_sq : ∀ t ∈ W, V^2 ≤ ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 := by
    intro t ht
    have ht_bound := hBound t ht
    have hV_nonneg : 0 ≤ V := le_of_lt hV
    nlinarith
  have h_sum_V2 : (W.card : ℝ) * V^2 ≤ ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 := by
    calc (W.card : ℝ) * V^2 = ∑ t ∈ W, V^2 := by
          simp only [sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ W, ‖∑ n ∈ Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * I)‖^2 := sum_le_sum h_bound_sq
  have h_combined :
      (W.card : ℝ) * V^2 ≤
        C * (T + (N : ℝ)) * ∑ n ∈ Ioc N (2 * N), ‖a n‖^2 :=
    le_trans h_sum_V2 h_mean
  have h_V2_inv_pos : 0 < V^(-2 : ℝ) := by
    apply Real.rpow_pos_of_pos hV
  have h_final :
      (W.card : ℝ) * V^2 * V^(-2 : ℝ) ≤
        (C * (T + (N : ℝ)) * (∑ n ∈ Ioc N (2 * N), ‖a n‖^2)) * V^(-2 : ℝ) := by
    exact mul_le_mul_of_nonneg_right h_combined (le_of_lt h_V2_inv_pos)
  have h_V2_cancel : V^2 * V^(-2 : ℝ) = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hV]
    norm_num
  rw [mul_assoc, h_V2_cancel, mul_one] at h_final
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h_final

/-- The Halász–Montgomery large-value counting estimate with its Montgomery
mean-value premise discharged by the project theorem. -/
theorem halasz_montgomery_lemma_native : HalaszMontgomeryLemma :=
  halasz_montgomery_lemma_of_mean_value montgomery_mean_value_native

end RiemannZeta.GuthMaynard
