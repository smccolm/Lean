import TaoTrudgianYang2025.BourgainCommonSlice
import GuthMaynard.LargeValuesEnergy

/-!
# Local means of the unchanged closed-support Dirichlet polynomial

Modulation places every frequency in a fixed interval of width log 2.
The existing audited finite-exponential-sum Fourier theorem then gives
a local integral plus an explicit arbitrary-order tail. No coefficient,
endpoint or sign is changed, and the modulation has unit norm.
-/

open MeasureTheory RiemannZeta.GuthMaynard Complex Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

def bourgainCenteredPolynomial (P : LargeValuePattern) (t : ℝ) : ℂ :=
  gmFiniteExpSum P.indices P.coeff (fun n => Real.log P.N-Real.log (n : ℝ)) t

theorem bourgain_centered_frequency_bound (P : LargeValuePattern) {n : ℕ}
    (hn : n ∈ P.indices) :
    |Real.log P.N-Real.log (n : ℝ)| ≤ 1 := by
  have hN : 0 < P.N := zero_lt_one.trans P.one_lt_N
  have hnp : (0 : ℝ) < n := by exact_mod_cast P.index_pos hn
  obtain ⟨hlo, hhi⟩ := (P.mem_indices_iff n).mp hn
  have hloglo := Real.log_le_log hN hlo
  have hloghi := Real.log_le_log hnp hhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hN.ne'] at hloghi
  rw [abs_of_nonpos (sub_nonpos.mpr hloglo)]
  linarith [Real.log_two_lt_d9]

/-- Exact modulation identity, including the lower dyadic endpoint. -/
theorem bourgain_centered_polynomial_identity (P : LargeValuePattern) (t : ℝ) :
    bourgainCenteredPolynomial P t =
      Complex.exp (((Real.log P.N*t : ℝ) : ℂ)*Complex.I)*
        ∑ n ∈ P.indices, P.coeff n*dirichletPhase n t := by
  unfold bourgainCenteredPolynomial gmFiniteExpSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast P.index_pos hn
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast (P.index_pos hn).ne'
  change P.coeff n*Complex.exp (((Real.log P.N-Real.log (n : ℝ))*t : ℝ)*Complex.I) =
    Complex.exp (((Real.log P.N*t : ℝ) : ℂ)*Complex.I)*
      (P.coeff n*((n : ℂ)^(-(Complex.I*(t : ℂ)))))
  rw [Complex.cpow_def_of_ne_zero hnne]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) :=
    (Complex.ofReal_log hnpos.le).symm
  rw [hlog, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem bourgain_centered_polynomial_norm (P : LargeValuePattern) (t : ℝ) :
    ‖bourgainCenteredPolynomial P t‖ =
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖ := by
  rw [bourgain_centered_polynomial_identity, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem LargeValuePattern.polynomial_norm_continuous (P : LargeValuePattern) :
    Continuous (fun t => ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖) := by
  have hc := (continuous_gmFiniteExpSum P.indices P.coeff
    (fun n => Real.log P.N-Real.log (n : ℝ))).norm
  simpa only [← bourgain_centered_polynomial_norm] using hc

theorem LargeValuePattern.coeff_mass_le_two_mul_N (P : LargeValuePattern) :
    (∑ n ∈ P.indices, ‖P.coeff n‖) ≤ 2*P.N := by
  calc
    _ ≤ ∑ _ ∈ P.indices, (1 : ℝ) :=
      Finset.sum_le_sum (fun n hn => P.coeff_one_bounded n hn)
    _ = (P.indices.card : ℝ) := by simp
    _ ≤ _ := P.indices_card_cast_le_two_mul_N

/-- The actual polynomial's local L1 mean with an explicit Schwartz tail.
The kernel and leading coefficient are independent of the pattern and scale. -/
theorem bourgain_polynomial_local_mean_add_tail (P : LargeValuePattern)
    (t H : ℝ) (hH : 1 ≤ H) (q : ℕ) (hq : 2 ≤ q) :
    ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n t‖ ≤
      (gmAffineLocalBumpFourierSup/(2*Real.pi))*
        (∫ y in Icc (t-2*Real.pi*H) (t+2*Real.pi*H),
          ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖)+
      2*P.N*gmAffineLocalBumpFourierTailConstant q hq*H^(1-(q : ℝ)) := by
  have h := norm_gmFiniteExpSum_le_localIntegral_add_tail
    P.indices P.coeff (fun n => Real.log P.N-Real.log (n : ℝ))
    (B := 1) (T := 1) (by norm_num)
    (fun n hn => by simpa only [mul_one] using bourgain_centered_frequency_bound P hn)
    t H hH q hq
  change ‖bourgainCenteredPolynomial P t‖ ≤ _ at h
  simp only [mul_one, div_one] at h
  have heq (y : ℝ) : ‖gmFiniteExpSum P.indices P.coeff
      (fun n => Real.log P.N-Real.log (n : ℝ)) y‖ =
      ‖∑ n ∈ P.indices, P.coeff n*dirichletPhase n y‖ :=
    bourgain_centered_polynomial_norm P y
  simp_rw [heq] at h
  rw [bourgain_centered_polynomial_norm] at h
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      have ht := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right P.coeff_mass_le_two_mul_N
          (gmAffineLocalBumpFourierTailConstant_pos q hq).le)
        (Real.rpow_nonneg (zero_le_one.trans hH) (1-(q : ℝ)))
      simp only [div_eq_mul_inv, one_mul]
      exact add_le_add le_rfl ht

end TaoTrudgianYang2025
