import Tao2026.SmoothNumberSaddleOuterDecay
import Tao2026.SmoothNumberCEPCoarse

/-!
# The first outer-frequency shell

This module gives the first quantitative lower bound for the global cosine
loss controlling the outer Perron line.  On the physical shell from
`pi / log y` to `4*pi / (3*log y)`, every prime in the top dyadic block has
nonpositive cosine.  The coarse Chebyshev--PNT block estimate then supplies a
loss of at least `y^(-sigma) * y / (16*log y)`.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators Interval Chebyshev

namespace Tao2026

noncomputable section

theorem card_cepDyadicPrimeBlock_lower
    {y : ℕ} (hy : 4 ≤ y)
    (hlower : (3 / 4 : ℝ) * y ≤ Chebyshev.theta (y : ℝ))
    (hupper : Chebyshev.theta ((y / 2 : ℕ) : ℝ) ≤
      (5 / 4 : ℝ) * (y / 2 : ℕ)) :
    (y : ℝ) / (16 * Real.log (y : ℝ)) ≤
      ((cepDyadicPrimeBlock y).card : ℝ) := by
  have hyPos : (0 : ℝ) < y := by positivity
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hrec := one_div_eight_log_le_sum_inv_cepDyadicPrimeBlock
    hy hlower hupper
  have hterm (p : ℕ) (hp : p ∈ cepDyadicPrimeBlock y) :
      ((p : ℝ)⁻¹) ≤ 2 / (y : ℝ) := by
    have hpData := mem_cepDyadicPrimeBlock_iff.mp hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
    have hyp : (y : ℝ) / 2 ≤ p := by
      have hynat : y ≤ p * 2 := by omega
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast hynat
    calc
      ((p : ℝ)⁻¹) ≤ ((y : ℝ) / 2)⁻¹ :=
        (inv_le_inv₀ hpPos (by positivity)).2 hyp
      _ = 2 / (y : ℝ) := by field_simp
  have hsumUpper :
      (∑ p ∈ cepDyadicPrimeBlock y, ((p : ℝ)⁻¹)) ≤
        ((cepDyadicPrimeBlock y).card : ℝ) * (2 / (y : ℝ)) := by
    calc
      (∑ p ∈ cepDyadicPrimeBlock y, ((p : ℝ)⁻¹)) ≤
          ∑ _p ∈ cepDyadicPrimeBlock y, (2 / (y : ℝ)) := by
        exact Finset.sum_le_sum fun p hp => hterm p hp
      _ = ((cepDyadicPrimeBlock y).card : ℝ) * (2 / (y : ℝ)) := by
        simp
  have h := hrec.trans hsumUpper
  rw [div_le_iff₀ (mul_pos (by norm_num) hlog)] at h
  rw [div_le_iff₀ (mul_pos (by norm_num) hlog)]
  field_simp [hyPos.ne'] at h ⊢
  nlinarith

theorem y_rpow_neg_le_prime_rpow_neg_of_mem_cepDyadicPrimeBlock
    {y p : ℕ} (hp : p ∈ cepDyadicPrimeBlock y)
    {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    (y : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-sigma) := by
  have hpData := mem_cepDyadicPrimeBlock_iff.mp hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
  have hyPos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le hpData.1.pos hpData.2.2)
  rw [Real.rpow_neg hyPos.le, Real.rpow_neg hpPos.le]
  apply (inv_le_inv₀ (Real.rpow_pos_of_pos hyPos sigma)
    (Real.rpow_pos_of_pos hpPos sigma)).2
  exact Real.rpow_le_rpow hpPos.le (by exact_mod_cast hpData.2.2) hsigma

theorem one_le_cosineLossTerm_of_firstOuterShell
    {y p : ℕ} (hy : 4 ≤ y) (hp : p ∈ cepDyadicPrimeBlock y)
    {t : ℝ}
    (hlogHalf : (3 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log ((y / 2 : ℕ) : ℝ))
    (htLower : Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 4 * Real.pi / (3 * Real.log (y : ℝ))) :
    1 ≤ 1 - Real.cos (t * Real.log (p : ℝ)) := by
  have hpData := mem_cepDyadicPrimeBlock_iff.mp hp
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hhalfPos : (0 : ℝ) < ((y / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < y / 2 by omega)
  have hlogpLower : (3 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log (p : ℝ) := by
    exact hlogHalf.trans (Real.log_le_log hhalfPos
      (by exact_mod_cast (Nat.le_of_lt hpData.2.1)))
  have hlogpUpper : Real.log (p : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hpPos (by exact_mod_cast hpData.2.2)
  have htPos : 0 < t := lt_of_lt_of_le (by positivity [Real.pi_pos]) htLower
  have hphaseLower : Real.pi / 2 ≤ t * Real.log (p : ℝ) := by
    have hmul := mul_le_mul htLower hlogpLower
      (by positivity) (by positivity [Real.pi_pos])
    field_simp [hlogy.ne'] at hmul
    nlinarith [Real.pi_pos]
  have hphaseUpper : t * Real.log (p : ℝ) ≤ Real.pi + Real.pi / 2 := by
    calc
      t * Real.log (p : ℝ) ≤
          (4 * Real.pi / (3 * Real.log (y : ℝ))) *
            Real.log (y : ℝ) :=
        mul_le_mul htUpper hlogpUpper
          (Real.log_nonneg (by exact_mod_cast hpData.1.one_le))
          (by positivity [Real.pi_pos])
      _ = 4 * Real.pi / 3 := by field_simp [hlogy.ne']
      _ ≤ Real.pi + Real.pi / 2 := by nlinarith [Real.pi_pos]
  linarith [Real.cos_nonpos_of_pi_div_two_le_of_le hphaseLower hphaseUpper]

theorem firstOuterShell_cosineLoss_lower
    {y : ℕ} (hy : 4 ≤ y)
    {sigma t : ℝ} (hsigma0 : 0 ≤ sigma)
    (hlogHalf : (3 / 4 : ℝ) * Real.log (y : ℝ) ≤
      Real.log ((y / 2 : ℕ) : ℝ))
    (htLower : Real.pi / Real.log (y : ℝ) ≤ t)
    (htUpper : t ≤ 4 * Real.pi / (3 * Real.log (y : ℝ)))
    (hlower : (3 / 4 : ℝ) * y ≤ Chebyshev.theta (y : ℝ))
    (hupper : Chebyshev.theta ((y / 2 : ℕ) : ℝ) ≤
      (5 / 4 : ℝ) * (y / 2 : ℕ)) :
    (y : ℝ) ^ (-sigma) *
        ((y : ℝ) / (16 * Real.log (y : ℝ))) ≤
      smoothSaddleCosineLoss y sigma t := by
  let S := (Finset.Icc 2 y).filter Nat.Prime
  have hsubset : cepDyadicPrimeBlock y ⊆ S := by
    intro p hp
    have hpData := mem_cepDyadicPrimeBlock_iff.mp hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpData.1.two_le, hpData.2.2⟩, hpData.1⟩
  have hterm (p : ℕ) (hp : p ∈ cepDyadicPrimeBlock y) :
      (y : ℝ) ^ (-sigma) ≤
        (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
    calc
      (y : ℝ) ^ (-sigma) ≤ (p : ℝ) ^ (-sigma) :=
        y_rpow_neg_le_prime_rpow_neg_of_mem_cepDyadicPrimeBlock hp hsigma0
      _ ≤ (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
        exact le_mul_of_one_le_right (by positivity)
          (one_le_cosineLossTerm_of_firstOuterShell hy hp hlogHalf htLower htUpper)
  calc
    (y : ℝ) ^ (-sigma) *
        ((y : ℝ) / (16 * Real.log (y : ℝ))) ≤
      (y : ℝ) ^ (-sigma) * ((cepDyadicPrimeBlock y).card : ℝ) := by
        exact mul_le_mul_of_nonneg_left
          (card_cepDyadicPrimeBlock_lower hy hlower hupper) (by positivity)
    _ = ∑ _p ∈ cepDyadicPrimeBlock y, (y : ℝ) ^ (-sigma) := by
      simp
      ring
    _ ≤ ∑ p ∈ cepDyadicPrimeBlock y,
        (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
      exact Finset.sum_le_sum fun p hp => hterm p hp
    _ ≤ ∑ p ∈ S, (p : ℝ) ^ (-sigma) *
          (1 - Real.cos (t * Real.log (p : ℝ))) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun p hp hnot => mul_nonneg (by positivity)
          (by linarith [Real.cos_le_one (t * Real.log (p : ℝ))]))
    _ = smoothSaddleCosineLoss y sigma t := rfl

end

end Tao2026
