import RiemannZeta.GuthMaynard.HughesYoungGlobalBounds

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

example (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, 1 ≤ T →
      hughesYoungMollifierCoefficientMass T ≤
        C * T ^ ((2 + 2 * δ) / 100 : ℝ) := by
  obtain ⟨A, hA, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  let C : ℝ := A * 3 ^ (2 + 2 * δ : ℝ)
  have hC : 0 < C := mul_pos hA (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  intro T hT
  let Q := detectorCutoff T
  let S := Finset.Icc 1 (Q ^ 2)
  have hQpos : 0 < Q := by simp [Q, detectorCutoff]
  have hQreal : 0 < (Q : ℝ) := by exact_mod_cast hQpos
  have hterm : ∀ h ∈ S, ‖shortMobiusSquareCoeff T h‖ ≤
      A * ((Q : ℝ) ^ 2) ^ δ := by
    intro h hh
    have hhpos : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
    have hhQ : (h : ℝ) ≤ (Q : ℝ) ^ 2 := by
      exact_mod_cast (Finset.mem_Icc.mp hh).2
    exact (hcoeff T h hhpos).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hhQ hδ.le) hA.le)
  have hcard : (S.card : ℝ) ≤ (Q : ℝ) ^ 2 := by
    exact_mod_cast (show S.card ≤ Q ^ 2 by simp [S])
  have hsum : hughesYoungMollifierCoefficientMass T ≤
      ((Q : ℝ) ^ 2) * (A * ((Q : ℝ) ^ 2) ^ δ) := by
    unfold hughesYoungMollifierCoefficientMass
    change (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ≤ _
    calc
      _ ≤ ∑ _h ∈ S, A * ((Q : ℝ) ^ 2) ^ δ := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (A * ((Q : ℝ) ^ 2) ^ δ) := by simp
      _ ≤ ((Q : ℝ) ^ 2) * (A * ((Q : ℝ) ^ 2) ^ δ) := by gcongr
  have hpower : ((Q : ℝ) ^ 2) * (A * ((Q : ℝ) ^ 2) ^ δ) =
      A * (Q : ℝ) ^ (2 + 2 * δ : ℝ) := by
    rw [show (Q : ℝ) ^ 2 = (Q : ℝ) ^ (2 : ℝ) by
      exact (Real.rpow_natCast (Q : ℝ) 2).symm]
    rw [← Real.rpow_mul hQreal.le]
    calc
      _ = A * ((Q : ℝ) ^ (2 : ℝ) * (Q : ℝ) ^ (2 * δ : ℝ)) := by ring
      _ = A * (Q : ℝ) ^ (2 + 2 * δ : ℝ) := by
        rw [← Real.rpow_add hQreal]
  have hQbound : (Q : ℝ) ≤ 3 * T ^ (1 / 100 : ℝ) :=
    detectorCutoff_le_three_mul_rpow_one_hundredth hT
  calc
    hughesYoungMollifierCoefficientMass T ≤
        A * (Q : ℝ) ^ (2 + 2 * δ : ℝ) := hsum.trans_eq hpower
    _ ≤ A * (3 * T ^ (1 / 100 : ℝ)) ^ (2 + 2 * δ : ℝ) := by
      gcongr
    _ = C * T ^ ((2 + 2 * δ) / 100 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (Real.rpow_nonneg (zero_le_one.trans hT) _)]
      rw [← Real.rpow_mul (zero_le_one.trans hT)]
      dsimp [C]
      rw [show (1 / 100 : ℝ) * (2 + 2 * δ) = (2 + 2 * δ) / 100 by ring]
      ring

example {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ ≤
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ := by
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlogh :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ)‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hh)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hh)]
    norm_num
  have hlogk :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ)‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hk)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
    norm_num
  have hhpow : (h : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hhR (by norm_num)
  have hkpow : (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos hkR (by norm_num)
  unfold hughesYoungLocalizedStaticScalar
  simp only [norm_mul, hlogh, hlogk, norm_div, norm_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hpi : 1 / Real.pi ≤ 1 := by
    exact (div_le_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
  have hprod :
      (h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hhpow hkpow
        (Real.rpow_nonneg (by positivity) _) (by norm_num)
      _ = 1 := by norm_num
  have hall :
      (h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / Real.pi) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hprod hpi
        (by positivity) (by norm_num)
      _ = 1 := by norm_num
  calc
    _ = (‖shortMobiusSquareCoeff T h‖ *
        ‖shortMobiusSquareCoeff T k‖) *
        ((h : ℝ) ^ (-(1 / 2 : ℝ)) *
          (k : ℝ) ^ (-(1 / 2 : ℝ)) * (1 / Real.pi)) := by ring
    _ ≤ (‖shortMobiusSquareCoeff T h‖ *
        ‖shortMobiusSquareCoeff T k‖) * 1 := by
      exact mul_le_mul_of_nonneg_left hall (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := mul_one _

example {T : ℝ} {h k : ℕ} (hh : 0 < h) (hk : 0 < k) :
    ‖hughesYoungLocalizedStaticScalar T h k‖ =
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        (h : ℝ) ^ (-(1 / 2 : ℝ)) * (k : ℝ) ^ (-(1 / 2 : ℝ)) *
          (1 / Real.pi) := by
  have hlogh :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ)‖ =
        (h : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hh)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hh)]
    norm_num
  have hlogk :
      ‖hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ)‖ =
        (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [hughesYoungLogPower_eq_cpow (by exact_mod_cast hk)]
    rw [norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hk)]
    norm_num
  unfold hughesYoungLocalizedStaticScalar
  simp only [norm_mul, hlogh, hlogk, norm_div, norm_one, norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  ring

end RiemannZeta.GuthMaynard
