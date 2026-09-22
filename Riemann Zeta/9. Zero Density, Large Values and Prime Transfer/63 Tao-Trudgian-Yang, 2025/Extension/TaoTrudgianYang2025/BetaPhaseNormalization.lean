import TaoTrudgianYang2025.BetaLegendreCorrection

/-!
# Multiplicative phase normalization on the canonical interval

A globally smooth small correction is rescaled onto [1,2] and added to
the exact model primitive. The source definition uses within-derivatives
at both closed endpoints; these are included in the proved bridge.
-/

noncomputable section

open Set Expdb
open scoped BigOperators ContDiff

namespace TaoTrudgianYang2025

def rescaledPhaseCorrection (H : ℝ → ℝ) (s A u : ℝ) : ℝ :=
  A^(s-1) * H (A*u)

def phaseRescalingBudget (s A : ℝ) (Q : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (Q+1), |A^(s-1)| * |A|^n

theorem rescaledPhaseCorrection_contDiff {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s A : ℝ) :
    ContDiff ℝ ∞ (rescaledPhaseCorrection H s A) :=
  contDiff_const.mul (hH.comp (contDiff_const.mul contDiff_id))

theorem rescaledPhaseCorrection_iteratedDeriv {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s A u : ℝ) (n : ℕ) :
    iteratedDeriv n (rescaledPhaseCorrection H s A) u =
      A^(s-1) * A^n * iteratedDeriv n H (A*u) := by
  have hN : (n : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  unfold rescaledPhaseCorrection
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_const_mul (hH.of_le hN) A]
  simp only [mul_assoc]

theorem phaseRescalingBudget_pos (s A : ℝ) (Q : ℕ) :
    0 < phaseRescalingBudget s A Q := by
  have h := Finset.sum_nonneg (s := Finset.range (Q+1))
    (fun n _ => mul_nonneg (abs_nonneg (A^(s-1))) (pow_nonneg (abs_nonneg A) n))
  unfold phaseRescalingBudget
  linarith

theorem rescaledPhaseCorrection_uniform_bound {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s A : ℝ) {Q : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ x : ℝ, ∀ n ≤ Q, |iteratedDeriv n H x| ≤ ε)
    (u : ℝ) {n : ℕ} (hn : n ≤ Q) :
    |iteratedDeriv n (rescaledPhaseCorrection H s A) u| ≤
      phaseRescalingBudget s A Q * ε := by
  have hb : |A^(s-1)| * |A|^n ≤ phaseRescalingBudget s A Q := by
    have h := Finset.single_le_sum (s := Finset.range (Q+1))
      (fun k _ => mul_nonneg (abs_nonneg (A^(s-1))) (pow_nonneg (abs_nonneg A) k))
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn))
    unfold phaseRescalingBudget
    linarith
  rw [rescaledPhaseCorrection_iteratedDeriv hH,abs_mul,abs_mul,abs_pow]
  exact (mul_le_mul_of_nonneg_left (he (A*u) n hn)
    (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))).trans
      (mul_le_mul_of_nonneg_right hb hε)

theorem referencePlusCorrection_approximate {H : ℝ → ℝ}
    (hH : ContDiff ℝ ∞ H) (s : ℝ) (P : ℕ) {ε : ℝ}
    (he : ∀ u ∈ Icc (1 : ℝ) 2, ∀ n ≤ P, |iteratedDeriv (n+1) H u| ≤ ε) :
    IsApproximateModelPhaseFunction (fun u => referenceModelPrimitive s u + H u)
      s P ε := by
  refine ⟨fun u hu => ((referenceModelPrimitive_contDiffAt s
    (zero_lt_one.trans_le hu.1)).add hH.contDiffAt).contDiffWithinAt,?_⟩
  intro n hn u
  have hu : 0 < (u : ℝ) := zero_lt_one.trans_le u.property.1
  have hN : ((n+1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    ENat.natCast_le_of_coe_top_le_withTop le_rfl (n+1)
  have hR := (referenceModelPrimitive_contDiffAt s hu).of_le hN
  have hC : ContDiffAt ℝ (n+1) H u := hH.contDiffAt.of_le hN
  have hm : ContDiffAt ℝ n (modelPhase s) u :=
    Real.contDiffAt_rpow_const_of_ne hu.ne'
  rw [modelPhaseErrorAt,
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval (hR.add hC) u.property,
    iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_phaseInterval hm u.property,
    iteratedDeriv_fun_add hR hC,referenceModelPrimitive_iteratedDeriv s hu n,
    add_sub_cancel_left,Real.norm_eq_abs]
  exact he u u.property n hn

theorem referenceModelPrimitive_scaling_difference
    (s : ℝ) {A u v : ℝ} (hA : 0 < A) (hu : 0 < u) (hv : 0 < v) :
    A^(s-1) * (referenceModelPrimitive s (A*u) -
      referenceModelPrimitive s (A*v)) =
      referenceModelPrimitive s u - referenceModelPrimitive s v := by
  by_cases hs : s = 1
  · subst s
    simp [referenceModelPrimitive,Real.log_mul hA.ne' hu.ne',Real.log_mul hA.ne' hv.ne']
  · simp only [referenceModelPrimitive,if_neg hs,Real.mul_rpow hA.le hu.le,
      Real.mul_rpow hA.le hv.le]
    have hp : A^(s-1)*A^(1-s) = 1 := by
      rw [← Real.rpow_add hA,show s-1+(1-s) = 0 by ring,Real.rpow_zero]
    calc
      A^(s-1) * (A^(1-s)*u^(1-s)/(1-s) - A^(1-s)*v^(1-s)/(1-s)) =
        (A^(s-1)*A^(1-s))*(u^(1-s)/(1-s)-v^(1-s)/(1-s)) := by ring
      _ = _ := by rw [hp,one_mul]

end TaoTrudgianYang2025
