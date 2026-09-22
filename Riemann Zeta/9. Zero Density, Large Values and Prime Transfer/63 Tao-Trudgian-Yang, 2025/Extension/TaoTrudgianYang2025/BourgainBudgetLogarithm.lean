import TaoTrudgianYang2025.BourgainSeparatedSelf
import TaoTrudgianYang2025.HeathBrownDoubleZeta

/-!
# The physical Heath--Brown budget in logarithmic coordinates

All three terms of the budget are retained. Its scalar exponent is the exact
frozen double-zeta maximum, with the physical height cap explicitly linked.
-/

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgainSecondBudget_pos {N T R : ℝ}
    (hN : 0 < N) (hT : 0 ≤ T) (hR : 0 < R) :
    0 < bourgainSecondBudget N T R := by
  unfold bourgainSecondBudget
  positivity

theorem bourgain_budget_at_power {N T τ r : ℝ}
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hcap : T ≤ N^τ) :
    bourgainSecondBudget N T (N^r) ≤ 3*N^(heathBrownDoubleZetaExponent τ r) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hfirst : (N^r)^2*N = N^(2*r+1) := by
    rw [← Real.rpow_mul_natCast hNp.le, Real.rpow_add hNp, Real.rpow_one]
    congr 2
    ring
  have hsecond : N^r*N^2 = N^(r+2) := by
    rw [Real.rpow_add hNp, Real.rpow_two]
  have hthird : (N^r)^(5/4 : ℝ)*T^(1/2 : ℝ)*N ≤ N^(5/4*r+1/2*τ+1) := by
    have ht : T^(1/2 : ℝ) ≤ (N^τ)^(1/2 : ℝ) :=
      Real.rpow_le_rpow hT hcap (by norm_num)
    calc
      _ ≤ (N^r)^(5/4 : ℝ)*(N^τ)^(1/2 : ℝ)*N := by gcongr
      _ = N^(r*(5/4)+τ*(1/2)+1) := by
        rw [← Real.rpow_mul hNp.le, ← Real.rpow_mul hNp.le,
          Real.rpow_add hNp, Real.rpow_add hNp, Real.rpow_one]
      _ = _ := by congr 1; ring
  have h₁ : N^(2*r+1) ≤ N^(heathBrownDoubleZetaExponent τ r) :=
    Real.rpow_le_rpow_of_exponent_le hN ((le_max_left _ _).trans (le_max_left _ _))
  have h₂ : N^(r+2) ≤ N^(heathBrownDoubleZetaExponent τ r) :=
    Real.rpow_le_rpow_of_exponent_le hN ((le_max_right _ _).trans (le_max_left _ _))
  have h₃ : N^(5/4*r+1/2*τ+1) ≤ N^(heathBrownDoubleZetaExponent τ r) :=
    Real.rpow_le_rpow_of_exponent_le hN (le_max_right _ _)
  unfold bourgainSecondBudget
  rw [hfirst, hsecond]
  linarith

/-- The argument of the logarithm is the actual positive cardinality. -/
theorem bourgain_budget_log_bound {N T R τ : ℝ}
    (hN : 1 < N) (hT : 0 ≤ T) (hR : 0 < R) (hcap : T ≤ N^τ) :
    Real.logb N (bourgainSecondBudget N T R) ≤
      Real.logb N 3+heathBrownDoubleZetaExponent τ (Real.logb N R) := by
  have hNp : 0 < N := zero_lt_one.trans hN
  have hb := bourgain_budget_at_power (r := Real.logb N R) hN.le hT hcap
  rw [Real.rpow_logb hNp hN.ne' hR] at hb
  have hlog := Real.logb_le_logb_of_le hN (bourgainSecondBudget_pos hNp hT hR) hb
  rw [Real.logb_mul (by norm_num) (Real.rpow_pos_of_pos hNp _).ne',
    Real.logb_rpow hNp hN.ne'] at hlog
  exact hlog

/-- Height slack changes the three-term maximum by at most half that slack. -/
theorem bourgain_doubleZeta_height_slack {τ r δ : ℝ} (hδ : 0 ≤ δ) :
    heathBrownDoubleZetaExponent (τ+δ) r ≤ heathBrownDoubleZetaExponent τ r+δ/2 := by
  have h₁ : 2*r+1 ≤ heathBrownDoubleZetaExponent τ r :=
    (le_max_left _ _).trans (le_max_left _ _)
  have h₂ : r+2 ≤ heathBrownDoubleZetaExponent τ r :=
    (le_max_right _ _).trans (le_max_left _ _)
  have h₃ : 5/4*r+1/2*τ+1 ≤ heathBrownDoubleZetaExponent τ r := le_max_right _ _
  unfold heathBrownDoubleZetaExponent at h₁ h₂ h₃ ⊢
  exact max_le (max_le (by linarith) (by linarith)) (by linarith)

/-- Joint continuity permits passing both actual cardinality coordinates to
limits along one common subsequence. -/
theorem bourgain_doubleZeta_exponent_continuous :
    Continuous (fun p : ℝ × ℝ => heathBrownDoubleZetaExponent p.1 p.2) := by
  unfold heathBrownDoubleZetaExponent
  fun_prop

end TaoTrudgianYang2025
