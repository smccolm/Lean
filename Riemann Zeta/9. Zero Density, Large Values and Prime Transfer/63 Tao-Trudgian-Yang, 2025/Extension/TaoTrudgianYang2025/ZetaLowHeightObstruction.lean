import TaoTrudgianYang2025.ZetaLowHeightFamily
import TaoTrudgianYang2025.ZetaGrowthBridge
import TaoTrudgianYang2025.ClassicalSecondDerivativePair
import TaoTrudgianYang2025.ExponentPairAProcess

/-!
# Low-height obstruction to the printed unrestricted growth transfer

The source add-bound(i) permits every tau>0. A coherent coefficient-one
interval gives a counterexample at sigma=3/4, tau=1/4. This does not refute
the high-height applications in the advertised zero-density theorems.
-/

noncomputable section
open Filter Topology
namespace TaoTrudgianYang2025

theorem zetaLargeValueExponent_three_quarters_quarter_ne_bot :
    zetaLargeValueExponent (3/4) (1/4) ≠ ⊥ := by
  have hex (n : ℕ) : ∃ P : ZetaLargeValuePattern,
      P.N = ((n : ℝ)+2)^4 ∧ P.T = ((n : ℝ)+2)/4 ∧
      P.V = ((n : ℝ)+2)^3/2 ∧ P.ordinates = {((n : ℝ)+2)/4} := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      exists_lowHeight_zetaPattern (n+2) (by omega)
  choose P hN hT hV hW using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    simp only [hN]
    exact (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).comp
      (tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop)
  have hlog (m : ℕ) :
      Tendsto (fun n => Real.logb (P n).N (((n : ℝ)+2)^m))
        atTop (nhds ((m : ℝ)/4)) := by
    have he (n : ℕ) : Real.logb (P n).N (((n : ℝ)+2)^m) = (m : ℝ)/4 := by
      have hn : 1 < (n : ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
      rw [hN,Real.logb,Real.log_pow,Real.log_pow]
      field_simp [(Real.log_pos hn).ne']
      norm_num
    simp only [he]
    exact tendsto_const_nhds
  have hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T)
      atTop (nhds (1/4 : ℝ)) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => (n : ℝ)+2) (fun n => (P n).T) (1/4) (1/4) (1/4)
      (fun n => (P n).one_lt_N) hNtop (fun n => by positivity)
      (by norm_num) (by norm_num)
    · intro n
      rw [hT]
      constructor <;> linarith
    · simpa only [pow_one,Nat.cast_one] using hlog 1
  have hVlog : Tendsto (fun n => Real.logb (P n).N (P n).V)
      atTop (nhds (3/4 : ℝ)) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => ((n : ℝ)+2)^3) (fun n => (P n).V) (3/4) (1/2) (1/2)
      (fun n => (P n).one_lt_N) hNtop (fun n => by positivity)
      (by norm_num) (by norm_num)
    · intro n
      rw [hV]
      constructor <;> linarith
    · simpa only [Nat.cast_ofNat] using hlog 3
  apply zetaLargeValueExponent_ne_bot_of_nonempty_family P hNtop hTlog hVlog
  intro n
  rw [hW]
  exact Finset.singleton_nonempty _

theorem zetaGrowth_half_le_one_sixth :
    zetaGrowthExponent (1/2) ≤ ((1/6 : ℝ) : EReal) := by
  convert exponentPair_half_half.aProcess.zetaGrowthExponent_le using 1 <;> norm_num

/-- A concrete contradiction to the unrestricted source implication,
using a proved zeta-growth upper bound and genuine unbounded patterns. -/
theorem zetaGrowth_unrestricted_largeValue_transfer_counterexample :
    (0 : ℝ) < 1/4 ∧ (1/2 : ℝ) ≤ 1/2 ∧ (1/2 : ℝ) ≤ 1 ∧
    ((1/2 : ℝ) : EReal)+((1/4 : ℝ) : EReal)*zetaGrowthExponent (1/2) <
      ((3/4 : ℝ) : EReal) ∧
    zetaLargeValueExponent (3/4) (1/4) ≠ ⊥ := by
  refine ⟨by norm_num,le_rfl,by norm_num,?_,
    zetaLargeValueExponent_three_quarters_quarter_ne_bot⟩
  have hmul : ((1/4 : ℝ) : EReal)*zetaGrowthExponent (1/2) ≤
      ((1/4 : ℝ) : EReal)*((1/6 : ℝ) : EReal) :=
    mul_le_mul_of_nonneg_left zetaGrowth_half_le_one_sixth (by norm_num)
  have hh : ((1/2 : ℝ) : EReal)+((1/4 : ℝ) : EReal)*zetaGrowthExponent (1/2) ≤
      ((13/24 : ℝ) : EReal) := by
    calc
      _ ≤ ((1/2 : ℝ) : EReal)+((1/4 : ℝ) : EReal)*((1/6 : ℝ) : EReal) :=
        add_le_add le_rfl hmul
      _ = _ := by rw [← EReal.coe_mul,← EReal.coe_add]; norm_num
  exact hh.trans_lt (by norm_num)

end TaoTrudgianYang2025
