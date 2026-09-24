import TaoTrudgianYang2025.ZetaDyadicAssembly
import TaoTrudgianYang2025.ZetaGrowthExponent
import TaoTrudgianYang2025.ClassicalBottomSourceThreshold

/-!
# Exponent pairs imply the source zeta growth bound

This consumes the analytic exponent-pair estimate at the logarithmic phase.
All cutoffs, weighted sums, logarithmic losses, sharp-truncation errors and
both signs of the ordinate are discharged in the public consumer.
-/

noncomputable section
open Filter
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem eventually_const_mul_zetaCutoff_successor_clog_le_rpow
    (C η : ℝ) (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᶠ t : ℝ in atTop,
      C*Nat.clog 2 (⌊sharpZetaCutoff t⌋₊+1) ≤ t^η := by
  filter_upwards [eventually_const_mul_classicalSource_two_clogs_le_rpow C η hC hη]
    with t ht
  have hfactor : (1 : ℝ) ≤ (Nat.clog 2 ⌊sharpZetaCutoff t⌋₊+1 : ℕ) := by
    exact_mod_cast (show 1 ≤ Nat.clog 2 ⌊sharpZetaCutoff t⌋₊+1 by omega)
  have hC' : C ≤ C*(Nat.clog 2 ⌊sharpZetaCutoff t⌋₊+1 : ℕ) := by
    nlinarith
  exact (mul_le_mul_of_nonneg_right hC' (Nat.cast_nonneg _)).trans ht

/-- The paper's exp-pair-mu conclusion, with the exact fixed-line
epsilon-loss semantics and no assumed zeta-growth estimate. -/
theorem ExponentPair.isZetaGrowthBound {k l : ℝ} (h : ExponentPair k l) :
    IsZetaGrowthBound (l-k) k := by
  apply isZetaGrowthBound_of_eventually_positive
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := h.zeta_sharp_sum_bound (show 0 < ε/2 by linarith)
  refine ⟨151,by norm_num,?_⟩
  filter_upwards [
    eventually_const_mul_zetaCutoff_successor_clog_le_rpow C (ε/2)
      (zero_le_one.trans hC) (by linarith),
    Filter.eventually_ge_atTop (1 : ℝ)] with t hlog ht
  have htp : 0 < t := zero_lt_one.trans_le ht
  have hσ0 : 0 ≤ l-k := by linarith [h.inTriangle.2.1,h.inTriangle.2.2.1]
  have hσ1 : l-k ≤ 1 := by linarith [h.inTriangle.1,h.inTriangle.2.2.2.1]
  have hpow : t^(ε/2)*t^(k+ε/2) = t^(k+ε) := by
    rw [← Real.rpow_add htp]
    congr 1
    ring
  have hone : 1 ≤ t^(k+ε) := Real.one_le_rpow ht (by linarith [h.inTriangle.1])
  have hsum := (hbound t ht).trans
    (mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg htp.le (k+ε/2)))
  rw [hpow] at hsum
  have htrunc := norm_zeta_le_sharp_sum_add hσ0 hσ1 ht
  linarith

theorem ExponentPair.zetaGrowthExponent_le {k l : ℝ} (h : ExponentPair k l) :
    zetaGrowthExponent (l-k) ≤ (k : EReal) :=
  zetaGrowthExponent_le_of_bound h.isZetaGrowthBound

end TaoTrudgianYang2025

