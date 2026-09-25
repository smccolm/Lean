import TaoTrudgianYang2025.ZetaReflectionScaleLimits
import TaoTrudgianYang2025.ZetaLargeValueDiscreteness

/-! Actual zeta-pattern sequences consume the uniform bound without replacing bottom by zero. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace TaoTrudgianYang2025

theorem IsZetaLargeValueBound.eventually_log_card_le {σ τ B : ℝ}
    (h : IsZetaLargeValueBound σ τ B) (P : ℕ → ZetaLargeValuePattern)
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hne : ∀ n, (P n).ordinates.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, Real.logb (P n).N ((P n).ordinates.card : ℝ) ≤ B+ε := by
  obtain ⟨C,hC,δ,hδ,hbound⟩ := h (ε/2) (by linarith)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hconst : Tendsto (fun n => Real.logb (P n).N C) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hNtop)
  filter_upwards [hNtop.eventually (eventually_ge_atTop C),
    (tendsto_order.mp hT).1 (τ-δ) (by linarith),
    (tendsto_order.mp hT).2 (τ+δ) (by linarith),
    (tendsto_order.mp hV).1 (σ-δ) (by linarith),
    (tendsto_order.mp hV).2 (σ+δ) (by linarith),
    (tendsto_order.mp hconst).2 (ε/2) (by linarith)] with n hN hTl hTu hVl hVu hsmall
  have hc := hbound (P n) hN
    ((Real.le_logb_iff_rpow_le (P n).one_lt_N (P n).T_pos).mp hTl.le)
    ((Real.logb_le_iff_le_rpow (P n).one_lt_N (P n).T_pos).mp hTu.le)
    ((Real.le_logb_iff_rpow_le (P n).one_lt_N (P n).V_pos).mp hVl.le)
    ((Real.logb_le_iff_le_rpow (P n).one_lt_N (P n).V_pos).mp hVu.le)
  have hcard : (0 : ℝ) < (P n).ordinates.card := by exact_mod_cast (hne n).card_pos
  have hp := Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) (B+ε/2)
  have hl := (Real.logb_le_logb (P n).one_lt_N hcard (mul_pos hCp hp)).mpr hc
  have hpow : Real.logb (P n).N ((P n).N^(B+ε/2)) = B+ε/2 := by
    rw [Real.logb,Real.log_rpow (zero_lt_one.trans (P n).one_lt_N)]
    field_simp [(Real.log_pos (P n).one_lt_N).ne']
  rw [Real.logb_mul hCp.ne' hp.ne',hpow] at hl
  linarith

theorem IsZetaLargeValueBound.nonneg_of_nonempty_sequence {σ τ B : ℝ}
    (h : IsZetaLargeValueBound σ τ B) (P : ℕ → ZetaLargeValuePattern)
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hne : ∀ n, (P n).ordinates.Nonempty) : 0 ≤ B := by
  by_contra hneg
  have hb : B < 0 := lt_of_not_ge hneg
  have hsmall := h.eventually_log_card_le P hNtop hT hV hne
    (show 0 < -B/2 by linarith)
  obtain ⟨n,hn⟩ := hsmall.exists
  have hc : (1 : ℝ) ≤ (P n).ordinates.card := by
    exact_mod_cast (show 1 ≤ (P n).ordinates.card from (hne n).card_pos)
  have hl := Real.logb_nonneg (P n).one_lt_N hc
  linarith

theorem zetaLargeValueExponent_nonneg_of_nonempty_sequence {σ τ : ℝ}
    (P : ℕ → ZetaLargeValuePattern)
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hne : ∀ n, (P n).ordinates.Nonempty) :
    (0 : EReal) ≤ zetaLargeValueExponent σ τ := by
  apply le_sInf
  rintro _ ⟨B,hB,rfl⟩
  change ((0 : ℝ) : EReal) ≤ (B : EReal)
  exact EReal.coe_le_coe_iff.mpr
    (IsZetaLargeValueBound.nonneg_of_nonempty_sequence hB P hNtop hT hV hne)

end TaoTrudgianYang2025
