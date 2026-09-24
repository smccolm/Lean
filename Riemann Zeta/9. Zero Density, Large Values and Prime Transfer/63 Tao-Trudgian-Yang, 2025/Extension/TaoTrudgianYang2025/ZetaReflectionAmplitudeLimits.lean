import TaoTrudgianYang2025.ZetaReflectionScaleLimits

/-! Compact extraction of the actual reflected amplitude exponent. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
namespace TaoTrudgianYang2025

theorem ZetaLargeValuePattern.value_le_two_mul_N_of_nonempty (P : ZetaLargeValuePattern)
    (hne : P.ordinates.Nonempty) : P.V ≤ 2*P.N := by
  obtain ⟨t,ht⟩ := hne
  have hv := P.large t ht
  rw [P.polynomial_eq_active_sum] at hv
  have hb := reciprocalCompletion_phase_sum_norm_le_card P.active
    (fun n hn => ne_of_gt (P.index_pos (P.active_subset hn))) t
  have hc : (P.active.card : ℝ) ≤ P.indices.card := by
    exact_mod_cast Finset.card_le_card P.active_subset
  exact hv.trans (hb.trans (hc.trans P.indices_card_cast_le_two_mul_N))

theorem reflection_tendsto_log_value_floor (P : ℕ → ZetaLargeValuePattern)
    (err : ℕ → ℝ) {σ τ : ℝ} (he : Tendsto err atTop (nhds 0))
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ)) :
    Tendsto (fun n => Real.logb (P n).N
      ((P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n))))
      atTop (nhds (σ+τ/2-1)) := by
  have hN (n : ℕ) := zero_lt_one.trans (P n).one_lt_N
  have hself := tendsto_logb_self_of_one_lt (fun n => (P n).N) (fun n => (P n).one_lt_N)
  have hsqrt : Tendsto (fun n => Real.logb (P n).N (Real.sqrt (P n).T))
      atTop (nhds (τ/2)) := by
    simpa only [Real.sqrt_eq_rpow,div_eq_mul_inv,mul_comm,one_mul] using
      tendsto_logb_rpow (1/2) (fun n => (P n).T_pos) hT
  have hvar : Tendsto (fun n => Real.logb (P n).N ((P n).N^(err n)))
      atTop (nhds 0) := by
    have heq (n : ℕ) : Real.logb (P n).N ((P n).N^(err n)) = err n := by
      rw [Real.logb,Real.log_rpow (hN n)]
      field_simp [(Real.log_pos (P n).one_lt_N).ne']
    simpa only [heq] using he
  have hnum := tendsto_logb_mul (fun n => (P n).V_pos)
    (fun n => Real.sqrt_pos.mpr (P n).T_pos) hV hsqrt
  have hden := tendsto_logb_mul hN
    (fun n => Real.rpow_pos_of_pos (hN n) (err n)) hself hvar
  simpa only [add_zero] using tendsto_logb_div
    (fun n => mul_pos (P n).V_pos (Real.sqrt_pos.mpr (P n).T_pos))
    (fun n => mul_pos (hN n) (Real.rpow_pos_of_pos (hN n) (err n))) hnum hden

theorem exists_reflection_amplitude_subsequence (P Q : ℕ → ZetaLargeValuePattern)
    (err : ℕ → ℝ) {σ τ κ : ℝ}
    (hNtop : Tendsto (fun n => (P n).N) atTop atTop)
    (he : Tendsto err atTop (nhds 0))
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hscale : Tendsto (fun n => Real.logb (P n).N (Q n).N) atTop (nhds κ))
    (hne : ∀ n, (Q n).ordinates.Nonempty)
    (hvalue : ∀ n, (P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n)) ≤ (Q n).V) :
    ∃ v ∈ Icc (σ+τ/2-1) κ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => Real.logb (P (φ n)).N (Q (φ n)).V) atTop (nhds v) := by
  let lo := fun n => Real.logb (P n).N
    ((P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n)))
  let hi := fun n => Real.logb (P n).N (2*(Q n).N)
  let x := fun n => Real.logb (P n).N (Q n).V
  have hlo : Tendsto lo atTop (nhds (σ+τ/2-1)) :=
    reflection_tendsto_log_value_floor P err he hT hV
  have htwo : Tendsto (fun n => Real.logb (P n).N 2) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp hNtop)
  have hhi : Tendsto hi atTop (nhds κ) := by
    simpa only [hi,Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0)
      (zero_lt_one.trans (Q _).one_lt_N).ne',zero_add] using htwo.add hscale
  have hlower (n : ℕ) : lo n ≤ x n := by
    apply (Real.logb_le_logb (P n).one_lt_N _ (Q n).V_pos).mpr (hvalue n)
    exact div_pos (mul_pos (P n).V_pos (Real.sqrt_pos.mpr (P n).T_pos))
      (mul_pos (zero_lt_one.trans (P n).one_lt_N)
        (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _))
  have hupper (n : ℕ) : x n ≤ hi n :=
    (Real.logb_le_logb (P n).one_lt_N (Q n).V_pos
      (mul_pos (by norm_num) (zero_lt_one.trans (Q n).one_lt_N))).mpr
        ((Q n).value_le_two_mul_N_of_nonempty (hne n))
  have hbounded : ∀ᶠ n in atTop, x n ∈ Icc (σ+τ/2-2) (κ+1) := by
    filter_upwards [(tendsto_order.mp hlo).1 (σ+τ/2-2) (by linarith),
      (tendsto_order.mp hhi).2 (κ+1) (by linarith)] with n hn hn'
    exact ⟨hn.le.trans (hlower n),(hupper n).trans hn'.le⟩
  obtain ⟨v,_hv,φ,hφ,hlim⟩ := isCompact_Icc.tendsto_subseq' hbounded.frequently
  refine ⟨v,⟨?_,?_⟩,φ,hφ,hlim⟩
  · exact le_of_tendsto_of_tendsto (hlo.comp hφ.tendsto_atTop) hlim
      (Eventually.of_forall (fun n => hlower (φ n)))
  · exact le_of_tendsto_of_tendsto hlim (hhi.comp hφ.tendsto_atTop)
      (Eventually.of_forall (fun n => hupper (φ n)))

end TaoTrudgianYang2025
