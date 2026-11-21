import Dubon2026.EnergyBands

namespace Dubon2026
open Filter Set
open scoped Topology
noncomputable section

/-- On the logarithmic scale the number of amplitude classes has exponent zero. -/
private theorem energyBandCount_upper :
    ∀ᶠ N : ℕ in atTop, (energyBandCount N : ℝ) ≤ (3 / Real.log 2 + 1) * Real.log N := by
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_ge_atTop 1] with N hN
  have h := Real.natLog_le_logb (N^3) 2
  simp only [Real.logb,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at h
  unfold energyBandCount
  push_cast
  linarith [show 3 * Real.log N / Real.log 2 = (3/Real.log 2)*Real.log N by ring]

theorem maximalEnergyBand_growth {e : ℕ → ℝ} (he : ∀ n, 0 ≤ e n) {C : ℝ} (hC : 0 < C)
    (hu : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, e n ≤ C * N)
    (hl : ∀ᶠ N : ℕ in atTop, ((N:ℝ)/Real.log N)/4 ≤ ∑ p ∈ dyadicPrimes N, e p) :
    (∀ᶠ N : ℕ in atTop, 0 < ∑ p ∈ maximalEnergyBand e N, e p) ∧
      Tendsto (fun N : ℕ => Real.log (∑ p ∈ maximalEnergyBand e N, e p) / Real.log N) atTop (𝓝 1) := by
  let W := fun N => ∑ p ∈ maximalEnergyBand e N, e p
  let K := 8 * (3/Real.log 2 + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hNlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log N) / Real.log N) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [pow_one,one_mul,add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    exact h.comp hNlog
  have hsub (N : ℕ) : dyadicPrimes N ⊆ Finset.Icc 1 N := fun p hp =>
    Finset.mem_Icc.mpr ⟨(mem_dyadicPrimes.mp hp).1.one_le,(mem_dyadicPrimes.mp hp).2.2⟩
  have hwUpper (N : ℕ) : W N ≤ C * N :=
    (Finset.sum_le_sum_of_subset_of_nonneg ((maximalEnergyBand_subset e N).trans (hsub N)) (fun p _ _ => he p)).trans (hu N)
  have hlow : ∀ᶠ N : ℕ in atTop, (N:ℝ) / (K * (Real.log N)^2) ≤ W N := by
    filter_upwards [hl, energyBandCount_upper, tendsto_nat_div_log_atTop.eventually_ge_atTop 8,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop C, eventually_ge_atTop (2:ℕ)]
      with N hm hc hlarge hCN hN
    have hn : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog := Real.log_pos hn
    have hb := maximalEnergyBand_mass (e := e) (show 1 ≤ N by omega) (by
      intro p hp
      have hpe := (Finset.single_le_sum (fun n (_ : n ∈ Finset.Icc 1 N) => he n) (hsub N hp)).trans (hu N)
      calc (N:ℝ)* e p ≤ N * (C * N) := mul_le_mul_of_nonneg_left hpe (by positivity)
           _ ≤ (N:ℝ)^3 := by nlinarith [mul_le_mul_of_nonneg_right hCN (sq_nonneg (N:ℝ))])
    have hw : 0 ≤ W N := Finset.sum_nonneg fun p _ => he p
    have hprod := mul_le_mul_of_nonneg_right hc hw
    change _ ≤ 1 + (energyBandCount N : ℝ) * W N at hb
    have hdiv : (N:ℝ) / Real.log N ≤ (K * Real.log N) * W N := by dsimp [K]; linarith
    have hmul := (div_le_iff₀ hlog).mp hdiv
    apply (div_le_iff₀ (mul_pos hK (sq_pos_of_pos hlog))).mpr
    linarith only [show (K * Real.log N * W N) * Real.log N = W N * (K * Real.log N ^ 2) by ring, hmul]
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < W N := by
    filter_upwards [hlow,eventually_ge_atTop (2:ℕ)] with N h hN
    have hn : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact (div_pos (by linarith) (mul_pos hK (sq_pos_of_pos (Real.log_pos hn)))).trans_le h
  refine ⟨hpos, ?_⟩
  have hlo : Tendsto (fun N : ℕ => 1 - Real.log K / Real.log N - 2 * (Real.log (Real.log N) / Real.log N)) atTop (𝓝 1) := by
    simpa only [sub_zero,mul_zero] using ((tendsto_const_nhds (x := (1:ℝ))).sub (hNlog.const_div_atTop (Real.log K))).sub (hloglog.const_mul 2)
  have hhi : Tendsto (fun N : ℕ => Real.log C / Real.log N + 1) atTop (𝓝 1) := by
    simpa only [zero_add] using (hNlog.const_div_atTop (Real.log C)).add_const 1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hlow,eventually_ge_atTop (2:ℕ)] with N h hN
    have hn : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog := Real.log_pos hn
    have h0 := lt_trans zero_lt_one hn
    have hh := div_le_div_of_nonneg_right (Real.log_le_log (div_pos h0 (mul_pos hK (sq_pos_of_pos hlog))) h) hlog.le
    rw [Real.log_div h0.ne' (mul_pos hK (sq_pos_of_pos hlog)).ne', Real.log_mul hK.ne' (sq_pos_of_pos hlog).ne', Real.log_pow] at hh
    convert hh using 1
    field_simp [hlog.ne']
    ring
  · filter_upwards [hpos,eventually_ge_atTop (2:ℕ)] with N h hN
    have hn : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hh := div_le_div_of_nonneg_right (Real.log_le_log h (hwUpper N)) (Real.log_pos hn).le
    rw [Real.log_mul hC.ne' (lt_trans zero_lt_one hn).ne', add_div, div_self (Real.log_pos hn).ne'] at hh
    exact hh

theorem maximalEnergyBand_card_growth {e : ℕ → ℝ} {B : ℝ} (hB : 0 < B)
    (hb : ∀ n : ℕ, 1 ≤ n → e n ≤ B * (n:ℝ)^(3/5:ℝ))
    (hpos : ∀ᶠ N : ℕ in atTop, 0 < ∑ p ∈ maximalEnergyBand e N, e p)
    (hlog : Tendsto (fun N : ℕ => Real.log (∑ p ∈ maximalEnergyBand e N, e p) / Real.log N) atTop (𝓝 1)) :
    Tendsto (fun N => (maximalEnergyBand e N).card) atTop atTop := by
  have hg := ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/5)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))).atTop_div_const hB
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hg.eventually_ge_atTop (b:ℝ),hlog.eventually (lt_mem_nhds (by norm_num : (4/5:ℝ)<1)),
    hpos,eventually_ge_atTop (2:ℕ)] with N hgrow hscale hmass hN
  have hn : (1:ℝ) < N := by exact_mod_cast (show 1<N by omega)
  have h0 := lt_trans zero_lt_one hn
  have hlow := Real.exp_le_exp.mpr ((lt_div_iff₀ (Real.log_pos hn)).mp hscale).le
  rw [Real.exp_log hmass, mul_comm (4/5:ℝ), ← Real.rpow_def_of_pos h0] at hlow
  have hhigh := Finset.sum_le_sum (s := maximalEnergyBand e N) (fun p hp =>
    (hb p (mem_dyadicPrimes.mp (maximalEnergyBand_subset e N hp)).1.one_le).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (y := (N:ℝ)) (Nat.cast_nonneg p)
        (by exact_mod_cast (mem_dyadicPrimes.mp (maximalEnergyBand_subset e N hp)).2.2) (by norm_num : (0:ℝ)≤3/5)) hB.le))
  simp only [Finset.sum_const,nsmul_eq_mul] at hhigh
  rw [show (4/5:ℝ) = 1/5 + 3/5 by norm_num, Real.rpow_add h0] at hlow
  have hrat : (N:ℝ)^(1/5:ℝ) ≤ (maximalEnergyBand e N).card * B := by
    apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos h0 (3/5:ℝ))).mp
    simpa only [mul_assoc] using hlow.trans hhigh
  exact_mod_cast (hgrow.trans ((div_le_iff₀ hB).mpr hrat))

end
end Dubon2026
