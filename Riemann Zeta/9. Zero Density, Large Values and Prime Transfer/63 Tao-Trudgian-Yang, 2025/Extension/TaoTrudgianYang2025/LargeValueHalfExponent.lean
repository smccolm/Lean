import TaoTrudgianYang2025.LargeValueRandomPattern
import TaoTrudgianYang2025.EnergyPoweringLimits
import TaoTrudgianYang2025.EnergyCardinalityBounds
import TaoTrudgianYang2025.LargeValueExponent

/-! The exact square-root large-value exponent from actual random-sign patterns. -/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

theorem halfPattern_value_sandwich {N : ℝ} (hN : 1 ≤ N) :
    (1/2)*Real.sqrt N ≤ Real.sqrt ((N+1)/2) ∧
      Real.sqrt ((N+1)/2) ≤ Real.sqrt N := by
  have hNp : 0 ≤ N := zero_le_one.trans hN
  have hVp : 0 ≤ (N+1)/2 := by positivity
  have hsqN := Real.sq_sqrt hNp
  have hsqV := Real.sq_sqrt hVp
  have hsn := Real.sqrt_nonneg N
  have hsv := Real.sqrt_nonneg ((N+1)/2)
  constructor
  · nlinarith
  · exact Real.sqrt_le_sqrt (by linarith)

theorem exists_half_largeValueEnergyRegion {τ : ℝ} (hτ : 0 ≤ τ) :
    ∃ e s : ℝ, InLargeValueEnergyRegion (1/2) τ τ e s := by
  have hex (n : ℕ) : ∃ P : LargeValuePattern,
      P.N = (n:ℝ)+2 ∧ P.T = ((n:ℝ)+2)^τ ∧
      P.V = Real.sqrt (((n:ℝ)+3)/2) ∧
      ((n:ℝ)+2)^τ ≤ 12*(P.ordinates.card:ℝ) := by
    have h := exists_half_largeValuePattern (n+2) (by omega)
      (((n:ℝ)+2)^τ) (Real.rpow_pos_of_pos (by positivity) _)
    simpa only [Nat.cast_add,Nat.cast_ofNat,show (n:ℝ)+2+1 = n+3 by ring] using h
  choose P hN hT hV hcard using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    simp only [hN]
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hTpow (n : ℕ) : (P n).T = (P n).N^τ := by rw [hN,hT]
  have hVeq (n : ℕ) : (P n).V = Real.sqrt (((P n).N+1)/2) := by
    rw [hN,hV]
    congr 2
    ring
  have hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ) := by
    have heq (n : ℕ) : Real.logb (P n).N (P n).T = τ := by
      rw [hTpow,Real.logb_rpow (zero_lt_one.trans (P n).one_lt_N)
        (ne_of_gt (P n).one_lt_N)]
    simp only [heq]
    exact tendsto_const_nhds
  have hslog : Tendsto (fun n => Real.logb (P n).N (Real.sqrt (P n).N))
      atTop (nhds (1/2:ℝ)) := by
    have heq (n : ℕ) : Real.logb (P n).N (Real.sqrt (P n).N) = 1/2 := by
      rw [Real.sqrt_eq_rpow,Real.logb_rpow (zero_lt_one.trans (P n).one_lt_N)
        (ne_of_gt (P n).one_lt_N)]
    simp only [heq]
    exact tendsto_const_nhds
  have hVlog : Tendsto (fun n => Real.logb (P n).N (P n).V)
      atTop (nhds (1/2:ℝ)) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => Real.sqrt (P n).N) (fun n => (P n).V) (1/2) (1/2) 1
      (fun n => (P n).one_lt_N) hNtop
      (fun n => Real.sqrt_pos.mpr (zero_lt_one.trans (P n).one_lt_N))
      (by norm_num) zero_lt_one _ hslog
    intro n
    change (1/2)*Real.sqrt (P n).N ≤ (P n).V ∧
      (P n).V ≤ 1*Real.sqrt (P n).N
    rw [hVeq,one_mul]
    exact halfPattern_value_sandwich (P n).one_lt_N.le
  have hc (n : ℕ) : (P n).T ≤ 12*((P n).ordinates.card:ℝ) := by
    rw [hT]
    exact hcard n
  have hcpos (n : ℕ) : 0 < ((P n).ordinates.card:ℝ) := by
    have := (P n).T_pos
    linarith [hc n]
  have hclog : Tendsto (fun n => Real.logb (P n).N
      ((P n).ordinates.card:ℝ)) atTop (nhds τ) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => (P n).T) (fun n => ((P n).ordinates.card:ℝ)) τ (1/12) 2
      (fun n => (P n).one_lt_N) hNtop (fun n => (P n).T_pos)
      (by norm_num) (by norm_num) _ hTlog
    intro n
    have htone : 1 ≤ (P n).T := by
      rw [hTpow]
      exact Real.one_le_rpow (P n).one_lt_N.le hτ
    constructor
    · linarith [hc n]
    · linarith [(P n).ordinate_card_cast_le]
  obtain ⟨x,φ,hφ,hlim,hmem⟩ := energyRegion_subsequence_of_log_limits
    (le_refl (1/2:ℝ)) (by norm_num) hτ P hNtop hTlog hVlog hcpos
  have hρ : Tendsto (fun n => Real.logb (P (φ n)).N
      ((P (φ n)).ordinates.card:ℝ)) atTop (nhds x.1) := by
    simpa only [Function.comp_def,energyLogCoordinates] using
      (continuous_fst.tendsto x).comp hlim
  have heq : x.1 = τ := tendsto_nhds_unique hρ (hclog.comp hφ.tendsto_atTop)
  exact ⟨x.2.1,x.2.2,by simpa only [heq] using hmem⟩

theorem IsLargeValueBound.half_lower {τ B : ℝ} (hτ : 0 ≤ τ)
    (h : IsLargeValueBound (1/2) τ B) : τ ≤ B := by
  obtain ⟨e,s,hr⟩ := exists_half_largeValueEnergyRegion hτ
  exact hr.rho_le_of_largeValueBound h

theorem largeValueExponent_half {τ : ℝ} (hτ : 0 ≤ τ) :
    largeValueExponent (1/2) τ = (τ:EReal) := by
  apply le_antisymm (largeValueExponent_le_tau (1/2) hτ)
  unfold largeValueExponent
  apply le_sInf
  rintro x ⟨B,hB,rfl⟩
  exact EReal.coe_le_coe_iff.mpr (IsLargeValueBound.half_lower hτ hB)

end TaoTrudgianYang2025
