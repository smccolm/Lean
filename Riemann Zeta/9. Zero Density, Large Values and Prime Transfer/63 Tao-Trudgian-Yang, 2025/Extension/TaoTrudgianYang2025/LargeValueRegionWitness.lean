import TaoTrudgianYang2025.EnergyPoweringLimits
import TaoTrudgianYang2025.EnergyCardinalityBounds

/-! Failure of a uniform cardinality bound yields an actual feasible region point. -/

noncomputable section

open Filter Topology

namespace TaoTrudgianYang2025

theorem energyRegion_exists_rho_gt_of_not_largeValueBound
    {σ τ B : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ)
    (hnot : ¬ IsLargeValueBound σ τ B) :
    ∃ ρ e s : ℝ, InLargeValueEnergyRegion σ τ ρ e s ∧ B < ρ := by
  rw [IsLargeValueBound] at hnot
  push Not at hnot
  obtain ⟨η,hη,hfail⟩ := hnot
  let err : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have he (n : ℕ) : 0 < err n := by dsimp [err]; positivity
  have he0 : Tendsto err atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hex (n : ℕ) : ∃ P : LargeValuePattern,
      (n:ℝ)+2 ≤ P.N ∧
      P.N^(τ-err n) ≤ P.T ∧ P.T ≤ P.N^(τ+err n) ∧
      P.N^(σ-err n) ≤ P.V ∧ P.V ≤ P.N^(σ+err n) ∧
      ((n:ℝ)+2)*P.N^(B+η) < (P.ordinates.card:ℝ) :=
    hfail ((n:ℝ)+2) (by have := Nat.cast_nonneg (α:=ℝ) n; linarith) (err n) (he n)
  choose P hN hTl hTu hVl hVu hcard using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono' atTop (Eventually.of_forall hN)
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hc (n : ℕ) : 0 < ((P n).ordinates.card:ℝ) := by
    have hp : 0 < ((n:ℝ)+2)*(P n).N^(B+η) :=
      mul_pos (by positivity) (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _)
    exact hp.trans (hcard n)
  have hcl (n : ℕ) : (P n).N^(B+η) ≤ ((P n).ordinates.card:ℝ) := by
    have hf : 1 ≤ (n:ℝ)+2 := by have := Nat.cast_nonneg (α:=ℝ) n; linarith
    exact (le_mul_of_one_le_left
      (Real.rpow_nonneg (zero_lt_one.trans (P n).one_lt_N).le _) hf).trans (hcard n).le
  have hTlog := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => (P n).T) err τ (fun n => (P n).one_lt_N)
    (fun n => (P n).T_pos) he0 (fun n => ⟨hTl n,hTu n⟩)
  have hVlog := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => (P n).V) err σ (fun n => (P n).one_lt_N)
    (fun n => (P n).V_pos) he0 (fun n => ⟨hVl n,hVu n⟩)
  obtain ⟨x,φ,_hφ,hlim,hmem⟩ :=
    energyRegion_subsequence_of_log_limits hσ hσ₁ hτ P hNtop hTlog hVlog hc
  have hρ : Tendsto (fun n => Real.logb (P (φ n)).N
      ((P (φ n)).ordinates.card:ℝ)) atTop (nhds x.1) := by
    simpa only [Function.comp_def,energyLogCoordinates] using
      (continuous_fst.tendsto x).comp hlim
  have hb : B+η ≤ x.1 := by
    apply ge_of_tendsto' hρ
    intro n
    exact (Real.le_logb_iff_rpow_le (P (φ n)).one_lt_N (hc (φ n))).mpr (hcl (φ n))
  exact ⟨x.1,x.2.1,x.2.2,hmem,by linarith⟩

theorem isLargeValueBound_iff_region_cardinality
    {σ τ B : ℝ} (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    IsLargeValueBound σ τ B ↔
      ∀ ρ e s : ℝ, InLargeValueEnergyRegion σ τ ρ e s → ρ ≤ B := by
  constructor
  · intro h ρ e s hm
    exact hm.rho_le_of_largeValueBound h
  · intro h
    by_contra hn
    obtain ⟨ρ,e,s,hm,hb⟩ := energyRegion_exists_rho_gt_of_not_largeValueBound hσ hσ₁ hτ hn
    exact (not_le_of_gt hb) (h ρ e s hm)

end TaoTrudgianYang2025

