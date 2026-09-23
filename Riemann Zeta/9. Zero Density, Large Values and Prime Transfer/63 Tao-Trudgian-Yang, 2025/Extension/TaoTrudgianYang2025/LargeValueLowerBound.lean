import TaoTrudgianYang2025.LargeValueLowerPatterns
import TaoTrudgianYang2025.LargeValueHalfExponent

/-! The general source lower bound, from actual coherent-block patterns. -/

open Filter Topology

noncomputable section

namespace TaoTrudgianYang2025

theorem exists_lower_largeValueEnergyRegion {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    ∃ ρ e s : ℝ, InLargeValueEnergyRegion σ τ ρ e s ∧ min (2-2*σ) τ ≤ ρ := by
  have hex (n : ℕ) : ∃ P : LargeValuePattern,
      P.N = (n:ℝ)+2 ∧ P.T = ((n:ℝ)+2)^τ ∧
      (1/8)*((n:ℝ)+2)^σ ≤ P.V ∧ P.V ≤ ((n:ℝ)+2)^σ ∧
      ((n:ℝ)+2)^(min τ (2-2*σ)) ≤ 24*(P.ordinates.card:ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      exists_lower_largeValuePattern (τ:=τ) (n+2) (by omega) hσ hσ₁
  choose P hN hT hVl hVu hcard using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    simp only [hN]
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hpowlog (x : ℝ) : Tendsto (fun n => Real.logb (P n).N ((P n).N^x))
      atTop (nhds x) := by
    have heq (n : ℕ) : Real.logb (P n).N ((P n).N^x) = x :=
      Real.logb_rpow (zero_lt_one.trans (P n).one_lt_N) (ne_of_gt (P n).one_lt_N)
    simp only [heq]
    exact tendsto_const_nhds
  have hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ) := by
    simpa only [hT,hN] using hpowlog τ
  have hVlog : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => (P n).N^σ) (fun n => (P n).V) σ (1/8) 1
      (fun n => (P n).one_lt_N) hNtop
      (fun n => Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _)
      (by norm_num) zero_lt_one _ (hpowlog σ)
    intro n
    simpa only [hN,one_mul] using And.intro (hVl n) (hVu n)
  let β := min τ (2-2*σ)
  have hc (n : ℕ) : (1/24)*(P n).N^β ≤ ((P n).ordinates.card:ℝ) := by
    rw [hN]
    dsimp [β]
    linarith [hcard n]
  have hbasepos (n : ℕ) : 0 < (1/24)*(P n).N^β :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _)
  have hcpos (n : ℕ) : 0 < ((P n).ordinates.card:ℝ) := (hbasepos n).trans_le (hc n)
  have hlowerlog : Tendsto (fun n => Real.logb (P n).N ((1/24)*(P n).N^β))
      atTop (nhds β) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => (P n).N^β) (fun n => (1/24)*(P n).N^β) β (1/24) (1/24)
      (fun n => (P n).one_lt_N) hNtop
      (fun n => Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _)
      (by norm_num) (by norm_num) (fun _ => ⟨le_rfl,le_rfl⟩) (hpowlog β)
  obtain ⟨x,φ,hφ,hlim,hmem⟩ :=
    energyRegion_subsequence_of_log_limits hσ hσ₁ hτ P hNtop hTlog hVlog hcpos
  have hρ : Tendsto (fun n => Real.logb (P (φ n)).N
      ((P (φ n)).ordinates.card:ℝ)) atTop (nhds x.1) := by
    simpa only [Function.comp_def,energyLogCoordinates] using
      (continuous_fst.tendsto x).comp hlim
  have hb : β ≤ x.1 := by
    apply le_of_tendsto_of_tendsto' (hlowerlog.comp hφ.tendsto_atTop) hρ
    intro n
    exact (Real.logb_le_logb (P (φ n)).one_lt_N (hbasepos (φ n)) (hcpos (φ n))).mpr
      (hc (φ n))
  exact ⟨x.1,x.2.1,x.2.2,hmem,by simpa only [β,min_comm] using hb⟩

theorem IsLargeValueBound.source_lower {σ τ B : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ)
    (h : IsLargeValueBound σ τ B) : min (2-2*σ) τ ≤ B := by
  obtain ⟨ρ,e,s,hr,hb⟩ := exists_lower_largeValueEnergyRegion hσ hσ₁ hτ
  exact hb.trans (hr.rho_le_of_largeValueBound h)

theorem largeValueExponent_lower {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ₁ : σ ≤ 1) (hτ : 0 ≤ τ) :
    ((min (2-2*σ) τ:ℝ):EReal) ≤ largeValueExponent σ τ := by
  unfold largeValueExponent
  apply le_sInf
  rintro x ⟨B,hB,rfl⟩
  exact EReal.coe_le_coe_iff.mpr (IsLargeValueBound.source_lower hσ hσ₁ hτ hB)

end TaoTrudgianYang2025

