import TaoTrudgianYang2025.LargeValueRegionWitness
import TaoTrudgianYang2025.LargeValueBoundClosure
import TaoTrudgianYang2025.LargeValueNonnegative

/-!
# The exact large-value exponent is attained by an actual energy-region point

Failure below the infimum gives genuine patterns on unbounded scales.
A common compactness subsequence retains all three energy coordinates;
the uniform upper bound identifies the limiting cardinality exactly.
-/

noncomputable section
open Filter Topology
namespace TaoTrudgianYang2025

theorem exists_energyRegion_at_largeValueExponent {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hσ1 : σ ≤ 1) (hτ : 0 ≤ τ) :
    ∃ e s : ℝ,
      InLargeValueEnergyRegion σ τ (largeValueExponent σ τ).toReal e s := by
  have hcoe := largeValueExponent_coe_toReal hσ hσ1 hτ
  let L : ℝ := (largeValueExponent σ τ).toReal
  have hbound : IsLargeValueBound σ τ L :=
    isLargeValueBound_of_exponent_le (by rw [← hcoe])
  let err : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have he (n : ℕ) : 0 < err n := by dsimp [err]; positivity
  have he0 : Tendsto err atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnot (n : ℕ) : ¬ IsLargeValueBound σ τ (L-err n) := by
    intro hh
    have hb := largeValueExponent_le_of_bound hh
    rw [← hcoe] at hb
    have hh' := EReal.coe_le_coe_iff.mp hb
    have hp := he n
    change L ≤ L-err n at hh'
    linarith
  have hex (n : ℕ) : ∃ P : LargeValuePattern,
      (n : ℝ)+2 ≤ P.N ∧
      P.N^(τ-err n) ≤ P.T ∧ P.T ≤ P.N^(τ+err n) ∧
      P.N^(σ-err n) ≤ P.V ∧ P.V ≤ P.N^(σ+err n) ∧
      P.N^(L-2*err n) ≤ (P.ordinates.card : ℝ) := by
    obtain ⟨ρ,e,s,hm,hρ⟩ :=
      energyRegion_exists_rho_gt_of_not_largeValueBound hσ hσ1 hτ (hnot n)
    obtain ⟨P,hN,hTl,hTu,hVl,hVu,hcl,_⟩ :=
      hm.2.2.2.2.2 (err n) (he n) (err n) (he n) ((n : ℝ)+2) (by positivity)
    refine ⟨P,hN,hTl,hTu,hVl,hVu,?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hcl
  choose P hN hTl hTu hVl hVu hcard using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono' atTop (Eventually.of_forall hN)
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hc (n : ℕ) : (0 : ℝ) < (P n).ordinates.card :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _).trans_le (hcard n)
  have hTlog := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => (P n).T) err τ (fun n => (P n).one_lt_N)
    (fun n => (P n).T_pos) he0 (fun n => ⟨hTl n,hTu n⟩)
  have hVlog := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => (P n).V) err σ (fun n => (P n).one_lt_N)
    (fun n => (P n).V_pos) he0 (fun n => ⟨hVl n,hVu n⟩)
  obtain ⟨x,φ,hφ,hlim,hm⟩ :=
    energyRegion_subsequence_of_log_limits hσ hσ1 hτ P hNtop hTlog hVlog hc
  have hr : Tendsto (fun n => Real.logb (P (φ n)).N
      ((P (φ n)).ordinates.card : ℝ)) atTop (nhds x.1) := by
    simpa only [Function.comp_def,energyLogCoordinates] using
      (continuous_fst.tendsto x).comp hlim
  have hlower : L ≤ x.1 := by
    have heφ := he0.comp hφ.tendsto_atTop
    have hl : Tendsto (fun n => L-2*err (φ n)) atTop (nhds L) := by
      simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (heφ.const_mul 2)
    apply le_of_tendsto_of_tendsto hl hr
    exact Eventually.of_forall fun n =>
      (Real.le_logb_iff_rpow_le (P (φ n)).one_lt_N (hc (φ n))).mpr (hcard (φ n))
  have heq : x.1 = L := le_antisymm (hm.rho_le_of_largeValueBound hbound) hlower
  rw [heq] at hm
  exact ⟨x.2.1,x.2.2,hm⟩

end TaoTrudgianYang2025
