import TaoTrudgianYang2025.ZetaCoherentScale
import TaoTrudgianYang2025.EnergyLogLimits
import TaoTrudgianYang2025.ZetaLargeValueDiscreteness

/-! The exact low-height zeta exponent from genuine separated coherent sums. -/

noncomputable section
open Expdb Filter Topology
namespace TaoTrudgianYang2025

theorem IsZetaLargeValueBound.family_powerBound {σ τ B : ℝ}
    (h : IsZetaLargeValueBound σ τ B) (P : ℕ → ZetaLargeValuePattern)
    (hN : Tendsto (fun n => (P n).N) atTop atTop)
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ)) :
    IsPowerBounded (fun n => ((P n).ordinates.card : ℝ)) (fun n => (P n).N) B := by
  have hbase : ∀ n, 1 ≤ (P n).N := fun n => (P n).one_lt_N.le
  have hNu : VariableObject.IsUnbounded (fun n => (P n).N) :=
    (VariableObject.isUnbounded_iff_tendsto_atTop
      (fun n => zero_le_one.trans (hbase n))).mpr hN
  apply (isPowerBounded_iff_forall_pos _ _ _ hbase hNu).mpr
  intro ε hε
  obtain ⟨C,_hC,δ,hδ,hbound⟩ := h ε hε
  have ht := isPowerAsymptotic_of_logb_tendsto
    (Eventually.of_forall fun n => (P n).one_lt_N)
    (Eventually.of_forall fun n => (P n).T_pos) hT
  have hv := isPowerAsymptotic_of_logb_tendsto
    (Eventually.of_forall fun n => (P n).one_lt_N)
    (Eventually.of_forall fun n => (P n).V_pos) hV
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hN.eventually (eventually_ge_atTop C),
    ht.eventually_between (Eventually.of_forall hbase) hδ,
    hv.eventually_between (Eventually.of_forall hbase) hδ] with n hn htn hvn
  rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (zero_le_one.trans (hbase n)) _)]
  exact hbound (P n) hn htn.1 htn.2 hvn.1 hvn.2

theorem zetaLargeValueExponent_ge_of_family {σ τ ρ c : ℝ}
    (P : ℕ → ZetaLargeValuePattern)
    (hN : Tendsto (fun n => (P n).N) atTop atTop)
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hc : 0 < c)
    (hcard : ∀ n, c*(P n).N^ρ ≤ ((P n).ordinates.card : ℝ)) :
    (ρ : EReal) ≤ zetaLargeValueExponent σ τ := by
  unfold zetaLargeValueExponent
  apply le_sInf
  rintro x ⟨B,hB,rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  have hbase : ∀ n, 1 ≤ (P n).N := fun n => (P n).one_lt_N.le
  apply exponent_le_of_isPowerBounded_of_eventually_norm_ge_rpow hbase
    ((VariableObject.isUnbounded_iff_tendsto_atTop
      (fun n => zero_le_one.trans (hbase n))).mpr hN)
    (hB.family_powerBound P hN hT hV) hc
  exact Eventually.of_forall fun n => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)] using hcard n

theorem zetaLargeValueExponent_eq_tau_of_lowHeight {σ τ : ℝ}
    (hσ : 0 ≤ σ) (hτ : 0 ≤ τ) (hrange : σ+τ ≤ 1) :
    zetaLargeValueExponent σ τ = (τ : EReal) := by
  have hex (n : ℕ) : ∃ P : ZetaLargeValuePattern,
      P.N = (n : ℝ)+2 ∧ P.T = ((n : ℝ)+2)^τ/8 ∧
      (1/4)*((n : ℝ)+2)^σ ≤ P.V ∧ P.V ≤ (1/2)*((n : ℝ)+2)^σ ∧
      (1/8)*((n : ℝ)+2)^τ ≤ (P.ordinates.card : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using
      exists_coherentZetaPowerPattern (n+2) (by omega) hσ hτ hrange
  choose P hN hT hVl hVu hcard using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    simp only [hN]
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hpowlog (x : ℝ) : Tendsto (fun n => Real.logb (P n).N ((P n).N^x))
      atTop (nhds x) := by
    have he (n : ℕ) : Real.logb (P n).N ((P n).N^x) = x :=
      Real.logb_rpow (zero_lt_one.trans (P n).one_lt_N) (ne_of_gt (P n).one_lt_N)
    simp only [he]
    exact tendsto_const_nhds
  have hTlog : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => (P n).N^τ) (fun n => (P n).T) τ (1/8) (1/8)
      (fun n => (P n).one_lt_N) hNtop
      (fun n => Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _)
      (by norm_num) (by norm_num) _ (hpowlog τ)
    intro n
    dsimp only
    rw [hN,hT]
    constructor <;> linarith
  have hVlog : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ) := by
    apply tendsto_logb_of_const_mul_sandwich (fun n => (P n).N)
      (fun n => (P n).N^σ) (fun n => (P n).V) σ (1/4) (1/2)
      (fun n => (P n).one_lt_N) hNtop
      (fun n => Real.rpow_pos_of_pos (zero_lt_one.trans (P n).one_lt_N) _)
      (by norm_num) (by norm_num) _ (hpowlog σ)
    intro n
    simpa only [hN] using And.intro (hVl n) (hVu n)
  apply le_antisymm (zetaLargeValueExponent_le_tau σ hτ)
  apply zetaLargeValueExponent_ge_of_family P hNtop hTlog hVlog (by norm_num : (0 : ℝ) < 1/8)
  intro n
  simpa only [hN] using hcard n

end TaoTrudgianYang2025
