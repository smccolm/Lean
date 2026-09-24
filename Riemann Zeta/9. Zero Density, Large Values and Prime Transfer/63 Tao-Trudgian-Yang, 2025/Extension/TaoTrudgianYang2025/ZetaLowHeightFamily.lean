import TaoTrudgianYang2025.ZetaCoherentPattern
import TaoTrudgianYang2025.EnergyLogLimits

/-! A concrete unbounded low-height family with nonempty ordinate sets. -/

noncomputable section
open Filter Topology
namespace TaoTrudgianYang2025

theorem exists_lowHeight_zetaPattern (n : ℕ) (hn : 2 ≤ n) :
    ∃ P : ZetaLargeValuePattern,
      P.N = (n : ℝ)^4 ∧ P.T = (n : ℝ)/4 ∧
      P.V = (n : ℝ)^3/2 ∧ P.ordinates = {(n : ℝ)/4} := by
  have hn1 : 1 ≤ n := by omega
  have hnp : 0 < n := by omega
  have hp : 1 < n^4 := by
    have hh : n ≤ n^4 := by
      simpa using pow_le_pow_right₀ hn1 (by norm_num : (1 : ℕ) ≤ 4)
    omega
  have hL : 0 < n^3 := pow_pos hnp _
  have hLN : n^3 ≤ n^4 := pow_le_pow_right₀ hn1 (by norm_num)
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnp
  have hT : 0 < (n : ℝ)/4 := by positivity
  have hh : (n : ℝ)/4 ≤ ((n^4 : ℕ) : ℝ)/(2*((n^3 : ℕ) : ℝ)) := by
    push_cast
    apply (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ)^3)).mpr
    nlinarith [pow_nonneg hnr.le 4]
  refine ⟨coherentZetaPattern (n^4) (n^3) hp hL hLN ((n : ℝ)/4) hT hh,?_,rfl,?_,rfl⟩
  · simp only [coherentZetaPattern_scale,Nat.cast_pow]
  · simp only [coherentZetaPattern_value,Nat.cast_pow]

theorem zetaLargeValueExponent_ne_bot_of_nonempty_family
    {σ τ : ℝ} (P : ℕ → ZetaLargeValuePattern)
    (hN : Tendsto (fun n => (P n).N) atTop atTop)
    (hT : Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ))
    (hV : Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ))
    (hne : ∀ n, (P n).ordinates.Nonempty) :
    zetaLargeValueExponent σ τ ≠ ⊥ := by
  intro he
  obtain ⟨C,δ,_hC,hδ,hbound⟩ :=
    (zetaLargeValueExponent_eq_bot_iff_empty_threshold σ τ).mp he
  have hbase : ∀ᶠ n in atTop, 1 ≤ (P n).N :=
    Eventually.of_forall fun n => (P n).one_lt_N.le
  have ht := Expdb.isPowerAsymptotic_of_logb_tendsto
    (Eventually.of_forall fun n => (P n).one_lt_N)
    (Eventually.of_forall fun n => (P n).T_pos) hT
  have hv := Expdb.isPowerAsymptotic_of_logb_tendsto
    (Eventually.of_forall fun n => (P n).one_lt_N)
    (Eventually.of_forall fun n => (P n).V_pos) hV
  obtain ⟨n,hscale,htb,hvb⟩ :=
    ((hN.eventually (eventually_ge_atTop C)).and
      ((ht.eventually_between hbase hδ).and (hv.eventually_between hbase hδ))).exists
  have hempty := hbound (P n) hscale htb.1 htb.2 hvb.1 hvb.2
  exact (hne n).ne_empty hempty

end TaoTrudgianYang2025

