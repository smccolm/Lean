import TaoTrudgianYang2025.ZetaReflectionScaleLimits

/-! Reflected counterexample families chosen after every accuracy-dependent threshold. -/

noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped Classical BigOperators
namespace TaoTrudgianYang2025

theorem exists_reflection_counterexample_families {σ τ B : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 1 < τ) (hnot : ¬ IsZetaLargeValueBound σ τ B) :
    ∃ η : ℝ, 0 < η ∧ ∃ err : ℕ → ℝ,
      (∀ n, 0 < err n) ∧ Tendsto err atTop (nhds 0) ∧
      ∃ P Q : ℕ → ZetaLargeValuePattern,
        Tendsto (fun n => (P n).N) atTop atTop ∧
        Tendsto (fun n => Real.logb (P n).N (P n).T) atTop (nhds τ) ∧
        Tendsto (fun n => Real.logb (P n).N (P n).V) atTop (nhds σ) ∧
        ∀ n, (P n).N^(B+η) ≤ ((P n).ordinates.card : ℝ) ∧
          (Q n).ordinates.Nonempty ∧
          ((P n).T/(4*Real.pi*(P n).N)/2 ≤ (Q n).N ∧
            (Q n).N ≤ 4*((P n).T/(4*Real.pi*(P n).N))) ∧
          ((P n).T/2 ≤ (Q n).T ∧ (Q n).T ≤ 2*(P n).T) ∧
          (P n).V*Real.sqrt (P n).T/((P n).N*(P n).N^(err n)) ≤ (Q n).V ∧
          ((P n).ordinates.card : ℝ)*(P n).V*Real.sqrt (P n).T/
              ((P n).N*(P n).N^(err n)) ≤
            (Q n).V*((Q n).ordinates.card : ℝ) := by
  rw [IsZetaLargeValueBound] at hnot
  push Not at hnot
  obtain ⟨η,hη,hfail⟩ := hnot
  let err : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have he (n : ℕ) : 0 < err n := by dsimp [err]; positivity
  have he0 : Tendsto err atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose d hd M hM hentry using
    (fun n => exists_zetaReflection_power_loss_pattern hτ (he n))
  have hex (n : ℕ) : ∃ P Q : ZetaLargeValuePattern,
      (n : ℝ)+2 ≤ P.N ∧
      (P.N^(τ-err n) ≤ P.T ∧ P.T ≤ P.N^(τ+err n)) ∧
      (P.N^(σ-err n) ≤ P.V ∧ P.V ≤ P.N^(σ+err n)) ∧
      P.N^(B+η) ≤ (P.ordinates.card : ℝ) ∧ Q.ordinates.Nonempty ∧
      (P.T/(4*Real.pi*P.N)/2 ≤ Q.N ∧ Q.N ≤ 4*(P.T/(4*Real.pi*P.N))) ∧
      (P.T/2 ≤ Q.T ∧ Q.T ≤ 2*P.T) ∧
      P.V*Real.sqrt P.T/(P.N*P.N^(err n)) ≤ Q.V ∧
      (P.ordinates.card : ℝ)*P.V*Real.sqrt P.T/(P.N*P.N^(err n)) ≤
        Q.V*(Q.ordinates.card : ℝ) := by
    let C := max (M n) ((n : ℝ)+2)
    let δ := min (d n) (err n)
    have hC : 1 ≤ C := (hM n).trans (le_max_left _ _)
    have hδ : 0 < δ := lt_min (hd n) (he n)
    have hδd : δ ≤ d n := min_le_left _ _
    have hδe : δ ≤ err n := min_le_right _ _
    obtain ⟨P,hN,hTl,hTu,hVl,hVu,hc⟩ := hfail C hC δ hδ
    have hNp := zero_lt_one.trans P.one_lt_N
    have hcard : P.N^(B+η) ≤ (P.ordinates.card : ℝ) :=
      (le_mul_of_one_le_left (Real.rpow_nonneg hNp.le _) hC).trans hc.le
    have hcardp : (0 : ℝ) < P.ordinates.card :=
      (Real.rpow_pos_of_pos hNp _).trans_le hcard
    have hne : P.ordinates.Nonempty := Finset.card_pos.mp (by exact_mod_cast hcardp)
    have hTld : P.N^(τ-d n) ≤ P.T :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTl
    have hTud : P.T ≤ P.N^(τ+d n) := hTu.trans
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
    have hVld : P.N^(σ-d n) ≤ P.V :=
      (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hVl
    obtain ⟨_u,_hu,Q,hQne,_hQsub,hQNl,hQNu,hQTl,hQTu,hQV,hQmass⟩ :=
      hentry n P ((le_max_left _ _).trans hN) σ hσ hTld hTud hVld hne
    refine ⟨P,Q,(le_max_right _ _).trans hN,⟨?_,?_⟩,⟨?_,?_⟩,hcard,hQne,
      ⟨hQNl,hQNu⟩,⟨hQTl,hQTu⟩,hQV,hQmass⟩
    · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hTl
    · exact hTu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
    · exact (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith)).trans hVl
    · exact hVu.trans (Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le (by linarith))
  choose P Q hN hT hV hc hQne hs ht hv hm using hex
  have hNtop : Tendsto (fun n => (P n).N) atTop atTop := by
    apply tendsto_atTop_mono' atTop (Eventually.of_forall hN)
    exact tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hTlog := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => (P n).T) err τ (fun n => (P n).one_lt_N)
    (fun n => (P n).T_pos) he0 hT
  have hVlog := tendsto_logb_of_power_sandwich (fun n => (P n).N)
    (fun n => (P n).V) err σ (fun n => (P n).one_lt_N)
    (fun n => (P n).V_pos) he0 hV
  exact ⟨η,hη,err,he,he0,P,Q,hNtop,hTlog,hVlog,
    fun n => ⟨hc n,hQne n,hs n,ht n,hv n,hm n⟩⟩

end TaoTrudgianYang2025
