import TaoTrudgianYang2025.IvicSixthPointWidth
import TaoTrudgianYang2025.PointValueRanges

/-! Arbitrary power-loss counting for actual critical-line zeta peaks. -/

noncomputable section
open Filter RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem exists_ivicSixth_pointValue_card_le {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card : ℝ) ≤ H^ε*(H/V^6+H^(15/4:ℝ)/V^24) := by
  classical
  let η : ℝ := min (ε/4) (1/1000)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηUpper : η ≤ 1/48 := (min_le_right _ _).trans (by norm_num)
  have hηε : η < ε := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨K,D,B,hK,hD,hB,hcount⟩ :=
    exists_ivicSixth_pointValue_card_le_source_range
      (δ := (1/48:ℝ)) (κ := η) (ν := η)
      (by norm_num) (by norm_num) hη hη
  obtain ⟨B₁,hB₁,hGrowth⟩ := exists_zetaMomentCriticalNorm_lt_sixth_power hη
  have hlower := eventually_pointValue_source_lower_range hK hη
  have hupper := eventually_pointValue_sixth_power_source_range hK hη hηUpper
  have hl4 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := D) (a := η) (b := ε) hD.le 4 hηε
  have hl13 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := D) (a := η) (b := ε) hD.le 13 hηε
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.mp (hlower.and (hupper.and (hl4.and hl13)))
  refine ⟨max B (max B₁ B₂),le_max_of_le_left hB,?_⟩
  intro H V W hH hV hVlower hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHB₂ : B₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith [hB.trans hHB]
  have hH1 : 1 ≤ H := by linarith [hB₁.trans hHB₁]
  obtain ⟨hl,hu,hl4,hl13⟩ := hB₂ H hHB₂
  rcases W.eq_empty_or_nonempty with rfl | ⟨t,ht⟩
  · simp only [Finset.card_empty,Nat.cast_zero]
    positivity
  have hVgrowth : V ≤ H^(1/6+η) :=
    (hlarge t ht).trans (hGrowth H t hHB₁ (hrange t ht).1 (hrange t ht).2).le
  have hVl : H^(1/8+η) ≤ V :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hVlower
  have hVsq := pow_le_pow_left₀ (by positivity : 0 ≤ H^(1/8+η)) hVl 2
  have hVupper := pow_le_pow_left₀ hV.le hVgrowth 2
  have hc := hcount H V W hHB hV (hl.trans hVsq) (hVupper.trans hu.2)
    hsep hrange hlarge
  calc
    _ ≤ D*H^η*(H*(Real.log (3*H))^4/V^6+
        H^(15/4:ℝ)*(Real.log (3*H))^13/V^24) := hc
    _ = (D*(Real.log (3*H))^4*H^η)*(H/V^6)+
        (D*(Real.log (3*H))^13*H^η)*(H^(15/4:ℝ)/V^24) := by ring
    _ ≤ H^ε*(H/V^6)+H^ε*(H^(15/4:ℝ)/V^24) :=
      add_le_add (mul_le_mul_of_nonneg_right hl4 (by positivity))
        (mul_le_mul_of_nonneg_right hl13 (by positivity))
    _ = _ := by ring

end TaoTrudgianYang2025
