import TaoTrudgianYang2025.IvicSixthPointRanges
import TaoTrudgianYang2025.PointValueMeasure

/-! Sixth-power weighted actual peak counts above the 11/72 threshold. -/

noncomputable section
open Filter MeasureTheory RiemannZeta.GuthMaynard
namespace TaoTrudgianYang2025

theorem exists_ivicSixth_weighted_card_le {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(11/72+ε) ≤ V →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card : ℝ)*V^6 ≤ H^(1+ε) := by
  obtain ⟨A,hA,hcount⟩ :=
    exists_ivicSixth_pointValue_card_le (show 0 < ε/4 by linarith)
  obtain ⟨B,hB⟩ := eventually_atTop.mp
    (eventually_const_height_log_pow_mul_rpow_le_rpow
      (C := 2) (a := 1+ε/4) (b := 1+ε) (by norm_num) 0 (by linarith))
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro H V W hH hV hLower hsep hrange hlarge
  have hAH : A ≤ H := (le_max_left _ _).trans hH
  have hBH : B ≤ H := (le_max_right _ _).trans hH
  have hH1 : 1 ≤ H := by linarith [hA.trans hAH]
  have hH0 : 0 < H := by linarith
  have hlo : H^(1/8+ε/4) ≤ V :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hLower
  have hc := hcount H V W hAH hV hlo hsep hrange hlarge
  have hbase : H^(11/72:ℝ) ≤ V :=
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)).trans hLower
  have hp : H^(11/4:ℝ) ≤ V^18 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ H^(11/72:ℝ)) hbase 18
    rw [← Real.rpow_mul_natCast hH0.le] at hh
    convert hh using 1
    norm_num
  have he : H^(15/4:ℝ) = H*H^(11/4:ℝ) := by
    calc
      _ = H^(1+(11/4:ℝ)) := by congr 1; norm_num
      _ = _ := by rw [Real.rpow_add hH0,Real.rpow_one]
  have hf : H^(15/4:ℝ)/V^18 ≤ H :=
    (div_le_iff₀ (by positivity)).2 (by rw [he]; exact mul_le_mul_of_nonneg_left hp hH0.le)
  have hb : 2*H^(1+ε/4) ≤ H^(1+ε) := by
    simpa only [pow_zero,mul_one] using hB H hBH
  calc
    _ ≤ (H^(ε/4)*(H/V^6+H^(15/4:ℝ)/V^24))*V^6 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = H^(ε/4)*(H+H^(15/4:ℝ)/V^18) := by field_simp
    _ ≤ H^(ε/4)*(H+H) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hf) (by positivity)
    _ = 2*H^(1+ε/4) := by
      rw [Real.rpow_add hH0,Real.rpow_one]
      ring
    _ ≤ _ := hb

theorem exists_ivicSixth_volume_superlevel_le {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H V : ℝ,
      H₀ ≤ H → 0 < V → H^(11/72+ε) ≤ V →
      volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(1+ε)/V^6) := by
  obtain ⟨H₀,hH₀,hcount⟩ := exists_ivicSixth_weighted_card_le hε
  refine ⟨H₀,hH₀,?_⟩
  intro H V hH hV hLower
  have hc : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      IsSeparated 1 W → (W.card : ℝ) ≤ H^(1+ε)/V^6 := by
    intro W hWS hsep
    apply (le_div_iff₀ (by positivity)).mpr
    exact hcount H V W hH hV hLower hsep
      (fun t ht => ⟨(hWS t ht).1,(hWS t ht).2.1⟩)
      (fun t ht => (hWS t ht).2.2)
  have hm := volume_le_two_mul_of_separated_card_bound hc
  convert hm using 1
  congr 1
  ring

end TaoTrudgianYang2025
