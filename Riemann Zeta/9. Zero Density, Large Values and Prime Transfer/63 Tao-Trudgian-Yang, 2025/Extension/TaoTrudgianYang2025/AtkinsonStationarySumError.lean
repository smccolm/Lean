import TaoTrudgianYang2025.AtkinsonStationarySumScale

/-!
# A summed stationary error on the actual physical source

The complete evaluated leading series has its original cutoff-derived
finite support. At widths at least T^(1/4), the retained arithmetic
error is O_epsilon(T^(1/4+epsilon)); the proved source tail adds O(G).
The smaller-width source range and final main-amplitude assembly remain
separate obligations, not hypotheses hidden in these estimates.
-/

noncomputable section

open Complex Filter

namespace TaoTrudgianYang2025

theorem exists_atkinsonStationary_finite_log_error {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hεmax : ε ≤ 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
          C*T^(1/4+ε)*(Real.log T)^2 := by
  obtain ⟨C,hC,hbound⟩ := exists_norm_atkinsonLeadingFiniteSum_sub_stationary_le hε
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T^δ ≤ G → G ≤ T^(1/2-δ) →
      T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
          (37*C)*T^(1/4+ε)*(Real.log T)^2 := by
    filter_upwards [eventually_zetaSmoothDivisorTest_support_physical hδ,
      eventually_zeta_source_log_window_scales hδ,eventually_atkinsonSourceCutoff_small hδ]
      with T hsupport hscale hcut
    intro G hlower hupper hquarter
    have hT : 1 ≤ T := by linarith [hsupport.1]
    have hT0 : 0 < T := by linarith
    obtain ⟨hG0,hlog0,hwidth,_⟩ := hsupport.2 G hlower
    have hG1 : 1 ≤ G := (Real.one_le_rpow hT (by norm_num : (0:ℝ) ≤ 1/4)).trans hquarter
    have hGS : G ≤ Real.sqrt T := hupper.trans (by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hT (by linarith))
    rw [atkinsonStationaryLeadingSum_eq_finite hT0 hG0 hlog0 hwidth]
    apply (hbound T G (Real.log T) hT hquarter hGS hscale.2.1 hwidth
      (atkinsonSourceCutoff T G (Real.log T)) (hcut G hlower)).trans
    have he := atkinsonStationary_cutoff_scale_le hT hG1 hGS hscale.2.1
      (q := 3/4+ε) (by linarith) (by linarith)
    have h := mul_le_mul_of_nonneg_left he hC.le
    norm_num only [show (3/4+ε-1/2 : ℝ) = 1/4+ε by ring] at h
    convert h using 1 <;> ring
  obtain ⟨B,hB⟩ := eventually_atTop.mp hev
  refine ⟨37*C,by positivity,max 40000 B,le_max_left _ _,?_⟩
  intro T G hT hlower hupper hquarter
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper hquarter

theorem exists_atkinsonStationary_finite_power_error {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingFiniteSum T G (Real.log T) (atkinsonSourceCutoff T G (Real.log T)) -
        atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤ C*T^(1/4+ε) := by
  let e : ℝ := min (ε/2) (1/4)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have hemax : e ≤ 1/4 := min_le_right _ _
  have heε : e ≤ ε/2 := min_le_left _ _
  have hη : 0 < ε-e := by linarith
  obtain ⟨C,hC,B,hB,hbound⟩ := exists_atkinsonStationary_finite_log_error hδ he hemax
  obtain ⟨D,hD⟩ := eventually_atTop.mp (eventually_const_log_pow_le_rpow 1 (by norm_num) 2 hη)
  refine ⟨C,hC,max B D,hB.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hTB : B ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hlog := hD T ((le_max_right _ _).trans hT)
  simp only [one_mul] at hlog
  apply (hbound T G hTB hlower hupper hquarter).trans
  calc
    _ ≤ C*T^(1/4+e)*T^(ε-e) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = C*T^(1/4+ε) := by
      rw [mul_assoc,← Real.rpow_add hT0]
      congr 2
      ring

theorem exists_atkinsonLeadingSum_sub_stationary_bound {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4 : ℝ) ≤ G →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*(G+T^(1/4+ε)) := by
  obtain ⟨A,hA,B,hB,hfinite⟩ := exists_atkinsonStationary_finite_power_error hδ hε
  obtain ⟨D,hD,E,_,htail⟩ := exists_atkinsonLeading_source_band_bound hδ
  refine ⟨A+D,by positivity,max B E,hB.trans (le_max_left _ _),?_⟩
  intro T G hT hlower hupper hquarter
  have hT0 : 0 < T := by linarith [hB.trans ((le_max_left B E).trans hT)]
  have hG : 0 < G := (Real.rpow_pos_of_pos hT0 δ).trans_le hlower
  have hf := hfinite T G ((le_max_left _ _).trans hT) hlower hupper hquarter
  have ht := htail T G ((le_max_right _ _).trans hT) hlower hupper
    (atkinsonSourceCutoff T G (Real.log T)) (atkinsonSourceCutoff_lower _ _ _)
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add ht hf).trans ?_)
  nlinarith [Real.rpow_pos_of_pos hT0 (1/4+ε)]

theorem exists_atkinsonLeadingSum_sub_stationary_above_fourthRoot {δ κ : ℝ}
    (hδ : 0 < δ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 40000 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T^δ ≤ G → G ≤ T^(1/2-δ) → T^(1/4+κ) ≤ G →
      ‖atkinsonLeadingSum T G (Real.log T)-atkinsonStationaryLeadingSum T G (Real.log T)‖ ≤
        C*G := by
  obtain ⟨C,hC,B,hB,hbound⟩ := exists_atkinsonLeadingSum_sub_stationary_bound hδ hκ
  refine ⟨2*C,by positivity,B,hB,?_⟩
  intro T G hT hlower hupper hquarter
  have hT1 : 1 ≤ T := by linarith
  have hq : T^(1/4 : ℝ) ≤ G :=
    (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : (1/4:ℝ) ≤ 1/4+κ)).trans hquarter
  apply (hbound T G hT hlower hupper hq).trans
  nlinarith

end TaoTrudgianYang2025
