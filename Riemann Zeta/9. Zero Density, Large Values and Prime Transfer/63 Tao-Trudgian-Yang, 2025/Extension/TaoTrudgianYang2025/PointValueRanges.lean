import TaoTrudgianYang2025.PointValueGrowth

/-!
# Uniform high-value ranges for the actual critical-line zeta function

The proved pointwise growth supplies the upper amplitude condition.
The lower amplitude condition and logarithmic factors are absorbed with
explicit positive exponent gaps. The final theorem counts actual peaks
for every amplitude above H^(1/8+epsilon), without an upper-value premise.
-/

noncomputable section

open Filter RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem eventually_pointValue_source_lower_range {K η : ℝ}
    (hK : 0 < K) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+η) ≤
        (H^(1/8+η))^2 := by
  have hs := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := K*2^((1/4:ℝ)+η)) (a := 1/4+η) (b := 1/4+2*η)
    (by positivity) 2 (by linarith)
  filter_upwards [hs,eventually_gt_atTop (0:ℝ)] with H hs hH
  have hp : (H^(1/8+η))^2 = H^(1/4+2*η) := by
    rw [← Real.rpow_mul_natCast hH.le]
    congr 1
    norm_num
    ring
  rw [hp,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hH.le]
  nlinarith [hs]

theorem pointValue_count_mul_twelfth_identity {D H L V η : ℝ}
    (hV : 0 < V) :
    (D*H^η*(H*L^4/V^6+H^2*L^6/V^12))*V^12 =
      D*H^η*(H*L^4*V^6+H^2*L^6) := by
  field_simp

theorem pointValue_count_mul_twelfth_le_growth {D H L V η : ℝ}
    (hD : 0 ≤ D) (hH : 0 < H)
    (hV : 0 ≤ V) (hGrowth : V ≤ H^(1/6+η)) :
    D*H^η*(H*L^4*V^6+H^2*L^6) ≤
      D*L^4*H^(2+7*η)+D*L^6*H^(2+η) := by
  have hp : V^6 ≤ H^(1+6*η) := by
    have hh := pow_le_pow_left₀ hV hGrowth 6
    rw [← Real.rpow_mul_natCast hH.le] at hh
    convert hh using 1
    congr 1
    norm_num
    ring
  calc
    _ ≤ D*H^η*(H*L^4*H^(1+6*η)+H^2*L^6) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ H*L^4 by positivity)
      linarith
    _ = D*L^4*H^(2+7*η)+D*L^6*H^(2+η) := by
      have h1 : H^η*H*H^(1+6*η) = H^(2+7*η) := by
        calc
          H^η*H*H^(1+6*η) = H^(η+1)*H^(1+6*η) := by
            rw [Real.rpow_add hH η 1,Real.rpow_one]
          _ = H^(2+7*η) := by
            rw [← Real.rpow_add hH]
            congr 1
            ring
      have h2 : H^η*H^2 = H^(2+η) := by
        rw [← Real.rpow_two,← Real.rpow_add hH]
        congr 1
        ring
      calc
        _ = D*L^4*(H^η*H*H^(1+6*η))+D*L^6*(H^η*H^2) := by ring
        _ = _ := by rw [h1,h2]

theorem eventually_pointValue_high_budget {D η : ℝ}
    (hD : 0 < D) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      D*(Real.log (3*H))^4*H^(2+7*η) +
        D*(Real.log (3*H))^6*H^(2+η) ≤ H^(2+8*η) := by
  have h4 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 2*D) (a := 2+7*η) (b := 2+8*η)
    (by positivity) 4 (by linarith)
  have h6 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 2*D) (a := 2+η) (b := 2+8*η)
    (by positivity) 6 (by linarith)
  filter_upwards [h4,h6] with H h4 h6
  linarith

theorem exists_pointValue_twelfth_weighted_card_le
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ (H V : ℝ) (W : Finset ℝ),
      H₀ ≤ H → 0 < V → H^(1/8+ε) ≤ V →
      IsSeparated 1 W →
      (∀ t ∈ W, H ≤ t ∧ t ≤ 2*H) →
      (∀ t ∈ W, V ≤ zetaMomentCriticalNorm t) →
      (W.card:ℝ)*V^12 ≤ H^(2+ε) := by
  classical
  let η : ℝ := min (ε/16) (1/1000)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηUpper : η ≤ 1/48 := (min_le_right _ _).trans (by norm_num)
  have hηε : η ≤ ε := (min_le_left _ _).trans (by linarith)
  have h8η : 8*η ≤ ε := by have hh := min_le_left (ε/16) (1/1000:ℝ); dsimp only [η]; linarith
  obtain ⟨K,D,B,hK,hD,hB,hcount⟩ :=
    exists_pointValue_card_le_source_range
      (δ := (1/48:ℝ)) (κ := η) (ν := η)
      (by norm_num) (by norm_num) hη hη
  obtain ⟨B₁,hB₁,hGrowth⟩ := exists_zetaMomentCriticalNorm_lt_sixth_power hη
  have hlower := eventually_pointValue_source_lower_range hK hη
  have hupper := eventually_pointValue_sixth_power_source_range hK hη hηUpper
  have hbudget := eventually_pointValue_high_budget hD hη
  obtain ⟨B₂,hB₂⟩ := eventually_atTop.mp (hlower.and (hupper.and hbudget))
  refine ⟨max B (max B₁ B₂),le_max_of_le_left hB,?_⟩
  intro H V W hH hV hVlower hsep hrange hlarge
  have hHB : B ≤ H := (le_max_left _ _).trans hH
  have hHB₁ : B₁ ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHB₂ : B₂ ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith [hB.trans hHB]
  have hH1 : 1 ≤ H := by linarith [hB₁.trans hHB₁]
  obtain ⟨hl,hu,hb⟩ := hB₂ H hHB₂
  rcases W.eq_empty_or_nonempty with rfl | ⟨t,ht⟩
  · simp only [Finset.card_empty,Nat.cast_zero,zero_mul]
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
    (W.card:ℝ)*V^12 ≤
        (D*H^η*(H*(Real.log (3*H))^4/V^6+H^2*(Real.log (3*H))^6/V^12))*V^12 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = D*H^η*(H*(Real.log (3*H))^4*V^6+H^2*(Real.log (3*H))^6) :=
      pointValue_count_mul_twelfth_identity hV
    _ ≤ D*(Real.log (3*H))^4*H^(2+7*η)+D*(Real.log (3*H))^6*H^(2+η) :=
      pointValue_count_mul_twelfth_le_growth hD.le hH0 hV.le hVgrowth
    _ ≤ H^(2+8*η) := hb
    _ ≤ H^(2+ε) := Real.rpow_le_rpow_of_exponent_le hH1 (by linarith)

end TaoTrudgianYang2025
