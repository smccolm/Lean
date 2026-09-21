import TaoTrudgianYang2025.PointValueWidth

/-!
# Pointwise critical-line growth from the actual peak count

A singleton at height H^(1/6+epsilon) would contradict the proved
occupancy-aware cardinality estimate. This derives the pointwise bound
from the actual local zeta source; no Weyl bound for zeta is assumed.
-/

noncomputable section

open Filter RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem eventually_const_height_log_pow_mul_rpow_le_rpow
    {C a b : ℝ} (hC : 0 ≤ C) (k : ℕ) (hab : a < b) :
    ∀ᶠ H : ℝ in atTop,
      C*(Real.log (3*H))^k*H^a ≤ H^b := by
  have hs := eventually_const_log_pow_le_rpow (C*2^k) (by positivity)
    k (sub_pos.mpr hab)
  filter_upwards [hs,eventually_ge_atTop (3:ℝ)] with H hs hH
  have hH0 : 0 < H := by linarith
  have hlog3 : Real.log 3 ≤ Real.log H :=
    Real.log_le_log (by norm_num) hH
  have hlog : Real.log (3*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 3*H)) hlog k) hC
  rw [mul_pow] at hp
  have hsmall : C*(Real.log (3*H))^k ≤ H^(b-a) := by
    exact hp.trans (by nlinarith [hs])
  calc
    C*(Real.log (3*H))^k*H^a ≤ H^(b-a)*H^a :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = H^b := by rw [← Real.rpow_add hH0]; congr 1; ring

theorem pointValue_sixth_power_count_identity {D L H η : ℝ}
    (hH : 0 < H) :
    D*H^η*(H*L^4/(H^(1/6+η))^6+H^2*L^6/(H^(1/6+η))^12) =
      D*L^4/H^(5*η)+D*L^6/H^(11*η) := by
  have h6 : (H^(1/6+η))^6 = H^η*H*H^(5*η) := by
    calc
      (H^(1/6+η))^6 = H^((1/6+η)*(6:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hH.le]
        norm_num
      _ = H^(η+1+5*η) := by congr 1; ring
      _ = H^η*H*H^(5*η) := by rw [Real.rpow_add hH,Real.rpow_add hH,Real.rpow_one]
  have h12 : (H^(1/6+η))^12 = H^η*H^2*H^(11*η) := by
    calc
      (H^(1/6+η))^12 = H^((1/6+η)*(12:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hH.le]
        norm_num
      _ = H^(η+2+11*η) := by congr 1; ring
      _ = H^η*H^2*H^(11*η) := by rw [Real.rpow_add hH,Real.rpow_add hH,Real.rpow_two]
  rw [h6,h12]
  field_simp

theorem eventually_pointValue_sixth_power_count_lt_one
    {D η : ℝ} (hD : 0 < D) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      D*H^η*(H*(Real.log (3*H))^4/(H^(1/6+η))^6 +
        H^2*(Real.log (3*H))^6/(H^(1/6+η))^12) < 1 := by
  have h4 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4*D) (a := 0) (b := 5*η) (by positivity) 4 (by linarith)
  have h6 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4*D) (a := 0) (b := 11*η) (by positivity) 6 (by linarith)
  filter_upwards [h4,h6,eventually_gt_atTop (0:ℝ)] with H h4 h6 hH
  rw [Real.rpow_zero,mul_one] at h4 h6
  have hfirst : D*(Real.log (3*H))^4/H^(5*η) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [h4])
  have hsecond : D*(Real.log (3*H))^6/H^(11*η) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [h6])
  rw [pointValue_sixth_power_count_identity hH]
  linarith

theorem eventually_pointValue_sixth_power_source_range
    {K η : ℝ} (hK : 0 < K) (hη : 0 < η) (hηUpper : η ≤ 1/48) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+(1/48:ℝ)) ≤
          (H^(1/6+η))^2 ∧
      (H^(1/6+η))^2 ≤
        K*(Real.log (3*H))^2*H^(1/2-(1/48:ℝ)) := by
  let q : ℝ := 1/4+(1/48:ℝ)
  let r : ℝ := 1/2-(1/48:ℝ)
  have hlower := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := K*2^q) (a := q) (b := 1/3+2*η) (by positivity) 2
    (by dsimp only [q]; linarith)
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (1/K)))
  filter_upwards [hlower,hlog,eventually_ge_atTop (3:ℝ)] with H hlower hlog hH
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hLmono : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log hH0 (by linarith)
  have hL1 : 1 ≤ Real.log (3*H) := ((le_max_left _ _).trans hlog).trans hLmono
  have hKL : 1 ≤ K*Real.log (3*H) := by
    have hr : 1/K ≤ Real.log (3*H) :=
      ((le_max_right _ _).trans hlog).trans hLmono
    have hp := (div_le_iff₀ hK).mp hr
    nlinarith
  have hKL2 : 1 ≤ K*(Real.log (3*H))^2 := by
    have hp := mul_le_mul_of_nonneg_right hL1 (by positivity : 0 ≤ K*Real.log (3*H))
    nlinarith
  have hp : (H^(1/6+η))^2 = H^(1/3+2*η) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    congr 1
    norm_num
    ring
  rw [hp]
  constructor
  · have htwo : (2*H)^q = 2^q*H^q :=
      Real.mul_rpow (by norm_num) hH0.le
    change K*(Real.log (3*H))^2*(2*H)^q ≤ _
    rw [htwo]
    nlinarith [hlower]
  · calc
      H^(1/3+2*η) ≤ H^r :=
        Real.rpow_le_rpow_of_exponent_le hH1 (by dsimp only [r]; linarith)
      _ ≤ K*(Real.log (3*H))^2*H^r := by
        have hh := mul_le_mul_of_nonneg_right hKL2 (by positivity : 0 ≤ H^r)
        simpa only [one_mul] using hh

theorem exists_zetaMomentCriticalNorm_lt_sixth_power
    {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H t : ℝ,
      H₀ ≤ H → H ≤ t → t ≤ 2*H →
      zetaMomentCriticalNorm t < H^(1/6+ε) := by
  let η : ℝ := min ε (1/48)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηUpper : η ≤ 1/48 := min_le_right _ _
  have hηε : η ≤ ε := min_le_left _ _
  obtain ⟨K,D,B,hK,hD,hB,hcount⟩ :=
    exists_pointValue_card_le_source_range
      (δ := (1/48:ℝ)) (κ := (1/48:ℝ)) (ν := η)
      (by norm_num) (by norm_num) (by norm_num) hη
  have hsmall := eventually_pointValue_sixth_power_count_lt_one hD hη
  have hsource := eventually_pointValue_sixth_power_source_range hK hη hηUpper
  have hevent : ∀ᶠ H : ℝ in atTop,
      B ≤ H ∧ ∀ t : ℝ, H ≤ t → t ≤ 2*H →
        zetaMomentCriticalNorm t < H^(1/6+η) := by
    filter_upwards [hsmall,hsource,eventually_ge_atTop B] with H hs hr hH
    refine ⟨hH,?_⟩
    intro t htlo hthi
    have hH0 : 0 < H := by linarith [hB.trans hH]
    by_contra hnot
    have hlarge : H^(1/6+η) ≤ zetaMomentCriticalNorm t := le_of_not_gt hnot
    have hsep : IsSeparated 1 ({t}:Finset ℝ) := by
      intro x hx y hy hxy
      have hx' := Finset.mem_singleton.mp hx
      have hy' := Finset.mem_singleton.mp hy
      exact (hxy (hx'.trans hy'.symm)).elim
    have hc := hcount H (H^(1/6+η)) {t} hH (by positivity)
      hr.1 hr.2 hsep (by simpa using And.intro htlo hthi) (by simpa using hlarge)
    norm_num only [Finset.card_singleton,Nat.cast_one] at hc
    linarith
  obtain ⟨B₁,hB₁⟩ := eventually_atTop.mp hevent
  refine ⟨max B B₁,le_max_of_le_left hB,?_⟩
  intro H t hH htlo hthi
  have hh := hB₁ H ((le_max_right _ _).trans hH)
  have hH1 : 1 ≤ H := by linarith [hB.trans hh.1]
  exact (hh.2 t htlo hthi).trans_le
    (Real.rpow_le_rpow_of_exponent_le hH1 (by linarith))

end TaoTrudgianYang2025
