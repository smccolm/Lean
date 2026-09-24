import TaoTrudgianYang2025.ZetaReflectionUniformEntry

/-! Physical logarithmic-reflection scale comparisons with exact constants. -/

noncomputable section
open Complex Filter MeasureTheory Set
namespace TaoTrudgianYang2025

theorem reflection_scaled_height_bounds {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc T (2*T)) :
    T/(2*Real.pi) ≤ t/(2*Real.pi) ∧
      t/(2*Real.pi) ≤ T ∧ 0 < t/(2*Real.pi) := by
  have hp : 0 < 2*Real.pi := by positivity
  refine ⟨div_le_div_of_nonneg_right ht.1 hp.le,?_,div_pos (hT.trans_le ht.1) hp⟩
  apply (div_le_iff₀ hp).2
  calc
    t ≤ 2*T := ht.2
    _ = T*2 := by ring
    _ ≤ T*(2*Real.pi) := mul_le_mul_of_nonneg_left (by nlinarith [Real.pi_gt_three]) hT.le

theorem reflection_sqrt_source_comparison {N T t : ℝ}
    (hN : 0 ≤ N) (hT : 0 < T) (ht : t ∈ Icc T (2*T)) :
    N/Real.sqrt (t/(2*Real.pi)) ≤ Real.sqrt (2*Real.pi)*N/Real.sqrt T := by
  have hl := (reflection_scaled_height_bounds hT ht).2.2
  have hprod : T ≤ (2*Real.pi)*(t/(2*Real.pi)) := by
    have he : (2*Real.pi)*(t/(2*Real.pi)) = t := by field_simp
    rw [he]
    exact ht.1
  have hs := Real.sqrt_le_sqrt hprod
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi)] at hs
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hl) (Real.sqrt_pos.2 hT)).2
  nlinarith

theorem reflection_sqrt_lower_power {N T a : ℝ}
    (hN : 0 < N) (hT : N^a ≤ T) :
    N^(a/2) ≤ Real.sqrt T := by
  have he : Real.sqrt (N^a) = N^(a/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hN.le]
    congr 1
    ring
  simpa only [he] using Real.sqrt_le_sqrt hT

theorem reflection_sqrt_upper_power {N T b : ℝ}
    (hN : 0 < N) (hupper : T ≤ N^b) :
    Real.sqrt T ≤ N^(b/2) := by
  have he : Real.sqrt (N^b) = N^(b/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hN.le]
    congr 1
    ring
  simpa only [he] using Real.sqrt_le_sqrt hupper

theorem reflection_source_remainder_power {N T t a : ℝ}
    (hN : 0 < N) (hT : 0 < T) (ht : t ∈ Icc T (2*T)) (hscale : N^a ≤ T) :
    N/Real.sqrt (t/(2*Real.pi)) ≤ Real.sqrt (2*Real.pi)*N^(1-a/2) := by
  have hs := reflection_sqrt_lower_power hN hscale
  calc
    _ ≤ Real.sqrt (2*Real.pi)*N/Real.sqrt T := reflection_sqrt_source_comparison hN.le hT ht
    _ ≤ Real.sqrt (2*Real.pi)*N/N^(a/2) :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hN _) hs
    _ = _ := by rw [Real.rpow_sub hN,Real.rpow_one]; ring

end TaoTrudgianYang2025
