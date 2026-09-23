import TaoTrudgianYang2025.SargosQuarticSexticBounds

/-! The actual frozen sextic phase satisfies Lemma 1 on every admissible rectangle. -/

noncomputable section

open Set GafniTao MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuarticFrozenSexticPhase_deriv_bound {Δ M c d x y t : ℝ}
    (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2) (hM : 0 < M)
    (hc : 1/(8*Δ) ≤ c) (hd : |d| ≤ 5/(Δ*M^3))
    (hx : x ∈ Icc c (c+1)) (hy : y ∈ Icc d (d+2/M^3))
    (ht : t ∈ Icc M (2*M)) :
    ‖24*(y^2/x-d^2/c)*t^5‖ ≤ 1916928/M := by
  have htpos : 0 < t := hM.trans_le ht.1
  have hcoef := sargosQuarticSextic_rectangle_coefficient hΔ hΔ₁ hM hc hd hx hy
  have ht5 := pow_le_pow_left₀ htpos.le ht.2 5
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 24),
    abs_of_nonneg (pow_nonneg htpos.le 5)]
  calc
    _ ≤ (24*(2496/M^6))*(2*M)^5 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by norm_num)) ht5
        (by positivity) (by positivity)
    _ = _ := by field_simp; ring

theorem sargosQuarticSextic_rectangle_upper_moment {M : ℕ}
    (hM : 2 ≤ M) {Δ c d : ℝ} (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2)
    (hc : 1/(8*Δ) ≤ c) (hd : |d| ≤ 5/(Δ*(M:ℝ)^3)) :
    sargosUpperIntegral
      ((volume.restrict (Icc c (c+1))).prod
        (volume.restrict (Icc d (d+2/(M:ℝ)^3))))
      (fun p : ℝ × ℝ => ENNReal.ofReal
        ((sargosSlowQuarticMaximum M (fun _ => 1) p.1 p.2
          (fun t => 4*p.2^2/p.1*t^6))^6)) ≤
      ENNReal.ofReal (384*sargosWindowConstant 3 1916928*
        (Real.log M)^6*sargosSixthBaseMoment M) := by
  have hMp : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hz : ∀ n ∈ sargosSourceInterval M, ‖sargosQuarticFrozenSexticCoeff c d n‖ ≤ 1 := by
    intro n hn
    rw [sargosQuarticFrozenSexticCoeff_norm]
  have hφ : ∀ x ∈ Icc c (c+1), ∀ y ∈ Icc d (d+2/(M:ℝ)^3),
      ∀ t ∈ Icc (M:ℝ) (2*M),
      HasDerivWithinAt (sargosQuarticFrozenSexticPhase c d x y)
        (24*(y^2/x-d^2/c)*t^5) (Icc (M:ℝ) (2*M)) t := by
    intro x hx y hy t ht
    exact (sargosQuarticFrozenSexticPhase_deriv c d x y t).hasDerivWithinAt
  have hφ' : ∀ x ∈ Icc c (c+1), ∀ y ∈ Icc d (d+2/(M:ℝ)^3),
      ∀ t ∈ Icc (M:ℝ) (2*M), ‖24*(y^2/x-d^2/c)*t^5‖ ≤ 1916928/(M:ℝ) := by
    intro x hx y hy t ht
    exact sargosQuarticFrozenSexticPhase_deriv_bound hΔ hΔ₁ hMp hc hd hx hy ht
  have hh := sargosSlowQuartic_upper_sixth_strip_reduction hM
    (sargosQuarticFrozenSexticCoeff c d) hz (by norm_num : (0:ℝ) ≤ 1916928)
    (by positivity : (0:ℝ) < 2/(M:ℝ)^3) c d
    (sargosQuarticFrozenSexticPhase c d) (fun x y t => 24*(y^2/x-d^2/c)*t^5) hφ hφ'
  simp_rw [sargosQuarticSexticMaximum_freeze M c d]
  convert hh using 1
  congr 1
  field_simp
  ring

end TaoTrudgianYang2025
