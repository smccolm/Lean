import TaoTrudgianYang2025.SargosQuarticParameterMap

/-! Exact horizontal image and vertical source enclosure for the parameter substitution. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace TaoTrudgianYang2025

theorem sargosQuarticParameter_horizontal_mem {a b x : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    1/(4*x) ∈ Icc a b ↔ x ∈ Icc (1/(4*b)) (1/(4*a)) := by
  have hb : 0 < b := ha.trans_le hab
  constructor
  · intro hx
    have hxpos : 0 < x := by
      have hh : 0 < 1/(4*x) := ha.trans_le hx.1
      have hp := (one_div_pos.mp hh)
      linarith
    constructor
    · apply (div_le_iff₀ (by positivity : 0 < 4*b)).2
      have hh := (div_le_iff₀ (by positivity : 0 < 4*x)).mp hx.2
      nlinarith only [hh]
    · apply (le_div_iff₀ (by positivity : 0 < 4*a)).2
      have hh := (le_div_iff₀ (by positivity : 0 < 4*x)).mp hx.1
      nlinarith only [hh]
  · intro hx
    have hxpos : 0 < x := (by positivity : 0 < 1/(4*b)).trans_le hx.1
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < 4*x)).2
      have hh := (le_div_iff₀ (by positivity : 0 < 4*a)).mp hx.2
      nlinarith only [hh]
    · apply (div_le_iff₀ (by positivity : 0 < 4*x)).2
      have hh := (div_le_iff₀ (by positivity : 0 < 4*b)).mp hx.1
      nlinarith only [hh]

theorem sargosQuarticParameter_horizontal_image {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (fun x : ℝ => 1/(4*x)) '' Icc (1/(4*b)) (1/(4*a)) = Icc a b := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (sargosQuarticParameter_horizontal_mem ha hab).2 hx
  · intro hy
    have hypos : 0 < y := ha.trans_le hy.1
    have hi : 1/(4*(1/(4*y))) = y := by field_simp
    refine ⟨1/(4*y),?_,hi⟩
    apply (sargosQuarticParameter_horizontal_mem ha hab).1
    rwa [hi]

theorem sargosQuarticParameter_vertical_image {x : ℝ} (hx : 0 < x) (H : ℝ) :
    (fun y : ℝ => -y/(16*x^4)) '' Icc (-16*H*x^4) (16*H*x^4) =
      Icc (-H) H := by
  have hx4 : 0 < 16*x^4 := by positivity
  ext γ
  constructor
  · rintro ⟨y,hy,rfl⟩
    constructor
    · apply (le_div_iff₀ hx4).2
      nlinarith only [hy.2]
    · apply (div_le_iff₀ hx4).2
      nlinarith only [hy.1]
  · intro hγ
    refine ⟨-16*x^4*γ,?_,?_⟩
    · constructor
      · have hh := mul_le_mul_of_nonneg_left hγ.2 hx4.le
        nlinarith only [hh]
      · have hh := mul_le_mul_of_nonneg_left hγ.1 hx4.le
        nlinarith only [hh]
    · field_simp

theorem sargosQuarticParameter_jacobian_bound {Δ x : ℝ}
    (hΔ : 0 < Δ) (hx : 1/(8*Δ) ≤ x) :
    1/(64*x^6) ≤ 4096*Δ^6 := by
  have hxpos : 0 < x := (by positivity : 0 < 1/(8*Δ)).trans_le hx
  have hprod : 1 ≤ 8*Δ*x := by
    have hh := (div_le_iff₀ (by positivity : 0 < 8*Δ)).mp hx
    nlinarith only [hh]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) hprod 6
  apply (div_le_iff₀ (by positivity : 0 < 64*x^6)).2
  nlinarith only [hp]

end TaoTrudgianYang2025
