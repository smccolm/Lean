import TaoTrudgianYang2025.SargosQuarticCoverGeometry

/-! Summation of the actual sextic rectangle moments over the finite source cover. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticSextic_cover_moment {M : ℕ}
    (hM : 2 ≤ M) {N Δ : ℝ} (hN : 0 < N) (hΔ : 0 < Δ) (hΔ₁ : Δ ≤ 1/2)
    (hscale : (M:ℝ) ≤ 4*Δ*N) :
    (∫⁻ x in Icc (1/(8*Δ)) (1/(4*Δ)),
      ∫⁻ y in Icc (-sargosQuarticParameterHeight N Δ) (sargosQuarticParameterHeight N Δ),
        ENNReal.ofReal ((sargosSlowQuarticMaximum M (fun _ => 1) x y
          (fun t => 4*y^2/x*t^6))^6)) ≤
      ENNReal.ofReal ((3840/Δ^2)*sargosWindowConstant 3 1916928*
        (Real.log M)^6*sargosSixthBaseMoment M) := by
  classical
  let A := 1/(8*Δ)
  let Y := sargosQuarticParameterHeight N Δ
  let ell := 2/(M:ℝ)^3
  let nx := sargosIntervalGridCount A 1
  let ny := sargosIntervalGridCount (2*Y) ell
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal
    ((sargosSlowQuarticMaximum M (fun _ => 1) p.1 p.2 (fun t => 4*p.2^2/p.1*t^6))^6)
  let B := 384*sargosWindowConstant 3 1916928*(Real.log M)^6*sargosSixthBaseMoment M
  have hMp : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hF : Measurable F := ((measurable_sargosQuarticSexticMaximum M).pow_const 6).ennreal_ofReal
  have hB : 0 ≤ B := by
    have hC := sargosWindowConstant_nonneg 3 (by norm_num : (0:ℝ) ≤ 1916928)
    have hI := sargosSixthBaseMoment_nonneg M
    dsimp [B]
    positivity
  let cells : ℕ × ℕ → Set (ℝ × ℝ) := fun p =>
    Icc (A+(p.1:ℝ)) (A+(p.1:ℝ)+1) ×ˢ
      Icc (-Y+(p.2:ℝ)*ell) (-Y+(p.2:ℝ)*ell+ell)
  have hcover : (Icc A (2*A) ×ˢ Icc (-Y) Y) ⊆
      ⋃ p ∈ (Finset.range nx).product (Finset.range ny), cells p := by
    simpa only [mul_one,show A+A = 2*A by ring,show -Y+2*Y = Y by ring] using
      (sargos_rectangle_grid_cover (a := A) (b := -Y) (L := A) (K := 2*Y)
        (by norm_num : (0:ℝ) < 1) (by positivity : 0 < ell))
  have hcell (p : ℕ × ℕ) (hp : p ∈ (Finset.range nx).product (Finset.range ny)) :
      (∫⁻ z in cells p, F z ∂((volume:Measure ℝ).prod volume)) ≤ ENNReal.ofReal B := by
    have hc : 1/(8*Δ) ≤ A+(p.1:ℝ) := by
      dsimp [A]
      have hn : (0:ℝ) ≤ p.1 := Nat.cast_nonneg _
      linarith only [hn]
    have hd := sargosQuarticVerticalGrid_corner hN hΔ hΔ₁ hMp hscale
      (Finset.mem_product.mp hp).2
    have hh := sargosQuarticSextic_rectangle_lintegral hM hΔ hΔ₁ hc hd
    simpa only [cells,← Measure.prod_restrict,lintegral_prod _ hF.aemeasurable] using hh
  have hu := sargos_lintegral_finset_cover_le ((volume:Measure ℝ).prod volume)
    ((Finset.range nx).product (Finset.range ny)) cells F hcover
  have hsum := Finset.sum_le_sum hcell
  have hcount : (nx:ℝ)*(ny:ℝ) ≤ 10/Δ^2 := by
    have hx := sargosQuarticHorizontalGrid_count hΔ hΔ₁
    have hy := sargosQuarticVerticalGrid_count hN hΔ hΔ₁ hMp hscale
    calc
      _ ≤ (2/Δ)*(5/Δ) := mul_le_mul hx hy (Nat.cast_nonneg _) (by positivity)
      _ = _ := by ring
  have hlast : (∑ p ∈ (Finset.range nx).product (Finset.range ny), ENNReal.ofReal B) ≤
      ENNReal.ofReal ((3840/Δ^2)*sargosWindowConstant 3 1916928*
        (Real.log M)^6*sargosSixthBaseMoment M) := by
    have hcard : ((Finset.range nx).product (Finset.range ny)).card = nx*ny := by
      rw [Finset.product_eq_sprod,Finset.card_product,Finset.card_range,Finset.card_range]
    rw [Finset.sum_const,hcard,nsmul_eq_mul,← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg (nx*ny)),Nat.cast_mul]
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_right hcount hB).trans_eq (by dsimp [B]; ring)
  have hout := (hu.trans hsum).trans hlast
  rw [← Measure.prod_restrict,lintegral_prod _ hF.aemeasurable] at hout
  have ha : 2*A = 1/(4*Δ) := by dsimp [A]; ring
  simpa only [ha] using hout

end TaoTrudgianYang2025
