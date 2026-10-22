import Dubon2026.SourceCellSixArcRegion
import Dubon2026.SourceCellBoundaryGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> paired analytic cell dissection.
The exact six-arc radial rectangle has prescribed split side segments,
endpoints, smooth pieces and segment-valued subarcs. These properties feed
ordinary grid-cell construction and neighboring-cell pairing.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
open Real RectRadial

private theorem r6_arc0 (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R 0 (cornerAngle (x₁ - p.re) (y₁ - p.im))
      {z : ℂ | z.re = x₁ ∧ z.im ∈ Set.Icc p.im y₁} ⟨x₁, p.im⟩ ⟨x₁, y₁⟩ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hθ0 := cornerAngle_pos ha hc
  have hθ2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (y₁ - p.im)
  have hmem : ∀ φ ∈ Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im)),
      φ ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    fun φ hφ => ⟨by linarith [hφ.1, Real.pi_pos], by linarith [hφ.2, hθ2]⟩
  have hrφ : ∀ φ ∈ Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im)),
      R.r φ = (Real.cos φ / (x₁ - p.re))⁻¹ := by
    intro φ hφ
    rw [hr]
    exact collapse_arc1 ha hb hc hd hφ.1 hφ.2
  have hre : ∀ φ ∈ Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im)), (R.loop φ).re = x₁ :=
    fun φ hφ =>
      (r6_re_cos hq (Real.cos_pos_of_mem_Ioo (hmem φ hφ)).ne' (hrφ φ hφ)).trans (by ring)
  have him : ∀ φ ∈ Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im)),
      (R.loop φ).im = p.im + (x₁ - p.re) * Real.tan φ :=
    fun φ hφ => r6_im_cos hq (hrφ φ hφ)
  have hg : StrictMonoOn (fun φ => p.im + (x₁ - p.re) * Real.tan φ)
      (Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im))) := by
    intro φ hφ ψ hψ hlt
    have h1 : Real.tan φ < Real.tan ψ := Real.strictMonoOn_tan (hmem φ hφ) (hmem ψ hψ) hlt
    have h2 := mul_lt_mul_of_pos_left h1 ha
    show p.im + (x₁ - p.re) * Real.tan φ < p.im + (x₁ - p.re) * Real.tan ψ
    linarith [h2]
  have hgu : p.im + (x₁ - p.re) * Real.tan 0 = p.im := by
    rw [Real.tan_zero, mul_zero, add_zero]
  have hgv : p.im + (x₁ - p.re) * Real.tan (cornerAngle (x₁ - p.re) (y₁ - p.im)) = y₁ := by
    rw [tan_cornerAngle, mul_div_cancel₀ _ ha.ne']
    ring
  exact r6_vert_arc R hθ0.le hre him (r6_image_mono hθ0.le (r6_contOn_of_im R him) hg hgu hgv)
    (Or.inl hg) hgu hgv

private theorem r6_arc1 (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R (cornerAngle (x₁ - p.re) (y₁ - p.im)) (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      {z : ℂ | z.im = y₁ ∧ z.re ∈ Set.Icc x₀ x₁} ⟨x₁, y₁⟩ ⟨x₀, y₁⟩ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hac0 := cornerAngle_pos ha hc
  have hac2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (y₁ - p.im)
  have hbc0 := cornerAngle_pos hb hc
  have hbc2 := cornerAngle_lt_pi_div_two (p.re - x₀) (y₁ - p.im)
  have huv : cornerAngle (x₁ - p.re) (y₁ - p.im) ≤ π - cornerAngle (p.re - x₀) (y₁ - p.im) := by
    linarith [hac2, hbc2]
  have hsin : ∀ φ ∈ Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im))
      (π - cornerAngle (p.re - x₀) (y₁ - p.im)), 0 < Real.sin φ :=
    fun φ hφ => Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1, hac0]) (by linarith [hφ.2, hbc0])
  have hrφ : ∀ φ ∈ Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im))
      (π - cornerAngle (p.re - x₀) (y₁ - p.im)), R.r φ = (Real.sin φ / (y₁ - p.im))⁻¹ := by
    intro φ hφ
    rw [hr]
    exact collapse_arc2 ha hb hc hd hφ.1 hφ.2
  have him : ∀ φ ∈ Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im))
      (π - cornerAngle (p.re - x₀) (y₁ - p.im)), (R.loop φ).im = y₁ :=
    fun φ hφ => (r6_im_sin hq (hsin φ hφ).ne' (hrφ φ hφ)).trans (by ring)
  have hre : ∀ φ ∈ Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im))
      (π - cornerAngle (p.re - x₀) (y₁ - p.im)),
      (R.loop φ).re = p.re + (y₁ - p.im) * (Real.cos φ / Real.sin φ) :=
    fun φ hφ => r6_re_sin hq (hrφ φ hφ)
  have hg : StrictAntiOn (fun φ => p.re + (y₁ - p.im) * (Real.cos φ / Real.sin φ))
      (Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im)) (π - cornerAngle (p.re - x₀) (y₁ - p.im))) := by
    intro φ hφ ψ hψ hlt
    have h1 : Real.cos ψ / Real.sin ψ < Real.cos φ / Real.sin φ :=
      r6_cot_lt_cot (by linarith [hφ.1, hac0]) (by linarith [hψ.2, hbc0]) hlt
    have h2 := mul_lt_mul_of_pos_left h1 hc
    show p.re + (y₁ - p.im) * (Real.cos ψ / Real.sin ψ)
      < p.re + (y₁ - p.im) * (Real.cos φ / Real.sin φ)
    linarith [h2]
  have hgu : p.re + (y₁ - p.im) * (Real.cos (cornerAngle (x₁ - p.re) (y₁ - p.im))
      / Real.sin (cornerAngle (x₁ - p.re) (y₁ - p.im))) = x₁ := by
    rw [cot_cornerAngle, mul_div_cancel₀ _ hc.ne']
    ring
  have hgv : p.re + (y₁ - p.im) * (Real.cos (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      / Real.sin (π - cornerAngle (p.re - x₀) (y₁ - p.im))) = x₀ := by
    rw [r6_cot_pi_sub, cot_cornerAngle, mul_neg, mul_div_cancel₀ _ hc.ne']
    ring
  exact r6_horiz_arc R huv him hre (r6_image_anti huv (r6_contOn_of_re R hre) hg hgu hgv)
    (Or.inr hg) hgu hgv

private theorem r6_arc2 (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R (π - cornerAngle (p.re - x₀) (y₁ - p.im)) (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
      {z : ℂ | z.re = x₀ ∧ z.im ∈ Set.Icc yL y₁} ⟨x₀, y₁⟩ ⟨x₀, yL⟩ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hbc2 := cornerAngle_lt_pi_div_two (p.re - x₀) (y₁ - p.im)
  have hbd2 := cornerAngle_lt_pi_div_two (p.re - x₀) (p.im - y₀)
  have hα₁ := neg_cornerAngle_lt_leftAngle hx₀ hL₁
  have hα₂ := leftAngle_lt_cornerAngle hx₀ hL₀
  have huv : π - cornerAngle (p.re - x₀) (y₁ - p.im)
      ≤ π + Real.arctan ((p.im - yL) / (p.re - x₀)) := by linarith [hα₁]
  have hmem : ∀ φ ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      (π + Real.arctan ((p.im - yL) / (p.re - x₀))), φ ∈ Set.Ioo (π / 2) (3 * π / 2) :=
    fun φ hφ => ⟨by linarith [hφ.1, hbc2], by linarith [hφ.2, hα₂, hbd2]⟩
  have hcos : ∀ φ ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      (π + Real.arctan ((p.im - yL) / (p.re - x₀))), Real.cos φ ≠ 0 :=
    fun φ hφ => (Real.cos_neg_of_pi_div_two_lt_of_lt (hmem φ hφ).1
      (by linarith [(hmem φ hφ).2])).ne
  have hrφ : ∀ φ ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      (π + Real.arctan ((p.im - yL) / (p.re - x₀))),
      R.r φ = (-Real.cos φ / (p.re - x₀))⁻¹ := by
    intro φ hφ
    rw [hr]
    exact collapse_arc3 ha hb hc hd hφ.1 (by linarith [hφ.2, hα₂])
  have hre : ∀ φ ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      (π + Real.arctan ((p.im - yL) / (p.re - x₀))), (R.loop φ).re = x₀ :=
    fun φ hφ => (r6_re_negcos hq (hcos φ hφ) (hrφ φ hφ)).trans (by ring)
  have him : ∀ φ ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
      (π + Real.arctan ((p.im - yL) / (p.re - x₀))),
      (R.loop φ).im = p.im - (p.re - x₀) * Real.tan φ :=
    fun φ hφ => r6_im_negcos hq (hrφ φ hφ)
  have hg : StrictAntiOn (fun φ => p.im - (p.re - x₀) * Real.tan φ)
      (Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
        (π + Real.arctan ((p.im - yL) / (p.re - x₀)))) := by
    intro φ hφ ψ hψ hlt
    have h1 : Real.tan φ < Real.tan ψ := r6_tan_strictMonoOn_shifted (hmem φ hφ) (hmem ψ hψ) hlt
    have h2 := mul_lt_mul_of_pos_left h1 hb
    show p.im - (p.re - x₀) * Real.tan ψ < p.im - (p.re - x₀) * Real.tan φ
    linarith [h2]
  have hgu : p.im - (p.re - x₀) * Real.tan (π - cornerAngle (p.re - x₀) (y₁ - p.im)) = y₁ := by
    rw [Real.tan_pi_sub, tan_cornerAngle, mul_neg, mul_div_cancel₀ _ hb.ne']
    ring
  have hgv : p.im - (p.re - x₀) * Real.tan (π + Real.arctan ((p.im - yL) / (p.re - x₀))) = yL := by
    rw [r6_tan_pi_add, Real.tan_arctan, mul_div_cancel₀ _ hb.ne']
    ring
  exact r6_vert_arc R huv hre him (r6_image_anti huv (r6_contOn_of_im R him) hg hgu hgv)
    (Or.inr hg) hgu hgv

private theorem r6_arc3 (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R (π + Real.arctan ((p.im - yL) / (p.re - x₀))) (π + cornerAngle (p.re - x₀) (p.im - y₀))
      {z : ℂ | z.re = x₀ ∧ z.im ∈ Set.Icc y₀ yL} ⟨x₀, yL⟩ ⟨x₀, y₀⟩ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hbc2 := cornerAngle_lt_pi_div_two (p.re - x₀) (y₁ - p.im)
  have hbd2 := cornerAngle_lt_pi_div_two (p.re - x₀) (p.im - y₀)
  have hα₁ := neg_cornerAngle_lt_leftAngle hx₀ hL₁
  have hα₂ := leftAngle_lt_cornerAngle hx₀ hL₀
  have huv : π + Real.arctan ((p.im - yL) / (p.re - x₀))
      ≤ π + cornerAngle (p.re - x₀) (p.im - y₀) := by linarith [hα₂]
  have hmem : ∀ φ ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
      (π + cornerAngle (p.re - x₀) (p.im - y₀)), φ ∈ Set.Ioo (π / 2) (3 * π / 2) :=
    fun φ hφ => ⟨by linarith [hφ.1, hα₁, hbc2], by linarith [hφ.2, hbd2]⟩
  have hcos : ∀ φ ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
      (π + cornerAngle (p.re - x₀) (p.im - y₀)), Real.cos φ ≠ 0 :=
    fun φ hφ => (Real.cos_neg_of_pi_div_two_lt_of_lt (hmem φ hφ).1
      (by linarith [(hmem φ hφ).2])).ne
  have hrφ : ∀ φ ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
      (π + cornerAngle (p.re - x₀) (p.im - y₀)), R.r φ = (-Real.cos φ / (p.re - x₀))⁻¹ := by
    intro φ hφ
    rw [hr]
    exact collapse_arc3 ha hb hc hd (by linarith [hφ.1, hα₁]) hφ.2
  have hre : ∀ φ ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
      (π + cornerAngle (p.re - x₀) (p.im - y₀)), (R.loop φ).re = x₀ :=
    fun φ hφ => (r6_re_negcos hq (hcos φ hφ) (hrφ φ hφ)).trans (by ring)
  have him : ∀ φ ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
      (π + cornerAngle (p.re - x₀) (p.im - y₀)),
      (R.loop φ).im = p.im - (p.re - x₀) * Real.tan φ :=
    fun φ hφ => r6_im_negcos hq (hrφ φ hφ)
  have hg : StrictAntiOn (fun φ => p.im - (p.re - x₀) * Real.tan φ)
      (Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
        (π + cornerAngle (p.re - x₀) (p.im - y₀))) := by
    intro φ hφ ψ hψ hlt
    have h1 : Real.tan φ < Real.tan ψ := r6_tan_strictMonoOn_shifted (hmem φ hφ) (hmem ψ hψ) hlt
    have h2 := mul_lt_mul_of_pos_left h1 hb
    show p.im - (p.re - x₀) * Real.tan ψ < p.im - (p.re - x₀) * Real.tan φ
    linarith [h2]
  have hgu : p.im - (p.re - x₀) * Real.tan (π + Real.arctan ((p.im - yL) / (p.re - x₀))) = yL := by
    rw [r6_tan_pi_add, Real.tan_arctan, mul_div_cancel₀ _ hb.ne']
    ring
  have hgv : p.im - (p.re - x₀) * Real.tan (π + cornerAngle (p.re - x₀) (p.im - y₀)) = y₀ := by
    rw [r6_tan_pi_add, tan_cornerAngle, mul_div_cancel₀ _ hb.ne']
    ring
  exact r6_vert_arc R huv hre him (r6_image_anti huv (r6_contOn_of_im R him) hg hgu hgv)
    (Or.inr hg) hgu hgv

private theorem r6_arc4 (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R (π + cornerAngle (p.re - x₀) (p.im - y₀)) (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀))
      {z : ℂ | z.im = y₀ ∧ z.re ∈ Set.Icc x₀ x₁} ⟨x₀, y₀⟩ ⟨x₁, y₀⟩ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hbd0 := cornerAngle_pos hb hd
  have hbd2 := cornerAngle_lt_pi_div_two (p.re - x₀) (p.im - y₀)
  have had0 := cornerAngle_pos ha hd
  have had2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (p.im - y₀)
  have huv : π + cornerAngle (p.re - x₀) (p.im - y₀)
      ≤ 2 * π - cornerAngle (x₁ - p.re) (p.im - y₀) := by linarith [hbd2, had2]
  have hsin : ∀ φ ∈ Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
      (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)), Real.sin φ < 0 := by
    intro φ hφ
    have h1 : 0 < Real.sin (φ - π) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hφ.1, hbd0]) (by linarith [hφ.2, had0])
    rw [Real.sin_sub_pi] at h1
    linarith [h1]
  have hrφ : ∀ φ ∈ Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
      (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)), R.r φ = (-Real.sin φ / (p.im - y₀))⁻¹ := by
    intro φ hφ
    rw [hr]
    exact collapse_arc4 ha hb hc hd hφ.1 hφ.2
  have him : ∀ φ ∈ Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
      (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)), (R.loop φ).im = y₀ :=
    fun φ hφ => (r6_im_negsin hq (hsin φ hφ).ne (hrφ φ hφ)).trans (by ring)
  have hre : ∀ φ ∈ Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
      (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)),
      (R.loop φ).re = p.re - (p.im - y₀) * (Real.cos φ / Real.sin φ) :=
    fun φ hφ => r6_re_negsin hq (hrφ φ hφ)
  have hg : StrictMonoOn (fun φ => p.re - (p.im - y₀) * (Real.cos φ / Real.sin φ))
      (Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
        (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀))) := by
    intro φ hφ ψ hψ hlt
    have h0 : 0 < φ - π := by linarith [hφ.1, hbd0]
    have hπ' : ψ - π < π := by linarith [hψ.2, had0]
    have h1 := r6_cot_lt_cot h0 hπ' (by linarith [hlt])
    rw [r6_cot_sub_pi ψ, r6_cot_sub_pi φ] at h1
    have h2 := mul_lt_mul_of_pos_left h1 hd
    show p.re - (p.im - y₀) * (Real.cos φ / Real.sin φ)
      < p.re - (p.im - y₀) * (Real.cos ψ / Real.sin ψ)
    linarith [h2]
  have hgu : p.re - (p.im - y₀) * (Real.cos (π + cornerAngle (p.re - x₀) (p.im - y₀))
      / Real.sin (π + cornerAngle (p.re - x₀) (p.im - y₀))) = x₀ := by
    rw [r6_cot_pi_add, cot_cornerAngle, mul_div_cancel₀ _ hd.ne']
    ring
  have hgv : p.re - (p.im - y₀) * (Real.cos (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀))
      / Real.sin (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀))) = x₁ := by
    rw [r6_cot_two_pi_sub, cot_cornerAngle, mul_neg, mul_div_cancel₀ _ hd.ne']
    ring
  exact r6_horiz_arc R huv him hre (r6_image_mono huv (r6_contOn_of_re R hre) hg hgu hgv)
    (Or.inl hg) hgu hgv

private theorem r6_arc5 (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π)
      {z : ℂ | z.re = x₁ ∧ z.im ∈ Set.Icc y₀ p.im} ⟨x₁, y₀⟩ ⟨x₁, p.im⟩ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have had0 := cornerAngle_pos ha hd
  have had2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (p.im - y₀)
  have huv : 2 * π - cornerAngle (x₁ - p.re) (p.im - y₀) ≤ 2 * π := by linarith [had0]
  have hmem : ∀ φ ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π),
      φ ∈ Set.Ioo (3 * π / 2) (5 * π / 2) :=
    fun φ hφ => ⟨by linarith [hφ.1, had2], by linarith [hφ.2, Real.pi_pos]⟩
  have hcos : ∀ φ ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π),
      Real.cos φ ≠ 0 := by
    intro φ hφ
    have h1 : 0 < Real.cos (φ - 2 * π) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hφ.1, had2], by linarith [hφ.2, Real.pi_pos]⟩
    rw [Real.cos_sub_two_pi] at h1
    exact h1.ne'
  have hrφ : ∀ φ ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π),
      R.r φ = (Real.cos φ / (x₁ - p.re))⁻¹ := by
    intro φ hφ
    rw [hr]
    exact collapse_arc5 ha hb hc hd hφ.1 hφ.2
  have hre : ∀ φ ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π),
      (R.loop φ).re = x₁ :=
    fun φ hφ => (r6_re_cos hq (hcos φ hφ) (hrφ φ hφ)).trans (by ring)
  have him : ∀ φ ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π),
      (R.loop φ).im = p.im + (x₁ - p.re) * Real.tan φ :=
    fun φ hφ => r6_im_cos hq (hrφ φ hφ)
  have hg : StrictMonoOn (fun φ => p.im + (x₁ - p.re) * Real.tan φ)
      (Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π)) := by
    intro φ hφ ψ hψ hlt
    have h1 : Real.tan φ < Real.tan ψ :=
      r6_tan_strictMonoOn_shifted2 (hmem φ hφ) (hmem ψ hψ) hlt
    have h2 := mul_lt_mul_of_pos_left h1 ha
    show p.im + (x₁ - p.re) * Real.tan φ < p.im + (x₁ - p.re) * Real.tan ψ
    linarith [h2]
  have hgu : p.im + (x₁ - p.re) * Real.tan (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) = y₀ := by
    rw [r6_tan_two_pi_sub, tan_cornerAngle, mul_neg, mul_div_cancel₀ _ ha.ne']
    ring
  have hgv : p.im + (x₁ - p.re) * Real.tan (2 * π) = p.im := by
    rw [r6_tan_two_pi, mul_zero, add_zero]
  exact r6_vert_arc R huv hre him (r6_image_mono huv (r6_contOn_of_im R him) hg hgu hgv)
    (Or.inl hg) hgu hgv

private theorem r6_arcs (R : RadialRegion) {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (hq : R.q = p) (hr : R.r = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)) :
    ArcData R 0 (cornerAngle (x₁ - p.re) (y₁ - p.im))
        (side x₀ x₁ y₀ y₁ p yL 0) (corner x₀ x₁ y₀ y₁ p yL 0) (corner x₀ x₁ y₀ y₁ p yL 1) ∧
      ArcData R (cornerAngle (x₁ - p.re) (y₁ - p.im)) (π - cornerAngle (p.re - x₀) (y₁ - p.im))
        (side x₀ x₁ y₀ y₁ p yL 1) (corner x₀ x₁ y₀ y₁ p yL 1) (corner x₀ x₁ y₀ y₁ p yL 2) ∧
      ArcData R (π - cornerAngle (p.re - x₀) (y₁ - p.im))
        (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
        (side x₀ x₁ y₀ y₁ p yL 2) (corner x₀ x₁ y₀ y₁ p yL 2) (corner x₀ x₁ y₀ y₁ p yL 3) ∧
      ArcData R (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
        (π + cornerAngle (p.re - x₀) (p.im - y₀))
        (side x₀ x₁ y₀ y₁ p yL 3) (corner x₀ x₁ y₀ y₁ p yL 3) (corner x₀ x₁ y₀ y₁ p yL 4) ∧
      ArcData R (π + cornerAngle (p.re - x₀) (p.im - y₀))
        (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀))
        (side x₀ x₁ y₀ y₁ p yL 4) (corner x₀ x₁ y₀ y₁ p yL 4) (corner x₀ x₁ y₀ y₁ p yL 5) ∧
      ArcData R (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π)
        (side x₀ x₁ y₀ y₁ p yL 5) (corner x₀ x₁ y₀ y₁ p yL 5) (corner x₀ x₁ y₀ y₁ p yL 6) :=
  ⟨r6_arc0 R hx₀ hx₁ hy₀ hy₁ hq hr, r6_arc1 R hx₀ hx₁ hy₀ hy₁ hq hr,
    r6_arc2 R hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ hq hr, r6_arc3 R hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ hq hr,
    r6_arc4 R hx₀ hx₁ hy₀ hy₁ hq hr, r6_arc5 R hx₀ hx₁ hy₀ hy₁ hq hr⟩

theorem arcSet_eq (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcSet k
      = side x₀ x₁ y₀ y₁ p yL k.val := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    r6_arcs (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ rfl rfl
  obtain ⟨n, hn⟩ := k
  have hn6 : n < 6 := hn
  interval_cases n
  · exact h0.image_eq
  · exact h1.image_eq
  · exact h2.image_eq
  · exact h3.image_eq
  · exact h4.image_eq
  · exact h5.image_eq

theorem injOn_loop_arcIcc (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) :
    Set.InjOn (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop
      ((rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    r6_arcs (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ rfl rfl
  obtain ⟨n, hn⟩ := k
  have hn6 : n < 6 := hn
  interval_cases n
  · exact h0.injOn
  · exact h1.injOn
  · exact h2.injOn
  · exact h3.injOn
  · exact h4.injOn
  · exact h5.injOn

theorem loop_φs (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin ((rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N + 1)) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop
        ((rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).φs k)
      = corner x₀ x₁ y₀ y₁ p yL k.val := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    r6_arcs (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ rfl rfl
  obtain ⟨n, hn⟩ := k
  have hn7 : n < 7 := hn
  interval_cases n
  · exact h0.loop_left
  · exact h0.loop_right
  · exact h1.loop_right
  · exact h2.loop_right
  · exact h3.loop_right
  · exact h4.loop_right
  · exact h5.loop_right

theorem image_loop_Icc (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) {t₁ t₂ : ℝ}
    (h₁ : t₁ ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k)
    (h₂ : t₂ ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k) (h : t₁ ≤ t₂) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop '' Set.Icc t₁ t₂
      = segment ℝ ((rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop t₁)
          ((rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop t₂) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ :=
    r6_arcs (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ rfl rfl
  obtain ⟨n, hn⟩ := k
  have hn6 : n < 6 := hn
  interval_cases n
  · exact h0.image_sub t₁ t₂ h₁ h₂ h
  · exact h1.image_sub t₁ t₂ h₁ h₂ h
  · exact h2.image_sub t₁ t₂ h₁ h₂ h
  · exact h3.image_sub t₁ t₂ h₁ h₂ h
  · exact h4.image_sub t₁ t₂ h₁ h₂ h
  · exact h5.image_sub t₁ t₂ h₁ h₂ h


end Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
