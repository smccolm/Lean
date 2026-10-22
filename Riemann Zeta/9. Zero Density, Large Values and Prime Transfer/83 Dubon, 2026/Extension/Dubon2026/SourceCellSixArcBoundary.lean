import Dubon2026.SourceCellSixArcSides
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

/- As constructed below. -/
/-- The argument represented in the half-open interval from zero to one full turn. -/
noncomputable def angle₀ (w : ℂ) : ℝ :=
  if Complex.arg w < 0 then Complex.arg w + 2 * Real.pi else Complex.arg w

theorem angle₀_mem (w : ℂ) : 0 ≤ angle₀ w ∧ angle₀ w < 2 * Real.pi := by
  have h1 := Complex.neg_pi_lt_arg w
  have h2 := Complex.arg_le_pi w
  have hπ := Real.pi_pos
  by_cases h : Complex.arg w < 0
  · rw [angle₀, if_pos h]
    exact ⟨by linarith [h1, hπ], by linarith [h]⟩
  · rw [angle₀, if_neg h]
    exact ⟨not_lt.mp h, by linarith [h2, hπ]⟩

theorem loop_angle₀_of_norm_eq (R : RadialRegion) {p z : ℂ} (hq : R.q = p)
    (hnorm : ‖z - p‖ = R.r (Complex.arg (z - p))) : R.loop (angle₀ (z - p)) = z := by
  have hr : R.r (angle₀ (z - p)) = R.r (Complex.arg (z - p)) := by
    by_cases h : Complex.arg (z - p) < 0
    · rw [angle₀, if_pos h]
      exact R.hper _
    · rw [angle₀, if_neg h]
  have hcos : Real.cos (angle₀ (z - p)) = Real.cos (Complex.arg (z - p)) := by
    by_cases h : Complex.arg (z - p) < 0
    · rw [angle₀, if_pos h]
      exact Real.cos_add_two_pi _
    · rw [angle₀, if_neg h]
  have hsin : Real.sin (angle₀ (z - p)) = Real.sin (Complex.arg (z - p)) := by
    by_cases h : Complex.arg (z - p) < 0
    · rw [angle₀, if_pos h]
      exact Real.sin_add_two_pi _
    · rw [angle₀, if_neg h]
  apply Complex.ext
  · rw [r6_loop_re, hq, hr, hcos, ← hnorm, Complex.norm_mul_cos_arg, Complex.sub_re]
    ring
  · rw [r6_loop_im, hq, hr, hsin, ← hnorm, Complex.norm_mul_sin_arg, Complex.sub_im]
    ring

theorem loop_angle₀ (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) {z : ℂ}
    (hz : z ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).K)
    (hz' : z ∉ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).Kint) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop (angle₀ (z - p)) = z := by
  have h1 : ‖z - p‖ ≤ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r
      (Complex.arg (z - p)) := hz
  have h2 : ¬ ‖z - p‖ < (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r
      (Complex.arg (z - p)) := hz'
  exact loop_angle₀_of_norm_eq _ (rectRegion6_q x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁)
    (le_antisymm h1 (not_lt.mp h2))

theorem r_eq_of_val_right (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N)
    (hk : k.val = 0 ∨ k.val = 5) :
    ∀ t ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k,
      (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r t
        = (Real.cos t / (x₁ - p.re))⁻¹ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  obtain ⟨n, hn⟩ := k
  rcases hk with hk | hk
  · obtain rfl : n = 0 := hk
    intro t ht
    have ht' : t ∈ Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im)) := ht
    exact collapse_arc1 ha hb hc hd ht'.1 ht'.2
  · obtain rfl : n = 5 := hk
    intro t ht
    have ht' : t ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π) := ht
    exact collapse_arc5 ha hb hc hd ht'.1 ht'.2

theorem r_eq_of_val_top (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) (hk : k.val = 1) :
    ∀ t ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k,
      (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r t
        = (Real.sin t / (y₁ - p.im))⁻¹ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  obtain ⟨n, hn⟩ := k
  obtain rfl : n = 1 := hk
  intro t ht
  have ht' : t ∈ Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im))
      (π - cornerAngle (p.re - x₀) (y₁ - p.im)) := ht
  exact collapse_arc2 ha hb hc hd ht'.1 ht'.2

theorem r_eq_of_val_left (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N)
    (hk : k.val = 2 ∨ k.val = 3) :
    ∀ t ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k,
      (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r t
        = (-Real.cos t / (p.re - x₀))⁻¹ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hα₁ := neg_cornerAngle_lt_leftAngle hx₀ hL₁
  have hα₂ := leftAngle_lt_cornerAngle hx₀ hL₀
  obtain ⟨n, hn⟩ := k
  rcases hk with hk | hk
  · obtain rfl : n = 2 := hk
    intro t ht
    have ht' : t ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
        (π + Real.arctan ((p.im - yL) / (p.re - x₀))) := ht
    exact collapse_arc3 ha hb hc hd ht'.1 (by linarith [ht'.2, hα₂])
  · obtain rfl : n = 3 := hk
    intro t ht
    have ht' : t ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
        (π + cornerAngle (p.re - x₀) (p.im - y₀)) := ht
    exact collapse_arc3 ha hb hc hd (by linarith [ht'.1, hα₁]) ht'.2

theorem r_eq_of_val_bottom (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) (hk : k.val = 4) :
    ∀ t ∈ (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k,
      (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r t
        = (-Real.sin t / (p.im - y₀))⁻¹ := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  obtain ⟨n, hn⟩ := k
  obtain rfl : n = 4 := hk
  intro t ht
  have ht' : t ∈ Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
      (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) := ht
  exact collapse_arc4 ha hb hc hd ht'.1 ht'.2

theorem arcIcc_subset_of_val_0 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) (hk : k.val = 0) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k
      ⊆ Set.Ico 0 (Real.pi / 2) := by
  have hac2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (y₁ - p.im)
  obtain ⟨n, hn⟩ := k
  obtain rfl : n = 0 := hk
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) (cornerAngle (x₁ - p.re) (y₁ - p.im)) := ht
  exact ⟨ht'.1, by linarith [ht'.2, hac2]⟩

theorem arcIcc_subset_of_val_1 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) (hk : k.val = 1) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k ⊆ Set.Ioo 0 Real.pi := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hac0 := cornerAngle_pos ha hc
  have hbc0 := cornerAngle_pos hb hc
  obtain ⟨n, hn⟩ := k
  obtain rfl : n = 1 := hk
  intro t ht
  have ht' : t ∈ Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im))
      (π - cornerAngle (p.re - x₀) (y₁ - p.im)) := ht
  exact ⟨by linarith [ht'.1, hac0], by linarith [ht'.2, hbc0]⟩

theorem arcIcc_subset_of_val_23 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N)
    (hk : k.val = 2 ∨ k.val = 3) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k
      ⊆ Set.Ioo (Real.pi / 2) (3 * Real.pi / 2) := by
  have hbc2 := cornerAngle_lt_pi_div_two (p.re - x₀) (y₁ - p.im)
  have hbd2 := cornerAngle_lt_pi_div_two (p.re - x₀) (p.im - y₀)
  have hα₁ := neg_cornerAngle_lt_leftAngle hx₀ hL₁
  have hα₂ := leftAngle_lt_cornerAngle hx₀ hL₀
  obtain ⟨n, hn⟩ := k
  rcases hk with hk | hk
  · obtain rfl : n = 2 := hk
    intro t ht
    have ht' : t ∈ Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
        (π + Real.arctan ((p.im - yL) / (p.re - x₀))) := ht
    exact ⟨by linarith [ht'.1, hbc2], by linarith [ht'.2, hα₂, hbd2]⟩
  · obtain rfl : n = 3 := hk
    intro t ht
    have ht' : t ∈ Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
        (π + cornerAngle (p.re - x₀) (p.im - y₀)) := ht
    exact ⟨by linarith [ht'.1, hα₁, hbc2], by linarith [ht'.2, hbd2]⟩

theorem arcIcc_subset_of_val_4 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) (hk : k.val = 4) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k
      ⊆ Set.Ioo Real.pi (2 * Real.pi) := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hbd0 := cornerAngle_pos hb hd
  have had0 := cornerAngle_pos ha hd
  obtain ⟨n, hn⟩ := k
  obtain rfl : n = 4 := hk
  intro t ht
  have ht' : t ∈ Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
      (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) := ht
  exact ⟨by linarith [ht'.1, hbd0], by linarith [ht'.2, had0]⟩

theorem arcIcc_subset_of_val_5 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁)
    (k : Fin (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N) (hk : k.val = 5) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).arcIcc k
      ⊆ Set.Ioc (3 * Real.pi / 2) (2 * Real.pi) := by
  have had2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (p.im - y₀)
  obtain ⟨n, hn⟩ := k
  obtain rfl : n = 5 := hk
  intro t ht
  have ht' : t ∈ Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π) := ht
  exact ⟨by linarith [ht'.1, had2], ht'.2⟩

open Set in

theorem exists_rect_sixArcs (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    ∃ R : RadialRegion,
      R.q = p ∧ R.N = 6 ∧
      R.K = {z : ℂ | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc y₀ y₁} ∧
      R.Kint = {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁} ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc p.im y₁}) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = y₁ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 2 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc yL y₁}) ∧
      (∀ k : Fin R.N, k.val = 3 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc y₀ yL}) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = y₀ ∧ z.re ∈ Icc x₀ x₁}) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc y₀ p.im}) ∧
      (∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨x₁, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨x₀, y₁⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨x₀, yL⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨x₀, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨x₁, y₀⟩) ∧
      (∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
      (∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (x₁ - p.re))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (y₁ - p.im))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (p.re - x₀))⁻¹)) ∧
      (∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (p.im - y₀))⁻¹) ∧
      (∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ R.K, z ∉ R.Kint →
        R.loop (if Complex.arg (z - p) < 0 then Complex.arg (z - p) + 2 * π else Complex.arg (z - p))
          = z) ∧
      (∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
        R.loop '' Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂)) := by
  refine ⟨rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    rectRegion6_q x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    rectRegion6_N x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    rectRegion6_K x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    rectRegion6_Kint x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    r_eq_of_val_right x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    r_eq_of_val_top x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    r_eq_of_val_left x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    r_eq_of_val_bottom x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    arcIcc_subset_of_val_0 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    arcIcc_subset_of_val_1 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    arcIcc_subset_of_val_23 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    arcIcc_subset_of_val_4 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    arcIcc_subset_of_val_5 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁,
    fun z hz hz' => loop_angle₀ x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ hz hz',
    fun k t₁ t₂ h₁ h₂ h => image_loop_Icc x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k h₁ h₂ h⟩
  · intro k hk
    rw [arcSet_eq x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [arcSet_eq x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [arcSet_eq x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [arcSet_eq x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [arcSet_eq x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [arcSet_eq x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl
  · intro k hk
    rw [loop_φs x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ k, hk]
    rfl


end Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
