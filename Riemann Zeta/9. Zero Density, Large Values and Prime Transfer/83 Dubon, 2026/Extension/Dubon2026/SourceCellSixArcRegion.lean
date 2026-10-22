import Dubon2026.SourceCellSixArcSegments
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
/-- The seven ordered angular endpoints for the six source rectangle arcs. -/
noncomputable def breaks6 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) : Fin (6 + 1) → ℝ :=
  ![0, cornerAngle (x₁ - p.re) (y₁ - p.im), π - cornerAngle (p.re - x₀) (y₁ - p.im),
    π + Real.arctan ((p.im - yL) / (p.re - x₀)), π + cornerAngle (p.re - x₀) (p.im - y₀),
    2 * π - cornerAngle (x₁ - p.re) (p.im - y₀), 2 * π]

/- As constructed below. -/
/-- The six prescribed side segments, including the two vertical splits. -/
noncomputable def side (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) : ℕ → Set ℂ
  | 0 => {z | z.re = x₁ ∧ z.im ∈ Set.Icc p.im y₁}
  | 1 => {z | z.im = y₁ ∧ z.re ∈ Set.Icc x₀ x₁}
  | 2 => {z | z.re = x₀ ∧ z.im ∈ Set.Icc yL y₁}
  | 3 => {z | z.re = x₀ ∧ z.im ∈ Set.Icc y₀ yL}
  | 4 => {z | z.im = y₀ ∧ z.re ∈ Set.Icc x₀ x₁}
  | 5 => {z | z.re = x₁ ∧ z.im ∈ Set.Icc y₀ p.im}
  | _ => ∅

/- As constructed below. -/
/-- The seven successive endpoints of the six source rectangle arcs. -/
noncomputable def corner (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) : ℕ → ℂ
  | 0 => ⟨x₁, p.im⟩
  | 1 => ⟨x₁, y₁⟩
  | 2 => ⟨x₀, y₁⟩
  | 3 => ⟨x₀, yL⟩
  | 4 => ⟨x₀, y₀⟩
  | 5 => ⟨x₁, y₀⟩
  | 6 => ⟨x₁, p.im⟩
  | _ => 0

theorem neg_cornerAngle_lt_leftAngle {x₀ y₁ : ℝ} {p : ℂ} {yL : ℝ} (hx₀ : x₀ < p.re)
    (hL₁ : yL < y₁) :
    -cornerAngle (p.re - x₀) (y₁ - p.im) < Real.arctan ((p.im - yL) / (p.re - x₀)) := by
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have h1 : -(y₁ - p.im) < p.im - yL := by linarith [hL₁]
  have h : -(y₁ - p.im) / (p.re - x₀) < (p.im - yL) / (p.re - x₀) :=
    div_lt_div_of_pos_right h1 hb
  rw [neg_div] at h
  rw [cornerAngle, ← Real.arctan_neg]
  exact Real.arctan_strictMono h

theorem leftAngle_lt_cornerAngle {x₀ y₀ : ℝ} {p : ℂ} {yL : ℝ} (hx₀ : x₀ < p.re)
    (hL₀ : y₀ < yL) :
    Real.arctan ((p.im - yL) / (p.re - x₀)) < cornerAngle (p.re - x₀) (p.im - y₀) := by
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have h1 : p.im - yL < p.im - y₀ := by linarith [hL₀]
  have h : (p.im - yL) / (p.re - x₀) < (p.im - y₀) / (p.re - x₀) :=
    div_lt_div_of_pos_right h1 hb
  rw [cornerAngle]
  exact Real.arctan_strictMono h

private theorem r6_breaks_strictMono {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) : StrictMono (breaks6 x₀ x₁ y₀ y₁ p yL) := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hac0 := cornerAngle_pos ha hc
  have hac2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (y₁ - p.im)
  have hbc2 := cornerAngle_lt_pi_div_two (p.re - x₀) (y₁ - p.im)
  have hbd2 := cornerAngle_lt_pi_div_two (p.re - x₀) (p.im - y₀)
  have had0 := cornerAngle_pos ha hd
  have had2 := cornerAngle_lt_pi_div_two (x₁ - p.re) (p.im - y₀)
  have hα₁ := neg_cornerAngle_lt_leftAngle hx₀ hL₁
  have hα₂ := leftAngle_lt_cornerAngle hx₀ hL₀
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i
  · show (0 : ℝ) < cornerAngle (x₁ - p.re) (y₁ - p.im)
    exact hac0
  · show cornerAngle (x₁ - p.re) (y₁ - p.im) < π - cornerAngle (p.re - x₀) (y₁ - p.im)
    linarith [hac2, hbc2]
  · show π - cornerAngle (p.re - x₀) (y₁ - p.im) < π + Real.arctan ((p.im - yL) / (p.re - x₀))
    linarith [hα₁]
  · show π + Real.arctan ((p.im - yL) / (p.re - x₀)) < π + cornerAngle (p.re - x₀) (p.im - y₀)
    linarith [hα₂]
  · show π + cornerAngle (p.re - x₀) (p.im - y₀) < 2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)
    linarith [hbd2, had2]
  · show 2 * π - cornerAngle (x₁ - p.re) (p.im - y₀) < 2 * π
    linarith [had0]

private theorem r6_C2 {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ}
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    ∀ i : Fin 6, ContDiffOn ℝ 2 (rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀))
      (Set.Icc (breaks6 x₀ x₁ y₀ y₁ p yL i.castSucc) (breaks6 x₀ x₁ y₀ y₁ p yL i.succ)) := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  have hα₁ := neg_cornerAngle_lt_leftAngle hx₀ hL₁
  have hα₂ := leftAngle_lt_cornerAngle hx₀ hL₀
  intro i
  fin_cases i
  · show ContDiffOn ℝ 2 _ (Set.Icc 0 (cornerAngle (x₁ - p.re) (y₁ - p.im)))
    exact contDiffOn_r4_arc1 ha hb hc hd
  · show ContDiffOn ℝ 2 _
      (Set.Icc (cornerAngle (x₁ - p.re) (y₁ - p.im)) (π - cornerAngle (p.re - x₀) (y₁ - p.im)))
    exact contDiffOn_r4_arc2 ha hb hc hd
  · show ContDiffOn ℝ 2 _
      (Set.Icc (π - cornerAngle (p.re - x₀) (y₁ - p.im))
        (π + Real.arctan ((p.im - yL) / (p.re - x₀))))
    exact (contDiffOn_r4_arc3 ha hb hc hd).mono (Set.Icc_subset_Icc le_rfl (by linarith [hα₂]))
  · show ContDiffOn ℝ 2 _
      (Set.Icc (π + Real.arctan ((p.im - yL) / (p.re - x₀)))
        (π + cornerAngle (p.re - x₀) (p.im - y₀)))
    exact (contDiffOn_r4_arc3 ha hb hc hd).mono (Set.Icc_subset_Icc (by linarith [hα₁]) le_rfl)
  · show ContDiffOn ℝ 2 _
      (Set.Icc (π + cornerAngle (p.re - x₀) (p.im - y₀))
        (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)))
    exact contDiffOn_r4_arc4 ha hb hc hd
  · show ContDiffOn ℝ 2 _ (Set.Icc (2 * π - cornerAngle (x₁ - p.re) (p.im - y₀)) (2 * π))
    exact contDiffOn_r4_arc5 ha hb hc hd

/- As constructed below. -/
/-- The constructed six-arc radial rectangle with its actual smoothness proofs. -/
noncomputable def rectRegion6 (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) : RadialRegion where
  q := p
  r := rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀)
  hcont := continuous_rectRadial4 (sub_pos.mpr hx₁) (sub_pos.mpr hx₀) (sub_pos.mpr hy₁)
    (sub_pos.mpr hy₀)
  hper := periodic_rectRadial4
  hpos := rectRadial4_pos (sub_pos.mpr hx₁) (sub_pos.mpr hx₀) (sub_pos.mpr hy₁) (sub_pos.mpr hy₀)
  N := 6
  φs := breaks6 x₀ x₁ y₀ y₁ p yL
  hφ0 := rfl
  hφN := rfl
  hmono := r6_breaks_strictMono hx₀ hx₁ hy₀ hy₁ hL₀ hL₁
  hC2 := r6_C2 hx₀ hx₁ hy₀ hy₁ hL₀ hL₁

theorem rectRegion6_q (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).q = p := rfl

theorem rectRegion6_N (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).N = 6 := rfl

theorem rectRegion6_r (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).r
      = rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀) := rfl

theorem rectRegion6_φs (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).φs = breaks6 x₀ x₁ y₀ y₁ p yL := rfl

theorem rectRegion6_loop (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) (φ : ℝ) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).loop φ
      = p + (rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀) φ : ℂ)
          * Complex.exp ((φ : ℂ) * Complex.I) := rfl

theorem rectRegion6_K (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).K
      = {z : ℂ | z.re ∈ Set.Icc x₀ x₁ ∧ z.im ∈ Set.Icc y₀ y₁} := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  ext z
  show ‖z - p‖ ≤ rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀) (Complex.arg (z - p))
    ↔ z.re ∈ Set.Icc x₀ x₁ ∧ z.im ∈ Set.Icc y₀ y₁
  rw [mem_rectRadial4_iff ha hb hc hd p z]
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem rectRegion6_Kint (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ)
    (hx₀ : x₀ < p.re) (hx₁ : p.re < x₁) (hy₀ : y₀ < p.im) (hy₁ : p.im < y₁)
    (hL₀ : y₀ < yL) (hL₁ : yL < y₁) :
    (rectRegion6 x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁).Kint
      = {z : ℂ | z.re ∈ Set.Ioo x₀ x₁ ∧ z.im ∈ Set.Ioo y₀ y₁} := by
  have ha : 0 < x₁ - p.re := sub_pos.mpr hx₁
  have hb : 0 < p.re - x₀ := sub_pos.mpr hx₀
  have hc : 0 < y₁ - p.im := sub_pos.mpr hy₁
  have hd : 0 < p.im - y₀ := sub_pos.mpr hy₀
  ext z
  show ‖z - p‖ < rectRadial4 (x₁ - p.re) (p.re - x₀) (y₁ - p.im) (p.im - y₀) (Complex.arg (z - p))
    ↔ z.re ∈ Set.Ioo x₀ x₁ ∧ z.im ∈ Set.Ioo y₀ y₁
  rw [mem_rectRadial4_lt_iff ha hb hc hd p z]
  simp only [Set.mem_Ioo]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩


end Dubon2026.SourceFunctionField.CellGeometry.RectSixArcs
