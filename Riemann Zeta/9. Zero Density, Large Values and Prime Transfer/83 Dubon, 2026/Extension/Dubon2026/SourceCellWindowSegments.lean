import Dubon2026.SourceCellSixArcBoundary
import Dubon2026.SourceCellPowerArcInjectivity

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite paired dissection.
Refine the outer window at exactly its grid perimeter vertices. The unchanged
radial region retains the pole-cell scale, while exact side intervals and
arc counts supply the boundary pairing and Euler calculation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing normalized argument, radial periodicity, loop injectivity and
six-arc rectangles are reused; no external Lean module is imported.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.GridWindow
noncomputable section
open scoped Real
open Set

theorem coords_of_mem_segment {z₁ z₂ z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      z.re = z₁.re + θ * (z₂.re - z₁.re) ∧ z.im = z₁.im + θ * (z₂.im - z₁.im) := by
  rw [segment_eq_image' ℝ] at hz
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := hz
  have e1 : (θ • (z₂ - z₁)).re = θ * (z₂ - z₁).re := Complex.smul_re θ (z₂ - z₁)
  have e2 : (θ • (z₂ - z₁)).im = θ * (z₂ - z₁).im := Complex.smul_im θ (z₂ - z₁)
  rw [Complex.sub_re] at e1
  rw [Complex.sub_im] at e2
  have hr : (z₁ + θ • (z₂ - z₁)).re = z₁.re + θ * (z₂.re - z₁.re) :=
    (Complex.add_re z₁ (θ • (z₂ - z₁))).trans (congrArg (fun x => z₁.re + x) e1)
  have hi : (z₁ + θ • (z₂ - z₁)).im = z₁.im + θ * (z₂.im - z₁.im) :=
    (Complex.add_im z₁ (θ • (z₂ - z₁))).trans (congrArg (fun x => z₁.im + x) e2)
  exact ⟨θ, h0, h1, hr, hi⟩

theorem mem_segment_of_coords {z₁ z₂ z : ℂ} {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hre : z.re = z₁.re + θ * (z₂.re - z₁.re)) (him : z.im = z₁.im + θ * (z₂.im - z₁.im)) :
    z ∈ segment ℝ z₁ z₂ := by
  rw [segment_eq_image' ℝ]
  refine ⟨θ, ⟨h0, h1⟩, ?_⟩
  have e1 : (θ • (z₂ - z₁)).re = θ * (z₂ - z₁).re := Complex.smul_re θ (z₂ - z₁)
  have e2 : (θ • (z₂ - z₁)).im = θ * (z₂ - z₁).im := Complex.smul_im θ (z₂ - z₁)
  rw [Complex.sub_re] at e1
  rw [Complex.sub_im] at e2
  have hr : (z₁ + θ • (z₂ - z₁)).re = z.re :=
    (Complex.add_re z₁ (θ • (z₂ - z₁))).trans ((congrArg (fun x => z₁.re + x) e1).trans hre.symm)
  have hi : (z₁ + θ • (z₂ - z₁)).im = z.im :=
    (Complex.add_im z₁ (θ • (z₂ - z₁))).trans ((congrArg (fun x => z₁.im + x) e2).trans him.symm)
  exact Complex.ext hr hi

theorem segment_horizontal {z₁ z₂ : ℂ} (him : z₁.im = z₂.im) (hre : z₁.re ≤ z₂.re) :
    segment ℝ z₁ z₂ = {z : ℂ | z.im = z₁.im ∧ z.re ∈ Set.Icc z₁.re z₂.re} := by
  ext z
  rw [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · intro hz
    obtain ⟨θ, h0, h1, hzre, hzim⟩ := coords_of_mem_segment hz
    rw [← him, sub_self, mul_zero, add_zero] at hzim
    have h2 := mul_nonneg h0 (sub_nonneg.mpr hre)
    have h3 := mul_le_of_le_one_left (sub_nonneg.mpr hre) h1
    exact ⟨hzim, by linarith, by linarith⟩
  · rintro ⟨hzim, hz1, hz2⟩
    rcases eq_or_lt_of_le hre with hd | hd
    · refine mem_segment_of_coords (θ := 0) (le_refl 0) zero_le_one ?_ ?_
      · rw [zero_mul, add_zero]
        linarith
      · rw [zero_mul, add_zero]
        exact hzim
    · have hd' : 0 < z₂.re - z₁.re := sub_pos.mpr hd
      have hθ0 : 0 ≤ (z.re - z₁.re) / (z₂.re - z₁.re) := div_nonneg (by linarith) hd'.le
      have hθ1 : (z.re - z₁.re) / (z₂.re - z₁.re) ≤ 1 := (div_le_one₀ hd').mpr (by linarith)
      refine mem_segment_of_coords hθ0 hθ1 ?_ ?_
      · rw [div_mul_cancel₀ _ hd'.ne']
        ring
      · rw [← him, sub_self, mul_zero, add_zero]
        exact hzim

theorem segment_vertical {z₁ z₂ : ℂ} (hre : z₁.re = z₂.re) (him : z₁.im ≤ z₂.im) :
    segment ℝ z₁ z₂ = {z : ℂ | z.re = z₁.re ∧ z.im ∈ Set.Icc z₁.im z₂.im} := by
  ext z
  rw [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · intro hz
    obtain ⟨θ, h0, h1, hzre, hzim⟩ := coords_of_mem_segment hz
    rw [← hre, sub_self, mul_zero, add_zero] at hzre
    have h2 := mul_nonneg h0 (sub_nonneg.mpr him)
    have h3 := mul_le_of_le_one_left (sub_nonneg.mpr him) h1
    exact ⟨hzre, by linarith, by linarith⟩
  · rintro ⟨hzre, hz1, hz2⟩
    rcases eq_or_lt_of_le him with hd | hd
    · refine mem_segment_of_coords (θ := 0) (le_refl 0) zero_le_one ?_ ?_
      · rw [zero_mul, add_zero]
        exact hzre
      · rw [zero_mul, add_zero]
        linarith
    · have hd' : 0 < z₂.im - z₁.im := sub_pos.mpr hd
      have hθ0 : 0 ≤ (z.im - z₁.im) / (z₂.im - z₁.im) := div_nonneg (by linarith) hd'.le
      have hθ1 : (z.im - z₁.im) / (z₂.im - z₁.im) ≤ 1 := (div_le_one₀ hd').mpr (by linarith)
      refine mem_segment_of_coords hθ0 hθ1 ?_ ?_
      · rw [← hre, sub_self, mul_zero, add_zero]
        exact hzre
      · rw [div_mul_cancel₀ _ hd'.ne']
        ring


/-- Reuse the normalized boundary argument already used by the six-arc cells. -/
def ang (w : ℂ) : ℝ := RectSixArcs.angle₀ w

theorem ang_mem (w : ℂ) : ang w ∈ Set.Ico 0 (2 * Real.pi) :=
  RectSixArcs.angle₀_mem w

end
end Dubon2026.SourceFunctionField.CellGeometry.GridWindow
