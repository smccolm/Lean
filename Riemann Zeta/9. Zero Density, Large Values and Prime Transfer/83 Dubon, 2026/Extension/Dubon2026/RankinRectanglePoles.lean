import Dubon2026.NewmanRectangle

/-! # Exact rectangle Cauchy identities for the two genuine Rankin Perron poles -/

namespace Dubon2026

open Complex Set Filter
open scoped Topology

noncomputable section

/-- Cauchy's formula at an arbitrary interior point, with the actual numerator and rectangle integral. -/
theorem rectangle_cauchy_at {F : ℂ → ℂ} {z w p : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) (hF : DifferentiableOn ℂ F (Rectangle z w)) :
    RectangleIntegral' (fun s => F s / (s - p)) z w = F p := by
  apply ResidueTheoremOnRectangleWithSimplePole hre him hp
    ((Complex.differentiableOn_dslope hp).mpr hF)
  intro s hs
  have hsp : s ≠ p := hs.2
  simp only [Pi.sub_apply, dslope_of_ne F hsp, slope_def_field]
  ring

/-- The actual Cauchy quotient is integrable on every edge when its pole lies strictly inside. -/
theorem rectangle_cauchy_border_integrable {F : ℂ → ℂ} {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) (hF : DifferentiableOn ℂ F (Rectangle z w)) :
    RectangleBorderIntegrable (fun s => F s / (s - p)) z w := by
  apply HolomorphicOn.rectangleBorderIntegrable' _ hp
  intro s hs
  exact (hF.mono diff_subset s hs).div (by fun_prop) (sub_ne_zero.mpr hs.2)

/-- The actual two-pole rectangle integral is the difference of the numerator's values at one and zero. -/
theorem rectangle_two_pole_cauchy {H : ℂ → ℂ} {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (h0 : Rectangle z w ∈ 𝓝 (0 : ℂ)) (h1 : Rectangle z w ∈ 𝓝 (1 : ℂ))
    (hH : DifferentiableOn ℂ H (Rectangle z w)) :
    RectangleIntegral' (fun s => H s / (s * (s - 1))) z w = H 1 - H 0 := by
  let G : ℂ → ℂ := fun s => dslope H 0 s + H 0
  have hG : DifferentiableOn ℂ G (Rectangle z w) :=
    ((Complex.differentiableOn_dslope h0).mpr hH).add_const _
  let F0 : ℂ → ℂ := fun s => (-H 0) / (s - 0)
  let F1 : ℂ → ℂ := fun s => G s / (s - 1)
  have hi0 : RectangleBorderIntegrable F0 z w := rectangle_cauchy_border_integrable h0 (differentiableOn_const (-H 0))
  have hi1 : RectangleBorderIntegrable F1 z w := rectangle_cauchy_border_integrable h1 hG
  have hI0 : RectangleIntegral' F0 z w = -H 0 := rectangle_cauchy_at hre him h0 (differentiableOn_const (-H 0))
  have hI1 : RectangleIntegral' F1 z w = G 1 := rectangle_cauchy_at hre him h1 hG
  have hG1 : G 1 = H 1 := by
    simp only [G, dslope_of_ne H one_ne_zero, slope_def_field, sub_zero, div_one]
    ring
  calc
    _ = RectangleIntegral' (F0 + F1) z w := by
      apply RectangleIntegral'_congr
      intro s hs
      have hs0 : s ≠ 0 := by
        intro he
        exact not_mem_rectangleBorder_of_rectangle_mem_nhds h0 (he ▸ hs)
      have hs1 : s ≠ 1 := by
        intro he
        exact not_mem_rectangleBorder_of_rectangle_mem_nhds h1 (he ▸ hs)
      simp only [Pi.add_apply, F0, F1, G, dslope_of_ne H hs0, slope_def_field, sub_zero]
      field_simp [hs0, sub_ne_zero.mpr hs1]
      ring
    _ = RectangleIntegral' F0 z w + RectangleIntegral' F1 z w := by
      rw [RectangleIntegral', RectangleBorderIntegrable.add hi0 hi1, smul_add]
    _ = _ := by rw [hI0, hI1, hG1]; ring

end
end Dubon2026
