import Dubon2026.ConvexDerivatives

/-! # Derivative limits forced by affine asymptotes of finite convex functions -/

namespace Dubon2026

open Set Filter
open scoped Topology

theorem convex_derivatives_between_unit_slopes {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (x : ℝ) :
    f x - f (x - 1) ≤ derivWithin f (Iio x) x ∧
      derivWithin f (Iio x) x ≤ derivWithin f (Ioi x) x ∧
        derivWithin f (Ioi x) x ≤ f (x + 1) - f x := by
  have hl := hf.slope_le_leftDeriv_of_mem_interior (mem_univ (x - 1))
    (by simp : x ∈ interior univ) (show x - 1 < x by linarith)
  have hr := hf.rightDeriv_le_slope_of_mem_interior (by simp : x ∈ interior univ)
    (mem_univ (x + 1)) (show x < x + 1 by linarith)
  have he₁ : x - (x - 1) = 1 := by ring
  have he₂ : x + 1 - x = 1 := by ring
  simp only [slope_def_field, he₁, he₂, div_one] at hl hr
  exact ⟨hl, hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp), hr⟩

theorem tendsto_convex_derivatives_of_affine_asymptote {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) {l : Filter ℝ} {c b : ℝ}
    (hminus : Tendsto (fun x : ℝ => x - 1) l l)
    (hplus : Tendsto (fun x : ℝ => x + 1) l l)
    (hlim : Tendsto (fun x => f x - c * x) l (𝓝 b)) :
    Tendsto (fun x => derivWithin f (Iio x) x) l (𝓝 c) ∧
      Tendsto (fun x => derivWithin f (Ioi x) x) l (𝓝 c) := by
  have hl : Tendsto (fun x => f x - f (x - 1)) l (𝓝 c) := by
    have he (x : ℝ) : f x - f (x - 1) =
        (f x - c * x) - (f (x - 1) - c * (x - 1)) + c := by ring
    simp only [he]
    simpa only [sub_self, zero_add] using (hlim.sub (hlim.comp hminus)).add_const c
  have hr : Tendsto (fun x => f (x + 1) - f x) l (𝓝 c) := by
    have he (x : ℝ) : f (x + 1) - f x =
        (f (x + 1) - c * (x + 1)) - (f x - c * x) + c := by ring
    simp only [he]
    simpa only [sub_self, zero_add] using ((hlim.comp hplus).sub hlim).add_const c
  exact ⟨hl.squeeze hr (fun x => (convex_derivatives_between_unit_slopes hf x).1)
    (fun x => (convex_derivatives_between_unit_slopes hf x).2.1.trans
      (convex_derivatives_between_unit_slopes hf x).2.2),
    hl.squeeze hr (fun x => (convex_derivatives_between_unit_slopes hf x).1.trans
      (convex_derivatives_between_unit_slopes hf x).2.1)
      (fun x => (convex_derivatives_between_unit_slopes hf x).2.2)⟩

theorem tendsto_convex_derivatives_atTop {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) {c b : ℝ}
    (hlim : Tendsto (fun x => f x - c * x) atTop (𝓝 b)) :
    Tendsto (fun x => derivWithin f (Iio x) x) atTop (𝓝 c) ∧
      Tendsto (fun x => derivWithin f (Ioi x) x) atTop (𝓝 c) :=
  tendsto_convex_derivatives_of_affine_asymptote hf
    (by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id) hlim

theorem tendsto_convex_derivatives_atBot {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) {c b : ℝ}
    (hlim : Tendsto (fun x => f x - c * x) atBot (𝓝 b)) :
    Tendsto (fun x => derivWithin f (Iio x) x) atBot (𝓝 c) ∧
      Tendsto (fun x => derivWithin f (Ioi x) x) atBot (𝓝 c) :=
  tendsto_convex_derivatives_of_affine_asymptote hf
    (by simpa only [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-1 : ℝ) tendsto_id)
    (tendsto_atBot_add_const_right atBot (1 : ℝ) tendsto_id) hlim

end Dubon2026
