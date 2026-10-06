import Dubon2026.ConvexAsymptotes

/-! # Derivative convergence from three convex potential values on an affine limiting segment -/

namespace Dubon2026

open Set Filter
open scoped Topology

theorem convex_derivatives_between_slopes {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) {l x u : ℝ} (hl : l < x) (hu : x < u) :
    slope f l x ≤ derivWithin f (Iio x) x ∧
      derivWithin f (Iio x) x ≤ derivWithin f (Ioi x) x ∧
      derivWithin f (Ioi x) x ≤ slope f x u :=
  ⟨hf.slope_le_leftDeriv_of_mem_interior (mem_univ l) (by simp) hl,
    hf.leftDeriv_le_rightDeriv_of_mem_interior (by simp),
    hf.rightDeriv_le_slope_of_mem_interior (by simp) (mem_univ u) hu⟩

/-- Only three actual potential limits are needed on an affine limiting segment. -/
theorem tendsto_scaled_convex_derivatives {F : ℕ → ℝ → ℝ} {d : ℕ → ℝ}
    (hf : ∀ᶠ N in atTop, ConvexOn ℝ univ (F N))
    (hd : ∀ᶠ N in atTop, 0 < d N) {l x u c b : ℝ} (hl : l < x) (hu : x < u)
    (hliml : Tendsto (fun N => F N l / d N) atTop (𝓝 (c * l + b)))
    (hlimx : Tendsto (fun N => F N x / d N) atTop (𝓝 (c * x + b)))
    (hlimu : Tendsto (fun N => F N u / d N) atTop (𝓝 (c * u + b))) :
    Tendsto (fun N => derivWithin (F N) (Iio x) x / d N) atTop (𝓝 c) ∧
      Tendsto (fun N => derivWithin (F N) (Ioi x) x / d N) atTop (𝓝 c) := by
  have hlower : Tendsto (fun N => slope (F N) l x / d N) atTop (𝓝 c) := by
    have he : (c * x + b - (c * l + b)) / (x - l) = c := by
      apply (div_eq_iff (sub_ne_zero.mpr hl.ne')).mpr
      ring
    have hh := (hlimx.sub hliml).div_const (x - l)
    rw [he] at hh
    convert hh using 1
    funext N
    simp only [slope_def_field]
    ring
  have hupper : Tendsto (fun N => slope (F N) x u / d N) atTop (𝓝 c) := by
    have he : (c * u + b - (c * x + b)) / (u - x) = c := by
      apply (div_eq_iff (sub_ne_zero.mpr hu.ne')).mpr
      ring
    have hh := (hlimu.sub hlimx).div_const (u - x)
    rw [he] at hh
    convert hh using 1
    funext N
    simp only [slope_def_field]
    ring
  have hbounds : ∀ᶠ N in atTop,
      slope (F N) l x / d N ≤ derivWithin (F N) (Iio x) x / d N ∧
      derivWithin (F N) (Iio x) x / d N ≤ derivWithin (F N) (Ioi x) x / d N ∧
      derivWithin (F N) (Ioi x) x / d N ≤ slope (F N) x u / d N := by
    filter_upwards [hf, hd] with N hFN hdN
    have hh := convex_derivatives_between_slopes hFN hl hu
    exact ⟨div_le_div_of_nonneg_right hh.1 hdN.le,
      div_le_div_of_nonneg_right hh.2.1 hdN.le, div_le_div_of_nonneg_right hh.2.2 hdN.le⟩
  exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2.1.trans h.2.2),
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
      (hbounds.mono fun _ h => h.1.trans h.2.1) (hbounds.mono fun _ h => h.2.2)⟩

end Dubon2026
