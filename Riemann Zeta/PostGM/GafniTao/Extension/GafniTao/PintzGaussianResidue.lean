import GafniTao.PintzGaussianKernel

/-!
# The origin residue of Pintz's Gaussian kernel

Equation (4.1) shifts the bare Gaussian kernel across the origin.  This file
proves, rather than postulates, that its principal part is exactly `1 / s`.
-/

open Complex Filter Asymptotics Topology

namespace GafniTao

noncomputable section

theorem pintzGaussianKernel_sub_principal_eq
    (lambda : ℝ) {s : ℂ} (hs : s ≠ 0) :
    pintzGaussianKernel lambda s - 1 / s =
      (pintzGaussianNumerator lambda s - 1) / s := by
  unfold pintzGaussianKernel
  field_simp

/-- The principal part at the origin is `1 / s`, uniformly for each fixed
positive Gaussian parameter. -/
theorem pintzGaussianKernel_sub_principal_isBigO_one
    (lambda : ℝ) :
    (pintzGaussianKernel lambda - fun s : ℂ => 1 / s) =O[𝓝[≠] (0 : ℂ)]
      (1 : ℂ → ℂ) := by
  have hdiff :
      (fun s : ℂ => pintzGaussianNumerator lambda s -
        pintzGaussianNumerator lambda 0) =O[𝓝 (0 : ℂ)]
          (fun s : ℂ => s - 0) :=
    (analyticAt_pintzGaussianNumerator lambda 0).differentiableAt.isBigO_sub
  rcases Asymptotics.isBigO_iff.mp hdiff with ⟨C, hC⟩
  refine Asymptotics.isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hC.filter_mono inf_le_left,
      self_mem_nhdsWithin] with s hsBound hsMem
  have hs : s ≠ 0 := by simpa using hsMem
  have hsNorm : 0 < ‖s‖ := norm_pos_iff.mpr hs
  rw [Pi.sub_apply, pintzGaussianKernel_sub_principal_eq lambda hs]
  rw [norm_div, Pi.one_apply, norm_one]
  have hnum :
      ‖pintzGaussianNumerator lambda s - 1‖ ≤ C * ‖s‖ := by
    simpa using hsBound
  calc
    ‖pintzGaussianNumerator lambda s - 1‖ / ‖s‖
        ≤ (C * ‖s‖) / ‖s‖ :=
      div_le_div_of_nonneg_right hnum hsNorm.le
    _ = C * 1 := by field_simp

#print axioms pintzGaussianKernel_sub_principal_isBigO_one

end

end GafniTao
