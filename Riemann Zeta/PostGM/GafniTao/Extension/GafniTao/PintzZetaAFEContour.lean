import RiemannZeta.GuthMaynard.SmoothZetaAFE

/-!
# A single-zeta smooth approximate-functional-equation contour

This is the pole-free contour needed for the pointwise zeta estimate in
Pintz (2023), equations (4.9)--(4.11).  It is deliberately kept separate
from the frozen Guth--Maynard source.  The completed-xi numerator removes the
zeta poles, while its functional equation identifies the left edge with the
right edge based at `1 - s`.
-/

open Complex Filter MeasureTheory Set Topology

noncomputable section

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- The entire numerator on the single-zeta AFE contour. -/
noncomputable def pintzZetaAFEContourNumerator (s w : ℂ) : ℂ :=
  Complex.exp (100 * w ^ 2) * completedXiNumerator (s + w)

/-- The Cauchy integrand whose residue at zero is the completed-xi numerator
at `s`. -/
noncomputable def pintzZetaAFEContourIntegrand (s w : ℂ) : ℂ :=
  pintzZetaAFEContourNumerator s w / w

theorem differentiable_pintzZetaAFEContourNumerator (s : ℂ) :
    Differentiable ℂ (pintzZetaAFEContourNumerator s) := by
  unfold pintzZetaAFEContourNumerator
  have hshift : Differentiable ℂ (fun w : ℂ => s + w) := by fun_prop
  have hxi : Differentiable ℂ
      (fun w : ℂ => completedXiNumerator (s + w)) :=
    fun w => differentiable_completedXiNumerator.differentiableAt.comp w
      (hshift w)
  fun_prop (disch := assumption)

@[simp]
theorem pintzZetaAFEContourNumerator_zero (s : ℂ) :
    pintzZetaAFEContourNumerator s 0 = completedXiNumerator s := by
  simp [pintzZetaAFEContourNumerator]

/-- Exact functional-equation reflection of the single-zeta integrand. -/
theorem pintzZetaAFEContourIntegrand_neg (s w : ℂ) :
    pintzZetaAFEContourIntegrand s (-w) =
      -pintzZetaAFEContourIntegrand (1 - s) w := by
  unfold pintzZetaAFEContourIntegrand pintzZetaAFEContourNumerator
  have harg : s + -w = 1 - ((1 - s) + w) := by ring
  rw [harg, completedXiNumerator_one_sub]
  simp only [neg_sq]
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

/-- The finite-rectangle residue identity.  No limiting argument or
Dirichlet-series opening is present at this stage. -/
theorem pintzZetaAFE_finiteRectangle (s : ℂ) {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) :
    RectangleIntegral'
        (pintzZetaAFEContourIntegrand s)
        ((-c : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      completedXiNumerator s := by
  let F : ℂ → ℂ := pintzZetaAFEContourNumerator s
  let z : ℂ := (-c : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hF : Differentiable ℂ F :=
    differentiable_pintzZetaAFEContourNumerator s
  have hzero : Rectangle z w ∈ nhds (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le (by simp [z, w]; linarith : z.re ≤ w.re),
      uIoo_of_le (by simp [z, w]; linarith : z.im ≤ w.im)]
    simp [z, w, hc, hH]
  have hdslope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    rw [differentiableOn_dslope
      (show Rectangle z w ∈ nhds (0 : ℂ) from hzero)]
    exact hF.differentiableOn
  have hprincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp
  have hrect := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0)
    (p := 0) (A := F 0)
    (zRe_le_wRe := by simp [z, w]; linarith)
    (zIm_le_wIm := by simp [z, w]; linarith)
    hzero hdslope hprincipal
  simpa [F, z, w, pintzZetaAFEContourIntegrand] using hrect

#print axioms differentiable_pintzZetaAFEContourNumerator
#print axioms pintzZetaAFEContourIntegrand_neg
#print axioms pintzZetaAFE_finiteRectangle

end GafniTao
