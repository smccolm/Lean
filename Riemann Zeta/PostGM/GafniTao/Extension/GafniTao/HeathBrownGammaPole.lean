import GafniTao.HeathBrownMovingPole

/-!
# Gamma's pole at zero in the Heath--Brown Mellin shift

After the moving zeta pole has been crossed on a positive line, the remaining
shift crosses `w=0`.  Multiplication by `w` is represented by the holomorphic
continuation `Gamma(w+1)`, so the residue is literally `zeta(s)^2`.
-/

open Complex Set
open scoped Topology

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Holomorphic numerator which clears Gamma's simple pole at zero. -/
noncomputable def heathBrownGammaPoleNumerator (s w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * riemannZeta (s + w) ^ 2

theorem heathBrownGammaPoleNumerator_zero (s : ℂ) :
    heathBrownGammaPoleNumerator s 0 = riemannZeta s ^ 2 := by
  simp [heathBrownGammaPoleNumerator]

theorem heathBrownZetaSquareMellinIntegrand_eq_gammaPoleCleared
    {s w : ℂ} (hw : w ≠ 0) :
    heathBrownZetaSquareMellinIntegrand s w =
      heathBrownGammaPoleNumerator s w / w := by
  have hRec := Complex.Gamma_add_one w hw
  unfold heathBrownZetaSquareMellinIntegrand heathBrownGammaPoleNumerator
  rw [hRec]
  field_simp [hw]

/-- Finite shift across Gamma's pole.  The condition `d < Re(1-s)` keeps the
moving zeta pole strictly to the right of this rectangle. -/
theorem heathBrown_gammaPole_finite_rectangle
    {s : ℂ} {delta d H : ℝ}
    (hdelta : 0 < delta) (hdeltaUpper : delta < 1)
    (hd : 0 < d) (hdp : d < (heathBrownMovingPole s).re)
    (hH : 0 < H) :
    RectangleIntegral' (heathBrownZetaSquareMellinIntegrand s)
        ((-delta : ℂ) - (H : ℂ) * I) ((d : ℂ) + (H : ℂ) * I) =
      riemannZeta s ^ 2 := by
  let z : ℂ := (-delta : ℂ) - (H : ℂ) * I
  let w : ℂ := (d : ℂ) + (H : ℂ) * I
  let F : ℂ → ℂ := heathBrownGammaPoleNumerator s
  have hzre : z.re ≤ w.re := by simp [z, w]; linarith
  have hzim : z.im ≤ w.im := by simp [z, w]; linarith
  have hzero : Rectangle z w ∈ 𝓝 (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, uIoo_of_le hzre, uIoo_of_le hzim,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    simp [z, w, hdelta, hd, hH]
  have hF : DifferentiableOn ℂ F (Rectangle z w) := by
    intro u hu
    have huBounds := (mem_Rect hzre hzim u).mp hu
    have huLower : -delta ≤ u.re := by
      have hzReal : z.re = -delta := by simp [z]
      linarith [huBounds.1]
    have huUpper : u.re ≤ d := by
      have hwReal : w.re = d := by simp [w]
      linarith [huBounds.2.1]
    have huNegOne : -(1 : ℝ) < u.re := by linarith
    have hGamma : DifferentiableAt ℂ
        (fun v : ℂ => Complex.Gamma (v + 1)) u := by
      apply (Complex.differentiableAt_Gamma (u + 1) ?_).comp u
        (differentiableAt_id.add_const 1)
      intro m hm
      have hre := congrArg Complex.re hm
      simp at hre
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      linarith
    have hNotPole : s + u ≠ 1 := by
      intro hsu
      have hre := congrArg Complex.re hsu
      have hpRe : (heathBrownMovingPole s).re = 1 - s.re := by
        simp [heathBrownMovingPole]
      simp only [add_re, one_re] at hre
      linarith
    have hZeta : DifferentiableAt ℂ
        (fun v : ℂ => riemannZeta (s + v)) u :=
      (differentiableAt_riemannZeta hNotPole).comp u
        (differentiableAt_const (c := s) |>.add differentiableAt_id)
    exact (hGamma.mul (hZeta.pow 2)).differentiableWithinAt
  have hSlope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    exact (Complex.differentiableOn_dslope hzero).2 hF
  have hPrincipal : Set.EqOn
      ((fun u : ℂ => F u / u) - fun u => F 0 / (u - 0))
      (dslope F 0) (Rectangle z w \ {0}) := by
    intro u hu
    have hu0 : u ≠ 0 := hu.2
    rw [Pi.sub_apply, dslope_of_ne F hu0]
    simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub]
    field_simp [hu0]
  have hCleared := ResidueTheoremOnRectangleWithSimplePole
    (f := fun u : ℂ => F u / u) (g := dslope F 0)
    (p := 0) (A := F 0) hzre hzim hzero hSlope hPrincipal
  have hzeroNotBorder : (0 : ℂ) ∉ RectangleBorder z w :=
    not_mem_rectangleBorder_of_rectangle_mem_nhds hzero
  have hCongr : Set.EqOn
      (heathBrownZetaSquareMellinIntegrand s)
      (fun u : ℂ => F u / u) (RectangleBorder z w) := by
    intro u hu
    have hu0 : u ≠ 0 := fun h => hzeroNotBorder (h ▸ hu)
    simpa only [F] using
      heathBrownZetaSquareMellinIntegrand_eq_gammaPoleCleared
        (s := s) hu0
  rw [RectangleIntegral'_congr hCongr]
  simpa only [F, heathBrownGammaPoleNumerator_zero] using hCleared


end

end GafniTao
