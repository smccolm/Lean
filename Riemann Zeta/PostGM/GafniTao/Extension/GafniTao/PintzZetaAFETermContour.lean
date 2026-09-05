import GafniTao.PintzZetaAFEDirichlet
import GafniTao.PintzGammaHorizontalSharp

/-!
# Termwise contour shift for the single-zeta AFE

This exposes the residue of each positive Dirichlet coefficient.  It is the
exact device needed to use one contour on integers below the square-root
conductor and the opposite contour on the tail.
-/

open Complex MeasureTheory Set
open scoped LSeries.notation

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

set_option maxHeartbeats 2000000

/-- Entire numerator of one positive Dirichlet-series term, on a strip where
the shifted Deligne Gamma factor stays in the open right half-plane. -/
noncomputable def pintzZetaAFETermNumerator
    (s base : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  let z := base + w
  Complex.exp (100 * w ^ 2) * (z * (1 - z)) * Complex.Gammaℝ z /
      pintzZetaAFENormalization s * pintzZetaDirichletTerm z n

/-- Cauchy integrand for one positive Dirichlet-series term. -/
noncomputable def pintzZetaAFETermContourIntegrand
    (s base : ℂ) (n : ℕ) (w : ℂ) : ℂ :=
  pintzZetaAFETermNumerator s base n w / w

/-- The termwise contour integrand restricts to the previously opened
right-edge term on a vertical line. -/
theorem pintzZetaAFETermContourIntegrand_vertical
    (s base : ℂ) (n : ℕ) (c u : ℝ) :
    pintzZetaAFETermContourIntegrand s base n
        ((c : ℂ) + (u : ℂ) * I) =
      pintzZetaAFERightTerm s base c u n := by
  unfold pintzZetaAFETermContourIntegrand pintzZetaAFETermNumerator
    pintzZetaAFERightTerm pintzZetaAFERightWeight
  ring

@[simp]
theorem pintzZetaAFETermNumerator_zero (s base : ℂ) (n : ℕ) :
    pintzZetaAFETermNumerator s base n 0 =
      (base * (1 - base)) * Complex.Gammaℝ base /
          pintzZetaAFENormalization s * pintzZetaDirichletTerm base n := by
  simp [pintzZetaAFETermNumerator]

theorem differentiableOn_pintzZetaAFETermNumerator_rectangle
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c H : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hbase : q < base.re) :
    DifferentiableOn ℂ (pintzZetaAFETermNumerator s base n)
      (Rectangle ((-q : ℂ) - (H : ℂ) * I)
        ((c : ℂ) + (H : ℂ) * I)) := by
  intro w hw
  have hwRe : -q ≤ w.re := by
    have := (mem_reProdIm.mp hw).1
    norm_num at this
    rw [uIcc_of_le (by linarith : (-q : ℝ) ≤ c)] at this
    exact this.1
  have hzpos : 0 < (base + w).re := by
    simp only [add_re]
    linarith
  have hshift : DifferentiableAt ℂ (fun u : ℂ => base + u) w :=
    (differentiableAt_const _).add differentiableAt_id
  have hexp : DifferentiableAt ℂ
      (fun u : ℂ => Complex.exp (100 * u ^ 2)) w := by
    fun_prop
  have hpoly : DifferentiableAt ℂ
      (fun u : ℂ => (base + u) * (1 - (base + u))) w :=
    hshift.mul ((differentiableAt_const _).sub hshift)
  have hgamma : DifferentiableAt ℂ (fun u : ℂ => Complex.Gammaℝ (base + u)) w :=
    (differentiableAt_GammaR_of_re_pos hzpos).comp w
      hshift
  have hdirichlet : DifferentiableAt ℂ
      (fun u : ℂ => pintzZetaDirichletTerm (base + u) n) w := by
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hpow : DifferentiableAt ℂ
        (fun u : ℂ => (n : ℂ) ^ (base + u)) w :=
      hshift.const_cpow (c := (n : ℂ)) (Or.inl hnc)
    simp only [pintzZetaDirichletTerm, LSeries.term_of_ne_zero hn]
    exact (differentiableAt_const _).div
      hpow (Complex.cpow_ne_zero_iff.mpr (Or.inl hnc))
  unfold pintzZetaAFETermNumerator
  dsimp only
  exact ((((hexp.mul hpoly).mul hgamma).div_const
    (pintzZetaAFENormalization s)).mul hdirichlet).differentiableWithinAt

/-- Finite termwise contour shift.  The right, left, top and bottom edges
together equal the literal residue at `w=0`. -/
theorem pintzZetaAFETerm_finiteRectangle
    (s base : ℂ) {n : ℕ} (hn : n ≠ 0) {q c H : ℝ}
    (hq : 0 < q) (hc : 0 < c) (hH : 0 < H) (hbase : q < base.re) :
    RectangleIntegral'
        (pintzZetaAFETermContourIntegrand s base n)
        ((-q : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      pintzZetaAFETermNumerator s base n 0 := by
  let F : ℂ → ℂ := pintzZetaAFETermNumerator s base n
  let z : ℂ := (-q : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  have hzero : Rectangle z w ∈ nhds (0 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le (by simp [z, w]; linarith : z.re ≤ w.re),
      uIoo_of_le (by simp [z, w]; linarith : z.im ≤ w.im)]
    simp [z, w, hq, hc, hH]
  have hF : DifferentiableOn ℂ F (Rectangle z w) := by
    simpa only [F, z, w] using
      differentiableOn_pintzZetaAFETermNumerator_rectangle
        s base hn hq hc hbase
  have hdslope : HolomorphicOn (dslope F 0) (Rectangle z w) := by
    change DifferentiableOn ℂ (dslope F 0) (Rectangle z w)
    rw [differentiableOn_dslope
      (show Rectangle z w ∈ nhds (0 : ℂ) from hzero)]
    exact hF
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
  simpa [F, z, w, pintzZetaAFETermContourIntegrand] using hrect

#print axioms differentiableOn_pintzZetaAFETermNumerator_rectangle
#print axioms pintzZetaAFETerm_finiteRectangle

set_option maxHeartbeats 200000

end

end GafniTao
