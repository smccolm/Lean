import GafniTao.Pintz2023MellinSeries
import RiemannZeta.GuthMaynard.HughesYoungShiftRegularization

/-!
# Pintz (2023), Lemma 3.4: the finite Mellin contour

The source shifts equation (3.5) to `Re w = 0`.  At the origin the zero of
`(2N)^w - N^w` cancels the pole of `Gamma w`.  We make that cancellation
literal by replacing their product with its divided-difference extension.
The only pole left in the rectangle is consequently the residue-one zeta
pole at `w = 1 - s`.
-/

open Complex Set MeasureTheory Filter
open scoped BigOperators Topology

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

noncomputable def pintz2023MellinPowerDiff (N : ℕ) (w : ℂ) : ℂ :=
  ((2 * N : ℕ) : ℂ) ^ w - (N : ℂ) ^ w

@[simp]
theorem pintz2023MellinPowerDiff_zero (N : ℕ) :
    pintz2023MellinPowerDiff N 0 = 0 := by
  simp [pintz2023MellinPowerDiff]

theorem differentiable_pintz2023MellinPowerDiff
    {N : ℕ} (hN : 0 < N) :
    Differentiable ℂ (pintz2023MellinPowerDiff N) := by
  unfold pintz2023MellinPowerDiff
  apply Differentiable.sub
  · exact differentiable_id.const_cpow
      (.inl (by exact_mod_cast (mul_pos (by norm_num : 0 < 2) hN).ne'))
  · exact differentiable_id.const_cpow
      (.inl (by exact_mod_cast hN.ne'))

/-- Holomorphic continuation of
`((2N)^w - N^w) * Gamma w` through `w = 0`. -/
noncomputable def pintz2023MellinWeight (N : ℕ) (w : ℂ) : ℂ :=
  dslope (pintz2023MellinPowerDiff N) 0 w * Complex.Gamma (w + 1)

theorem differentiableOn_pintz2023MellinWeight
    {N : ℕ} (hN : 0 < N) :
    DifferentiableOn ℂ (pintz2023MellinWeight N)
      {w : ℂ | -(1 : ℝ) < w.re} := by
  intro w hw
  have hSlope : DifferentiableAt ℂ
      (dslope (pintz2023MellinPowerDiff N) 0) w := by
    have hAll : Differentiable ℂ
        (dslope (pintz2023MellinPowerDiff N) 0) := by
      rw [← differentiableOn_univ]
      exact (Complex.differentiableOn_dslope (s := Set.univ) (c := 0)
        univ_mem).2 (differentiable_pintz2023MellinPowerDiff hN).differentiableOn
    exact hAll.differentiableAt
  have hNoPole : ∀ m : ℕ, w + 1 ≠ -m := by
    intro m hm
    change -(1 : ℝ) < w.re at hw
    have hre := congrArg Complex.re hm
    simp only [add_re, one_re, neg_re, natCast_re] at hre
    have hmNonneg : (0 : ℝ) ≤ m := by positivity
    linarith
  have hGamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w :=
    (Complex.differentiableAt_Gamma (w + 1) hNoPole).comp w
      (differentiableAt_id.add_const 1)
  exact (hSlope.mul hGamma).differentiableWithinAt

theorem pintz2023MellinWeight_eq
    {N : ℕ} {w : ℂ} (hw : w ≠ 0) :
    pintz2023MellinWeight N w =
      pintz2023MellinPowerDiff N w * Complex.Gamma w := by
  have hSlope := sub_smul_dslope (pintz2023MellinPowerDiff N) 0 w
  have hGamma := Complex.Gamma_add_one w hw
  rw [pintz2023MellinWeight, hGamma]
  rw [pintz2023MellinPowerDiff_zero] at hSlope
  simp only [sub_zero, smul_eq_mul] at hSlope
  calc
    dslope (pintz2023MellinPowerDiff N) 0 w *
        (w * Complex.Gamma w) =
      (w * dslope (pintz2023MellinPowerDiff N) 0 w) *
        Complex.Gamma w := by ring
    _ = pintz2023MellinPowerDiff N w * Complex.Gamma w := by rw [hSlope]

noncomputable def pintz2023MellinContourIntegrand
    (N : ℕ) (s w : ℂ) : ℂ :=
  pintz2023MellinWeight N w * riemannZeta (s + w)

theorem pintz2023MellinContourIntegrand_eq_source
    {N : ℕ} {s w : ℂ} (hw : w ≠ 0) :
    pintz2023MellinContourIntegrand N s w =
      pintz2023MellinPowerDiff N w * Complex.Gamma w *
        riemannZeta (s + w) := by
  rw [pintz2023MellinContourIntegrand, pintz2023MellinWeight_eq hw]

noncomputable def pintz2023MellinPoleFreeNumerator
    (N : ℕ) (s w : ℂ) : ℂ :=
  pintz2023MellinWeight N w * riemannZetaPoleRemoved (w - (1 - s))

theorem differentiableOn_pintz2023MellinPoleFreeNumerator
    {N : ℕ} (hN : 0 < N) (s : ℂ) :
    DifferentiableOn ℂ (pintz2023MellinPoleFreeNumerator N s)
      {w : ℂ | -(1 : ℝ) < w.re} := by
  intro w hw
  have hWeight := differentiableOn_pintz2023MellinWeight hN w hw
  have hPoleRemoved : DifferentiableAt ℂ
      (fun z : ℂ => riemannZetaPoleRemoved (z - (1 - s))) w :=
    differentiable_riemannZetaPoleRemoved.differentiableAt.comp w (by fun_prop)
  exact (hWeight.mul hPoleRemoved.differentiableWithinAt)

theorem pintz2023MellinContourIntegrand_eq_poleFree_div
    {N : ℕ} {s w : ℂ} (hw : w ≠ 1 - s) :
    pintz2023MellinContourIntegrand N s w =
      pintz2023MellinPoleFreeNumerator N s w / (w - (1 - s)) := by
  let u : ℂ := w - (1 - s)
  have hu : u ≠ 0 := sub_ne_zero.mpr hw
  have haffine : s + w = 1 + u := by dsimp only [u]; ring
  have hpole := riemannZetaPoleRemoved_eq_mul_riemannZeta hu
  unfold pintz2023MellinContourIntegrand pintz2023MellinPoleFreeNumerator
  rw [haffine]
  change pintz2023MellinWeight N w * riemannZeta (1 + u) =
    pintz2023MellinWeight N w * riemannZetaPoleRemoved u / u
  rw [hpole]
  field_simp [hu]

theorem pintz2023MellinPoleFreeNumerator_at_pole
    (N : ℕ) (s : ℂ) :
    pintz2023MellinPoleFreeNumerator N s (1 - s) =
      pintz2023MellinWeight N (1 - s) := by
  simp [pintz2023MellinPoleFreeNumerator, riemannZetaPoleRemoved_zero]

/-- Exact finite-height contour shift behind Pintz Lemma 3.4.  The Gamma
singularity at zero has already been removed; the displayed term is the
literal residue at the moving zeta pole. -/
theorem pintz2023Mellin_finite_rectangle
    {N : ℕ} {s : ℂ} (hN : 0 < N)
    (hsLower : -(1 : ℝ) < s.re) (hsUpper : s.re < 1)
    {R : ℝ} (hR : |s.im| < R) :
    RectangleIntegral' (pintz2023MellinContourIntegrand N s)
      (((0 : ℝ) : ℂ) - (R : ℂ) * I)
      (((2 : ℝ) : ℂ) + (R : ℂ) * I) =
        pintz2023MellinWeight N (1 - s) := by
  let z : ℂ := ((0 : ℝ) : ℂ) - (R : ℂ) * I
  let w : ℂ := ((2 : ℝ) : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - s
  let F : ℂ → ℂ := pintz2023MellinPoleFreeNumerator N s
  let g : ℂ → ℂ := dslope F p
  have hRpos : 0 < R := (abs_nonneg s.im).trans_lt hR
  have hzRe : z.re ≤ w.re := by simp [z, w]
  have hzIm : z.im ≤ w.im := by simp [z, w]; linarith
  have hpInterior : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [p, z, w]
      constructor <;> linarith
    · simp [p, z, w]
      constructor <;> linarith [le_abs_self s.im, neg_le_abs s.im]
  have hRectSubset : Rectangle z w ⊆ {u : ℂ | -(1 : ℝ) < u.re} := by
    intro u hu
    have huBounds := (mem_Rect hzRe hzIm u).mp hu
    have hzReal : z.re = 0 := by simp [z]
    change -(1 : ℝ) < u.re
    linarith [huBounds.1]
  have hFdiff : DifferentiableOn ℂ F (Rectangle z w) := by
    exact (differentiableOn_pintz2023MellinPoleFreeNumerator hN s).mono
      hRectSubset
  have hgHolo : HolomorphicOn g (Rectangle z w) := by
    exact (Complex.differentiableOn_dslope hpInterior).2 hFdiff
  have hPrincipal : Set.EqOn
      (pintz2023MellinContourIntegrand N s -
        fun u => pintz2023MellinWeight N (1 - s) / (u - p))
      g (Rectangle z w \ {p}) := by
    intro u hu
    have hup : u ≠ p := by simpa using hu.2
    have hSlope := sub_smul_dslope F p u
    change pintz2023MellinContourIntegrand N s u -
        pintz2023MellinWeight N (1 - s) / (u - p) = g u
    rw [pintz2023MellinContourIntegrand_eq_poleFree_div hup]
    have hFp : F p = pintz2023MellinWeight N (1 - s) := by
      simp [F, p, pintz2023MellinPoleFreeNumerator_at_pole]
    rw [← hFp]
    dsimp only [F, g]
    rw [← sub_div, ← hSlope]
    rw [smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hup)]
  have hResidue := ResidueTheoremOnRectangleWithSimplePole
    hzRe hzIm hpInterior hgHolo hPrincipal
  simpa [z, w, p] using hResidue

#print axioms pintz2023MellinWeight_eq
#print axioms pintz2023MellinContourIntegrand_eq_poleFree_div
#print axioms pintz2023Mellin_finite_rectangle

end

end GafniTao
