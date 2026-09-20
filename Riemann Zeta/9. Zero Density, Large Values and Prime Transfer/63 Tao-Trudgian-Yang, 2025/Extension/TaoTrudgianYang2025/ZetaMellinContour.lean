import TaoTrudgianYang2025.ZetaMellinEntry
import GuthMaynard.DFIPeriodicBounds

/-!
# The zeta-pole contribution in the coefficient-one Mellin entry

The exact contour shift retains the moving pole at `1-it`. The cutoff
is genuine and all analyticity and residue computations are proved.
-/

noncomputable section

open Complex Filter MeasureTheory Set Topology
open RiemannZeta.GuthMaynard
open scoped Interval

namespace TaoTrudgianYang2025

def zetaMellinIntegrand (g : ℝ → ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  riemannZeta (s + (t : ℂ) * I) * mellin g s

def zetaMellinNumerator (g : ℝ → ℂ) (t : ℝ) (s : ℂ) : ℂ :=
  regularizedRiemannZeta (s + (t : ℂ) * I) * mellin g s

theorem differentiable_zetaMellinNumerator {g : ℝ → ℂ}
    (hg : DFIVoronoiTestFunction g) (t : ℝ) : Differentiable ℂ (zetaMellinNumerator g t) := by
  intro s
  exact ((differentiableAt_regularizedRiemannZeta (s + (t : ℂ) * I)).comp s
    (differentiableAt_id.add_const _)).mul hg.differentiable_mellin.differentiableAt

theorem zetaMellinNumerator_at_pole (g : ℝ → ℂ) (t : ℝ) :
    zetaMellinNumerator g t (1 - (t : ℂ) * I) = mellin g (1 - (t : ℂ) * I) := by
  unfold zetaMellinNumerator
  rw [sub_add_cancel]
  simp [regularizedRiemannZeta]

theorem zetaMellinIntegrand_eq_quotient (g : ℝ → ℂ) (t : ℝ) {s : ℂ}
    (hs : s ≠ 1 - (t : ℂ) * I) :
    zetaMellinIntegrand g t s = zetaMellinNumerator g t s / (s - (1 - (t : ℂ) * I)) := by
  have harg : s + (t : ℂ) * I ≠ 1 := by intro h; apply hs; linear_combination h
  unfold zetaMellinIntegrand zetaMellinNumerator regularizedRiemannZeta
  rw [Function.update_of_ne harg]
  have hden : s - (1 - (t : ℂ) * I) ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

/-- Exact residue in the complete rectangle from the critical line to
`Re s = 3/2`. The pole height is `-t`, not `t`. -/
theorem zetaMellin_finite_rectangle {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
    (t : ℝ) {R : ℝ} (hR : |t| < R) :
    RectangleIntegral' (zetaMellinIntegrand g t)
      ((1 / 2 : ℂ) - (R : ℂ) * I) ((3 / 2 : ℂ) + (R : ℂ) * I) =
        mellin g (1 - (t : ℂ) * I) := by
  let z : ℂ := (1 / 2 : ℂ) - (R : ℂ) * I
  let w : ℂ := (3 / 2 : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - (t : ℂ) * I
  let F := zetaMellinNumerator g t
  have hRpos : 0 < R := (abs_nonneg t).trans_lt hR
  have hzRe : z.re ≤ w.re := by norm_num [z, w]
  have hzIm : z.im ≤ w.im := by simp [z, w]; linarith
  have hp : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · norm_num [p, z, w]
    · norm_num [p, z, w]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hdiff : DifferentiableOn ℂ F (Rectangle z w) :=
    (differentiable_zetaMellinNumerator hg t).differentiableOn
  have hdslope : HolomorphicOn (dslope F p) (Rectangle z w) :=
    (Complex.differentiableOn_dslope hp).2 hdiff
  have hFp : F p = mellin g p := zetaMellinNumerator_at_pole g t
  have hprincipal : Set.EqOn
      (zetaMellinIntegrand g t - fun s => mellin g p / (s - p)) (dslope F p)
      (Rectangle z w \ {p}) := by
    intro s hs
    have hsp : s ≠ p := hs.2
    change zetaMellinIntegrand g t s - mellin g p / (s - p) = dslope F p s
    rw [zetaMellinIntegrand_eq_quotient g t hsp, ← hFp, ← sub_div]
    change (F s - F p) / (s - p) = dslope F p s
    rw [← sub_smul_dslope F p s, smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]
  exact ResidueTheoremOnRectangleWithSimplePole hzRe hzIm hp hdslope hprincipal

end TaoTrudgianYang2025
