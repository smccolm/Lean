import RiemannZeta.GuthMaynard.HughesYoungCentralMaster
import RiemannZeta.GuthMaynard.HughesYoungShiftRegularization
import RiemannZeta.External.PNT.ResidueCalcOnRectangles

open Complex Filter Metric Set
open scoped BigOperators Interval Topology

noncomputable section

set_option maxHeartbeats 2000000

namespace RiemannZeta.GuthMaynard

/-!
# The moving equation-(98) residue

The auxiliary shifts are retained while the complete arithmetic series is
shifted.  Consequently the crossed singularity is the simple pole
`W = (1+z+w)/2`; auxiliary differentiation is performed only after this
residue identity has been established.
-/

/-- The `hughesYoungCentralMovingPole` definition used by the source-facing construction in `HughesYoungCentralResidue`. -/
noncomputable def hughesYoungCentralMovingPole (z w : ℂ) : ℂ :=
  (1 + z + w) / 2

theorem two_mul_hughesYoungCentralMovingPole_sub (z w : ℂ) :
    2 * hughesYoungCentralMovingPole z w - z - w = 1 := by
  unfold hughesYoungCentralMovingPole
  ring

/-- The named meromorphic master function used by the rectangle theorem. -/
noncomputable def hughesYoungCompletePositiveCentralMeromorphic
    (T t : ℝ) (h k a b : ℕ) (z w W : ℂ) : ℂ :=
  riemannZeta (2 * W - z - w) *
    hughesYoungCompletePositiveCentralPoleFree T t h k a b W z w

theorem hughesYoungCompletePositiveCentralMaster_eq_meromorphic
    (T t : ℝ) (h k a b : ℕ) (W z w : ℂ) :
    hughesYoungCompletePositiveCentralMaster T t h k a b W z w =
      hughesYoungCompletePositiveCentralMeromorphic
        T t h k a b z w W := by
  exact hughesYoungCompletePositiveCentralMaster_eq_pole_mul
    T t h k a b W z w

private theorem differentiableAt_hughesYoungCompletePositiveCentralPoleFree_movingPole
    (T t : ℝ) (h k a b : ℕ) {z w : ℂ}
    (hz : ‖z‖ < (1 / 8 : ℝ)) (hw : ‖w‖ < (1 / 8 : ℝ)) :
    DifferentiableAt ℂ
      (fun W => hughesYoungCompletePositiveCentralPoleFree
        T t h k a b W z w) (hughesYoungCentralMovingPole z w) := by
  let p : ℂ := hughesYoungCentralMovingPole z w
  have hzRe : |z.re| < (1 / 8 : ℝ) :=
    (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < (1 / 8 : ℝ) :=
    (abs_re_le_norm w).trans_lt hw
  have hpRe : p.re = (1 + z.re + w.re) / 2 := by
    dsimp only [p, hughesYoungCentralMovingPole]
    norm_num [Complex.div_re]
  have hp0 : 0 < p.re := by
    rw [hpRe]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hp3 : p.re < 3 / 2 := by
    rw [hpRe]
    linarith [le_abs_self z.re, le_abs_self w.re]
  have hzeta : 1 < (1 + 2 * p + z + w : ℂ).re := by
    dsimp only [p, hughesYoungCentralMovingPole]
    norm_num [Complex.div_re, Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hzetaDen : 1 ≤ (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hregular : (-2 - 2 * z - 2 * w : ℂ).re < 0 := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hleft : (z - w - 2 * p : ℂ).re < 0 := by
    dsimp only [p, hughesYoungCentralMovingPole]
    norm_num [Complex.div_re, Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hright : (w - z - 2 * p : ℂ).re < 0 := by
    dsimp only [p, hughesYoungCentralMovingPole]
    norm_num [Complex.div_re, Complex.mul_re]
    linarith [le_abs_self w.re, neg_abs_le z.re]
  exact differentiableAt_hughesYoungCompletePositiveCentralPoleFree
    T t h k a b hp0 hp3 hzeta hzetaDen hregular hleft hright

/-- Exact residue of the named meromorphic master at its moving pole. -/
theorem residue_hughesYoungCompletePositiveCentralMeromorphic
    (T t : ℝ) (h k a b : ℕ) {z w : ℂ}
    (hz : ‖z‖ < (1 / 8 : ℝ)) (hw : ‖w‖ < (1 / 8 : ℝ)) :
    residue (hughesYoungCompletePositiveCentralMeromorphic
        T t h k a b z w) (hughesYoungCentralMovingPole z w) =
      (2 : ℂ)⁻¹ *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w := by
  have hres := residue_riemannZeta_affine_mul
      (a := (2 : ℂ)) (b := -z - w)
      (p := hughesYoungCentralMovingPole z w)
      (f := fun W => hughesYoungCompletePositiveCentralPoleFree
        T t h k a b W z w)
      (by norm_num : (2 : ℂ) ≠ 0)
      (by unfold hughesYoungCentralMovingPole; ring)
      ((differentiableAt_hughesYoungCompletePositiveCentralPoleFree_movingPole
        T t h k a b hz hw).continuousAt)
  have hfun : hughesYoungCompletePositiveCentralMeromorphic
      T t h k a b z w =
      (fun W => riemannZeta (2 * W + (-z - w)) *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b W z w) := by
    funext W
    unfold hughesYoungCompletePositiveCentralMeromorphic
    congr 2
    ring
  rw [hfun]
  exact hres

/-- Exact residue of the complete master integrand at its moving zeta pole. -/
theorem residue_hughesYoungCompletePositiveCentralMaster
    (T t : ℝ) (h k a b : ℕ) {z w : ℂ}
    (hz : ‖z‖ < (1 / 8 : ℝ)) (hw : ‖w‖ < (1 / 8 : ℝ)) :
    residue
      (fun W => hughesYoungCompletePositiveCentralMaster
        T t h k a b W z w) (hughesYoungCentralMovingPole z w) =
      (2 : ℂ)⁻¹ *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w := by
  have hfun :
      (fun W => hughesYoungCompletePositiveCentralMaster
        T t h k a b W z w) =
      hughesYoungCompletePositiveCentralMeromorphic
        T t h k a b z w := by
    funext W
    exact hughesYoungCompletePositiveCentralMaster_eq_meromorphic
      T t h k a b W z w
  calc
    residue (fun W => hughesYoungCompletePositiveCentralMaster
        T t h k a b W z w) (hughesYoungCentralMovingPole z w) =
      residue (hughesYoungCompletePositiveCentralMeromorphic
        T t h k a b z w) (hughesYoungCentralMovingPole z w) := by rw [hfun]
    _ = _ := residue_hughesYoungCompletePositiveCentralMeromorphic
      T t h k a b hz hw

/-- Entire divided-difference remainder after subtracting the moving zeta
principal part. -/
noncomputable def hughesYoungCentralZetaRemainder
    (z w W : ℂ) : ℂ :=
  dslope riemannZetaPoleRemoved 0
    (2 * (W - hughesYoungCentralMovingPole z w))

private theorem differentiable_dslope_entire
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ) :
    Differentiable ℂ (dslope F a) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope
    (s := Set.univ) (c := a) univ_mem).2 hF.differentiableOn

theorem differentiable_hughesYoungCentralZetaRemainder
    (z w : ℂ) :
    Differentiable ℂ (hughesYoungCentralZetaRemainder z w) := by
  unfold hughesYoungCentralZetaRemainder
  exact (differentiable_dslope_entire
      differentiable_riemannZetaPoleRemoved 0).comp (by fun_prop)

/-- Away from the moving pole, the zeta factor is its principal part plus
the entire divided-difference remainder. -/
theorem hughesYoungCentralZeta_eq_principal_add_remainder
    (z w : ℂ) {W : ℂ}
    (hW : W ≠ hughesYoungCentralMovingPole z w) :
    riemannZeta (2 * W - z - w) =
      (2 : ℂ)⁻¹ / (W - hughesYoungCentralMovingPole z w) +
        hughesYoungCentralZetaRemainder z w W := by
  let p := hughesYoungCentralMovingPole z w
  let u := W - p
  have hu : u ≠ 0 := sub_ne_zero.mpr hW
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have h2u : 2 * u ≠ 0 := mul_ne_zero htwo hu
  have haffine : 2 * W - z - w = 1 + 2 * u := by
    dsimp only [u, p]
    unfold hughesYoungCentralMovingPole
    ring
  have hpole := riemannZetaPoleRemoved_eq_mul_riemannZeta h2u
  rw [haffine]
  change riemannZeta (1 + 2 * u) =
    (2 : ℂ)⁻¹ / u + dslope riemannZetaPoleRemoved 0 (2 * u)
  rw [dslope_of_ne riemannZetaPoleRemoved h2u]
  simp only [slope, sub_zero, smul_eq_mul, vsub_eq_sub,
    riemannZetaPoleRemoved_zero]
  rw [hpole]
  field_simp [hu, h2u]
  ring

/-- Holomorphic remainder after subtracting the full moving principal part,
including the variation of the pole-free numerator. -/
noncomputable def hughesYoungCompletePositiveCentralRegularPart
    (T t : ℝ) (h k a b : ℕ) (z w W : ℂ) : ℂ :=
  hughesYoungCentralZetaRemainder z w W *
      hughesYoungCompletePositiveCentralPoleFree T t h k a b W z w +
    (2 : ℂ)⁻¹ * dslope
      (fun V => hughesYoungCompletePositiveCentralPoleFree
        T t h k a b V z w)
      (hughesYoungCentralMovingPole z w) W

theorem hughesYoungCompletePositiveCentralMeromorphic_sub_principal
    (T t : ℝ) (h k a b : ℕ) (z w : ℂ) {W : ℂ}
    (hW : W ≠ hughesYoungCentralMovingPole z w) :
    hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w W -
        ((2 : ℂ)⁻¹ *
          hughesYoungCompletePositiveCentralPoleFree T t h k a b
            (hughesYoungCentralMovingPole z w) z w) /
          (W - hughesYoungCentralMovingPole z w) =
      hughesYoungCompletePositiveCentralRegularPart
        T t h k a b z w W := by
  rw [show hughesYoungCompletePositiveCentralMeromorphic
      T t h k a b z w W =
        riemannZeta (2 * W - z - w) *
          hughesYoungCompletePositiveCentralPoleFree
            T t h k a b W z w by rfl]
  rw [hughesYoungCentralZeta_eq_principal_add_remainder z w hW]
  unfold hughesYoungCompletePositiveCentralRegularPart
  rw [dslope_of_ne _ hW]
  simp only [slope, smul_eq_mul, vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hW]
  ring

private theorem differentiableOn_hughesYoungCompletePositiveCentralPoleFree_rectangle
    (T t : ℝ) (h k a b : ℕ) {z w : ℂ} {δ H : ℝ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ < δ / 4) (hw : ‖w‖ < δ / 4) (hH : 0 ≤ H) :
    DifferentiableOn ℂ
      (fun W => hughesYoungCompletePositiveCentralPoleFree
        T t h k a b W z w)
      (Rectangle ((δ : ℂ) - (H : ℂ) * I)
        ((1 : ℂ) + (H : ℂ) * I)) := by
  have hδ1 : δ ≤ 1 := hδ4.le.trans (by norm_num)
  have hRe : ((δ : ℂ) - (H : ℂ) * I).re ≤
      ((1 : ℂ) + (H : ℂ) * I).re := by simp; exact hδ1
  have hIm : ((δ : ℂ) - (H : ℂ) * I).im ≤
      ((1 : ℂ) + (H : ℂ) * I).im := by simp; linarith
  have hzRe : |z.re| < δ / 4 := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < δ / 4 := (abs_re_le_norm w).trans_lt hw
  intro W hW
  have hBounds := (mem_Rect hRe hIm W).mp hW
  have hWlower : δ ≤ W.re := by simpa using hBounds.1
  have hWupper : W.re ≤ 1 := by simpa using hBounds.2.1
  have hW0 : 0 < W.re := hδ0.trans_le hWlower
  have hW3 : W.re < 3 / 2 := hWupper.trans_lt (by norm_num)
  have hzeta : 1 < (1 + 2 * W + z + w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hzetaDen : 1 ≤ (2 + 2 * z + 2 * w : ℂ).re := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hregular : (-2 - 2 * z - 2 * w : ℂ).re < 0 := by
    norm_num [Complex.mul_re]
    linarith [neg_abs_le z.re, neg_abs_le w.re]
  have hleft : (z - w - 2 * W : ℂ).re < 0 := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self z.re, neg_abs_le w.re]
  have hright : (w - z - 2 * W : ℂ).re < 0 := by
    norm_num [Complex.mul_re]
    linarith [le_abs_self w.re, neg_abs_le z.re]
  exact (differentiableAt_hughesYoungCompletePositiveCentralPoleFree
    T t h k a b hW0 hW3 hzeta hzetaDen hregular hleft hright).differentiableWithinAt

/-- Finite-height contour displacement of the complete central master.  It
crosses exactly the moving simple pole and keeps both auxiliary shifts
generic. -/
theorem hughesYoungCompletePositiveCentralMaster_finiteRectangle
    (T t : ℝ) (h k a b : ℕ) {z w : ℂ} {δ H : ℝ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ < δ / 4) (hw : ‖w‖ < δ / 4) (hH : 1 ≤ H) :
    RectangleIntegral'
        (hughesYoungCompletePositiveCentralMeromorphic
          T t h k a b z w)
        ((δ : ℂ) - (H : ℂ) * I)
        ((1 : ℂ) + (H : ℂ) * I) =
      (2 : ℂ)⁻¹ *
        hughesYoungCompletePositiveCentralPoleFree T t h k a b
          (hughesYoungCentralMovingPole z w) z w := by
  let L : ℂ := (δ : ℂ) - (H : ℂ) * I
  let R : ℂ := (1 : ℂ) + (H : ℂ) * I
  let p : ℂ := hughesYoungCentralMovingPole z w
  let F : ℂ → ℂ := fun W =>
    hughesYoungCompletePositiveCentralPoleFree T t h k a b W z w
  let A : ℂ := (2 : ℂ)⁻¹ * F p
  let f : ℂ → ℂ :=
    hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
  let g : ℂ → ℂ :=
    hughesYoungCompletePositiveCentralRegularPart T t h k a b z w
  have hδ1 : δ ≤ 1 := hδ4.le.trans (by norm_num)
  have hLRe : L.re ≤ R.re := by simp [L, R]; exact hδ1
  have hLIm : L.im ≤ R.im := by simp [L, R]; linarith
  have hzRe : |z.re| < δ / 4 := (abs_re_le_norm z).trans_lt hz
  have hwRe : |w.re| < δ / 4 := (abs_re_le_norm w).trans_lt hw
  have hzIm : |z.im| < δ / 4 := (abs_im_le_norm z).trans_lt hz
  have hwIm : |w.im| < δ / 4 := (abs_im_le_norm w).trans_lt hw
  have hpRe : p.re = (1 + z.re + w.re) / 2 := by
    dsimp only [p, hughesYoungCentralMovingPole]
    norm_num [Complex.div_re]
  have hpIm : p.im = (z.im + w.im) / 2 := by
    dsimp only [p, hughesYoungCentralMovingPole]
    norm_num [Complex.div_im]
  have hpInterior : Rectangle L R ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      uIoo_of_le hLRe, uIoo_of_le hLIm]
    constructor
    · constructor
      · simp only [L, sub_re, ofReal_re, mul_re, ofReal_im, I_re,
          I_im, mul_zero, zero_mul, sub_zero]
        rw [hpRe]
        linarith [neg_abs_le z.re, neg_abs_le w.re]
      · simp only [R, add_re, ofReal_re, mul_re, ofReal_im, I_re,
          I_im, mul_zero, zero_mul]
        rw [hpRe]
        norm_num
        nlinarith [le_abs_self z.re, le_abs_self w.re]
    · constructor
      · simp only [L, sub_im, ofReal_im, mul_im, I_im, ofReal_re,
          I_re, mul_one, mul_zero]
        rw [hpIm]
        have hδH : δ / 4 < H := by linarith
        linarith [neg_abs_le z.im, neg_abs_le w.im]
      · simp only [R, add_im, ofReal_im, mul_im, I_im, ofReal_re,
          I_re, mul_one, mul_zero]
        rw [hpIm]
        have hδH : δ / 4 < H := by linarith
        norm_num
        nlinarith [le_abs_self z.im, le_abs_self w.im]
  have hFdiff : DifferentiableOn ℂ F (Rectangle L R) := by
    simpa only [F, L, R] using
      differentiableOn_hughesYoungCompletePositiveCentralPoleFree_rectangle
        T t h k a b hδ0 hδ4 hz hw (le_trans (by norm_num) hH)
  have hSlope : DifferentiableOn ℂ (dslope F p) (Rectangle L R) :=
    (Complex.differentiableOn_dslope hpInterior).2 hFdiff
  have hZetaRem : DifferentiableOn ℂ
      (hughesYoungCentralZetaRemainder z w) (Rectangle L R) :=
    (differentiable_hughesYoungCentralZetaRemainder z w).differentiableOn
  have hg : HolomorphicOn g (Rectangle L R) := by
    dsimp only [g, hughesYoungCompletePositiveCentralRegularPart]
    exact (hZetaRem.mul hFdiff).add
      ((differentiableOn_const (c := (2 : ℂ)⁻¹)).mul hSlope)
  have hprincipal : Set.EqOn
      (f - fun W => A / (W - p)) g (Rectangle L R \ {p}) := by
    intro W hW
    have hWp : W ≠ p := by simpa using hW.2
    exact hughesYoungCompletePositiveCentralMeromorphic_sub_principal
      T t h k a b z w hWp
  have hres := ResidueTheoremOnRectangleWithSimplePole
    hLRe hLIm hpInterior hg hprincipal
  simpa only [L, R, p, F, A, f, g] using hres

/-- Expansion of the normalized rectangular contour into its horizontal
and vertical edges.  This normalization is the one used throughout the
Hughes--Young Mellin argument, so the vertical coefficient is exactly
`1 / (2 * pi)`. -/
private theorem hughesYoungRectangleIntegral'_eq_edges
    (f : ℂ → ℂ) (a b H : ℝ) :
    RectangleIntegral' f
        ((a : ℂ) - (H : ℂ) * I) ((b : ℂ) + (H : ℂ) * I) =
      HIntegral' f a b (-H) - HIntegral' f a b H +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-H)..H, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ u in (-H)..H, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact finite-height vertical displacement across the moving equation-(98)
pole.  No limiting argument, auxiliary specialization, or absolute-value
estimate has yet been made. -/
theorem hughesYoungCompletePositiveCentralMaster_finiteVerticalShift
    (T t : ℝ) (h k a b : ℕ) {z w : ℂ} {δ H : ℝ}
    (hδ0 : 0 < δ) (hδ4 : δ < 1 / 4)
    (hz : ‖z‖ < δ / 4) (hw : ‖w‖ < δ / 4) (hH : 1 ≤ H) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u in (-H)..H,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((1 : ℂ) + (u : ℂ) * I)) -
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u in (-H)..H,
          hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w
            ((δ : ℂ) + (u : ℂ) * I)) =
      (2 : ℂ)⁻¹ *
          hughesYoungCompletePositiveCentralPoleFree T t h k a b
            (hughesYoungCentralMovingPole z w) z w -
        HIntegral'
          (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
          δ 1 (-H) +
        HIntegral'
          (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
          δ 1 H := by
  have hrect := hughesYoungCompletePositiveCentralMaster_finiteRectangle
    T t h k a b hδ0 hδ4 hz hw hH
  change RectangleIntegral'
      (hughesYoungCompletePositiveCentralMeromorphic T t h k a b z w)
      ((δ : ℂ) - (H : ℂ) * I)
      (((1 : ℝ) : ℂ) + (H : ℂ) * I) = _ at hrect
  rw [hughesYoungRectangleIntegral'_eq_edges] at hrect
  linear_combination hrect

end RiemannZeta.GuthMaynard
