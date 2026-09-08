import GafniTao.SharpPerronResidueAssembly
import GafniTao.SharpPerronOptimalLine

/-!
# The finite sharp-Perron zeta rectangle

This is the global contour identity behind the sharp truncated explicit
formula.  The contour is shifted to `Re s = -1`, so the finite singular set
is exactly the origin, the pole at one, and the nontrivial zeros in the
closed critical strip.  The strict height hypothesis rules out a zero on a
horizontal edge; it will later be supplied by the good-height construction.
-/

open Complex Set Filter Asymptotics Topology
open RiemannZeta.GuthMaynard

noncomputable section

namespace GafniTao

/-- The exact finite singular set for the sharp-Perron rectangle. -/
noncomputable def sharpPerronSingularities (R : ℝ) : Finset ℂ :=
  insert 0 (insert 1 (zeroSet 0 R))

private theorem zero_mem_sharpPerronSingularities (R : ℝ) :
    (0 : ℂ) ∈ sharpPerronSingularities R := by
  simp [sharpPerronSingularities]

private theorem one_mem_sharpPerronSingularities (R : ℝ) :
    (1 : ℂ) ∈ sharpPerronSingularities R := by
  simp [sharpPerronSingularities]

/-- Every zero in the `Re s ≥ -1` rectangle belongs to the finite source
zero set. -/
theorem mem_zeroSet_of_zeta_zero_of_rectangle
    {y R : ℝ} (hy : 1 < y) (hR : 0 ≤ R) {s : ℂ}
    (hsRect : s ∈ Rectangle
      ((-1 : ℂ) - (R : ℂ) * I)
      ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I))
    (hsZeta : riemannZeta s = 0) :
    s ∈ zeroSet 0 R := by
  have hc : 1 < sharpPerronAbscissa y := one_lt_sharpPerronAbscissa hy
  have hreBounds : -1 ≤ s.re ∧ s.re ≤ sharpPerronAbscissa y := by
    simpa [Rectangle, mem_reProdIm, Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
      sharpPerronAbscissa y)] using hsRect.1
  have himBounds : -R ≤ s.im ∧ s.im ≤ R := by
    have himMem := hsRect.2
    simp only [Set.mem_preimage, sub_im, neg_im, one_im, ofReal_im,
      mul_im, ofReal_re, I_im, I_re, zero_mul, mul_one, add_zero,
      add_im, neg_zero, zero_sub] at himMem
    norm_num at himMem
    rw [Set.uIcc_of_le (by linarith : -R ≤ R)] at himMem
    exact himMem
  have hstrip := zeta_zero_re_mem_of_neg_one_le hreBounds.1 hsZeta
  change s ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-R) R
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff]
  refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-R) R s).2 ?_,
    hsZeta⟩
  exact ⟨hstrip.1, hstrip.2, himBounds.1, himBounds.2⟩

/-- Every listed singularity is strictly inside the contour. -/
theorem sharpPerronSingularities_mem_nhds
    {y R : ℝ} (hy : 1 < y) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    ∀ p ∈ sharpPerronSingularities R,
      Rectangle
        ((-1 : ℂ) - (R : ℂ) * I)
        ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I) ∈ 𝓝 p := by
  intro p hp
  have hc : 1 < sharpPerronAbscissa y := one_lt_sharpPerronAbscissa hy
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_re, sub_im, mul_im, zero_add,
    add_im, neg_re, neg_im, one_re, one_im, mul_one, add_zero,
    neg_zero, zero_sub]
  rw [Set.uIoo_of_le (by linarith : (-1 : ℝ) ≤ sharpPerronAbscissa y),
    Set.uIoo_of_le (by linarith : -R ≤ R)]
  simp only [Set.mem_Ioo]
  simp only [sharpPerronSingularities, Finset.mem_insert] at hp
  rcases hp with rfl | rfl | hp
  · constructor <;> constructor <;> simp <;> linarith
  · constructor <;> constructor <;> simp <;> linarith
  · have hd := mem_zeroSet_zero_data hp
    have him := hheight p hp
    rw [abs_lt] at him
    exact ⟨⟨by linarith, by linarith⟩, ⟨him.1, him.2⟩⟩

/-- Away from the finite singular set, the surrogate Perron integrand is
holomorphic throughout the closed rectangle. -/
theorem sharpZetaPerronIntegrand_holomorphicOn_rectangle_diff
    {y R : ℝ} (hy : 1 < y) (hR : 0 ≤ R) :
    HolomorphicOn (sharpZetaPerronIntegrand y)
      (Rectangle
          ((-1 : ℂ) - (R : ℂ) * I)
          ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I) \
        (sharpPerronSingularities R : Set ℂ)) := by
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h
    apply hs.2
    simpa [h] using zero_mem_sharpPerronSingularities R
  have hs1 : s ≠ 1 := by
    intro h
    apply hs.2
    simpa [h] using one_mem_sharpPerronSingularities R
  have hsur : sharpZetaSurrogate s ≠ 0 := by
    intro hzero
    have hzeta : riemannZeta s = 0 :=
      (sharpZetaSurrogate_eq_zero_iff hs1).mp hzero
    have hmem : s ∈ zeroSet 0 R :=
      mem_zeroSet_of_zeta_zero_of_rectangle hy hR hs.1 hzeta
    apply hs.2
    simp [sharpPerronSingularities, hmem]
  have hy0 : 0 < y := by linarith
  exact ((differentiableAt_sharpSurrogateLogPerron (y := y) hy0 hs0 hsur).add
    (differentiableAt_sharpPerronPoleCorrection (y := y) hy0 hs0 hs1)).differentiableWithinAt

/-- The normalized boundary integral equals the sum of all exact principal
part coefficients. -/
theorem sharpZetaPerron_rectangleIntegral_eq_residue_sum
    {y R : ℝ} (hy : 1 < y) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    RectangleIntegral' (sharpZetaPerronIntegrand y)
        ((-1 : ℂ) - (R : ℂ) * I)
        ((sharpPerronAbscissa y : ℂ) + (R : ℂ) * I) =
      ∑ p ∈ sharpPerronSingularities R,
        sharpZetaPerronResidueCoefficient y p := by
  apply residueTheorem_finset
      (S := sharpPerronSingularities R)
      (A := sharpZetaPerronResidueCoefficient y)
  · simp
    linarith [one_lt_sharpPerronAbscissa hy]
  · simp
    linarith
  · exact sharpPerronSingularities_mem_nhds hy hR hheight
  · exact sharpZetaPerronIntegrand_holomorphicOn_rectangle_diff hy hR.le
  · intro p hp
    have hy0 : 0 < y := by linarith
    simp only [sharpPerronSingularities, Finset.mem_insert] at hp
    rcases hp with rfl | rfl | hp
    · exact sharpZetaPerronIntegrand_near_origin hy0
    · exact sharpZetaPerronIntegrand_near_one hy0
    · have hd := mem_zeroSet_zero_data hp
      exact sharpZetaPerronIntegrand_near_nontrivial_zero hy0
        (by intro h; subst p; norm_num [riemannZeta_zero] at hd)
        (by intro h; subst p; exact riemannZeta_one_ne_zero hd.2.2.2.2)
        hd.2.2.2.2

end GafniTao
