import GafniTao.FordKFiniteResidues

/-!
# Ford's finite `K(s)` rectangle

This is the finite-height residue identity underlying Ford's equations
`(I1)`--`(I2)`.  It deliberately precedes the horizontal-edge limit and the
Laplace inversion step.
-/

open Complex Set Filter Topology Asymptotics
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The pole at one together with all nontrivial zeta zeros in the finite
height window. -/
noncomputable def fordKSingularities (R : ℝ) : Finset ℂ :=
  insert 1 (zeroSet 0 R)

/-- Exact principal coefficient at each listed singularity. -/
noncomputable def fordKResidueCoefficient
    (s : ℂ) (F₀ : ℂ → ℂ) (p : ℂ) : ℂ :=
  if p = 1 then F₀ (s - 1)
  else -(analyticVanishingOrder riemannZeta p : ℂ) * F₀ (s - p)

/-- A zeta zero in Ford's finite rectangle is one of the actual source zero
set entries. -/
theorem mem_zeroSet_of_zeta_zero_of_fordKRectangle
    {alpha R : ℝ} (halpha : 1 < alpha) (hR : 0 ≤ R) {w : ℂ}
    (hwRect : w ∈ Rectangle
      ((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I)
      ((alpha : ℂ) + (R : ℂ) * I))
    (hwZeta : riemannZeta w = 0) :
    w ∈ zeroSet 0 R := by
  have hreBounds : -(1 / 2 : ℝ) ≤ w.re ∧ w.re ≤ alpha := by
    have h := hwRect.1
    simp only [Set.mem_preimage, sub_re, neg_re, ofReal_re, mul_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_re,
      add_zero] at h
    norm_num at h
    rw [Set.uIcc_of_le (by linarith : -(1 / 2 : ℝ) ≤ alpha)] at h
    exact h
  have himBounds : -R ≤ w.im ∧ w.im ≤ R := by
    have himMem := hwRect.2
    simp only [Set.mem_preimage, sub_im, neg_im, ofReal_im,
      mul_im, ofReal_re, I_im, I_re, zero_mul, mul_one, add_zero,
      add_im, neg_zero, zero_sub] at himMem
    norm_num at himMem
    rw [Set.uIcc_of_le (by linarith)] at himMem
    exact himMem
  have hstrip := zeta_zero_re_mem_of_neg_one_le (by linarith) hwZeta
  change w ∈ RiemannZeta.GuthMaynard.zerosInRect 0 1 (-R) R
  rw [RiemannZeta.GuthMaynard.zerosInRect,
    Set.Finite.mem_toFinset, Set.mem_inter_iff]
  refine ⟨(RiemannZeta.GuthMaynard.mem_ZeroRectangle 0 1 (-R) R w).2 ?_,
    hwZeta⟩
  exact ⟨hstrip.1, hstrip.2, himBounds.1, himBounds.2⟩

/-- Every finite Ford singularity lies strictly inside the contour when the
chosen height misses zero ordinates. -/
theorem fordKSingularities_mem_nhds
    {alpha R : ℝ} (halpha : 1 < alpha) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    ∀ p ∈ fordKSingularities R,
      Rectangle
        ((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I)
        ((alpha : ℂ) + (R : ℂ) * I) ∈ 𝓝 p := by
  intro p hp
  rw [rectangle_mem_nhds_iff, mem_reProdIm]
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, sub_zero, add_re, sub_im, mul_im, zero_add,
    add_im, neg_re, neg_im, mul_one, add_zero,
    neg_zero, zero_sub]
  rw [Set.uIoo_of_le (by linarith : -(1 / 2 : ℝ) ≤ alpha),
    Set.uIoo_of_le (by linarith : -R ≤ R)]
  simp only [Set.mem_Ioo]
  simp only [fordKSingularities, Finset.mem_insert] at hp
  rcases hp with rfl | hp
  · constructor <;> constructor <;> norm_num <;> linarith
  · have hd := mem_zeroSet_zero_data hp
    have him := hheight p hp
    rw [abs_lt] at him
    exact ⟨⟨by linarith, by linarith⟩, ⟨him.1, him.2⟩⟩

/-- Away from the displayed finite singularities, Ford's surrogate
integrand is holomorphic throughout the closed rectangle. -/
theorem fordKSurrogateIntegrand_holomorphicOn_rectangle_diff
    {s : ℂ} {F₀ : ℂ → ℂ} {alpha R : ℝ}
    (halpha : 1 < alpha) (hR : 0 ≤ R) (has : alpha < s.re)
    (hF₀ : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) :
    HolomorphicOn (fordKSurrogateIntegrand s F₀)
      (Rectangle
          ((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I)
          ((alpha : ℂ) + (R : ℂ) * I) \
        (fordKSingularities R : Set ℂ)) := by
  intro w hw
  have hw1 : w ≠ 1 := by
    intro h
    apply hw.2
    simp [h, fordKSingularities]
  have hwRe : w.re ≤ alpha := by
    have h := hw.1.1
    simp only [Set.mem_preimage, sub_re, neg_re, ofReal_re, mul_re,
      ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_re,
      add_zero] at h
    norm_num at h
    rw [Set.uIcc_of_le (by linarith : -(1 / 2 : ℝ) ≤ alpha)] at h
    exact h.2
  have hswRe : 0 < (s - w).re := by simp only [sub_re]; linarith
  have hsur : sharpZetaSurrogate w ≠ 0 := by
    intro hzero
    have hzeta : riemannZeta w = 0 :=
      (sharpZetaSurrogate_eq_zero_iff hw1).mp hzero
    have hmem : w ∈ zeroSet 0 R :=
      mem_zeroSet_of_zeta_zero_of_fordKRectangle halpha hR hw.1 hzeta
    apply hw.2
    simp [fordKSingularities, hmem]
  exact (differentiableAt_fordKSurrogateIntegrand
    (hF₀ (s - w) hswRe) hw1 hsur).differentiableWithinAt

/-- Normalized finite rectangle equals the pole coefficient plus the exact
multiplicity-weighted zero coefficients. -/
theorem fordK_rectangleIntegral_eq_residue_sum
    {s : ℂ} {F₀ : ℂ → ℂ} {alpha R : ℝ}
    (halpha : 1 < alpha) (hR : 0 < R) (has : alpha < s.re)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R)
    (hF₀ : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) :
    RectangleIntegral' (fordKSurrogateIntegrand s F₀)
        ((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I)
        ((alpha : ℂ) + (R : ℂ) * I) =
      ∑ p ∈ fordKSingularities R, fordKResidueCoefficient s F₀ p := by
  apply residueTheorem_finset
      (S := fordKSingularities R)
      (A := fordKResidueCoefficient s F₀)
  · simp
    linarith
  · simp
    linarith
  · exact fordKSingularities_mem_nhds halpha hR hheight
  · exact fordKSurrogateIntegrand_holomorphicOn_rectangle_diff
      halpha hR.le has hF₀
  · intro p hp
    have hpRe : p.re ≤ alpha := by
      have hpRect := fordKSingularities_mem_nhds halpha hR hheight p hp
      have hpMem : p ∈ Rectangle
          ((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I)
          ((alpha : ℂ) + (R : ℂ) * I) :=
        mem_of_mem_nhds hpRect
      have h := hpMem.1
      simp only [Set.mem_preimage, sub_re, neg_re, ofReal_re, mul_re,
        ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero, add_re,
        add_zero] at h
      norm_num at h
      rw [Set.uIcc_of_le (by linarith : -(1 / 2 : ℝ) ≤ alpha)] at h
      exact h.2
    have hspRe : 0 < (s - p).re := by simp only [sub_re]; linarith
    have hdiff := hF₀ (s - p) hspRe
    simp only [fordKSingularities, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · simpa [fordKResidueCoefficient] using
        (fordKSurrogateIntegrand_near_one (s := s) hdiff)
    · have hd := mem_zeroSet_zero_data hp
      have hp1 : p ≠ 1 := by
        intro h
        subst p
        exact riemannZeta_one_ne_zero hd.2.2.2.2
      simpa [fordKResidueCoefficient, hp1] using
        (fordKSurrogateIntegrand_near_zero
          (s := s) hd.2.2.2.2 hdiff)

/-- Evaluation of the finite coefficient sum in Ford's source notation. -/
theorem sum_fordKResidueCoefficient (s : ℂ) (F₀ : ℂ → ℂ) (R : ℝ) :
    (∑ p ∈ fordKSingularities R, fordKResidueCoefficient s F₀ p) =
      F₀ (s - 1) -
        ∑ rho ∈ zeroSet 0 R,
          (analyticVanishingOrder riemannZeta rho : ℂ) * F₀ (s - rho) := by
  classical
  have hone : (1 : ℂ) ∉ zeroSet 0 R := by
    intro h
    exact riemannZeta_one_ne_zero (mem_zeroSet_zero_data h).2.2.2.2
  rw [fordKSingularities, Finset.sum_insert hone]
  simp only [fordKResidueCoefficient, if_pos]
  have hsum :
      (∑ rho ∈ zeroSet 0 R,
        if rho = 1 then F₀ (s - 1)
        else -(analyticVanishingOrder riemannZeta rho : ℂ) * F₀ (s - rho)) =
        -(∑ rho ∈ zeroSet 0 R,
          (analyticVanishingOrder riemannZeta rho : ℂ) * F₀ (s - rho)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro rho hrho
    have hrho1 : rho ≠ 1 := by
      intro h
      exact hone (h ▸ hrho)
    simp [hrho1]
  rw [hsum]
  ring

/-- The finite Ford rectangle in its exact source residue form. -/
theorem fordK_rectangleIntegral_eq_explicit_sum
    {s : ℂ} {F₀ : ℂ → ℂ} {alpha R : ℝ}
    (halpha : 1 < alpha) (hR : 0 < R) (has : alpha < s.re)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R)
    (hF₀ : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) :
    RectangleIntegral' (fordKSurrogateIntegrand s F₀)
        ((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I)
        ((alpha : ℂ) + (R : ℂ) * I) =
      F₀ (s - 1) -
        ∑ rho ∈ zeroSet 0 R,
          (analyticVanishingOrder riemannZeta rho : ℂ) * F₀ (s - rho) := by
  rw [fordK_rectangleIntegral_eq_residue_sum halpha hR has hheight hF₀,
    sum_fordKResidueCoefficient]

end

end GafniTao
