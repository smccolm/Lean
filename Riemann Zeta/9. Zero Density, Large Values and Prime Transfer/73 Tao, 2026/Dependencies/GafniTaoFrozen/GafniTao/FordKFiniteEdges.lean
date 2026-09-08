import GafniTao.FordLaplaceSource

/-!
# Oriented edges of Ford's finite `K(s)` rectangle

This is the exact finite-height rearrangement of the residue theorem.  It
keeps both horizontal edges and the left edge visible; their limiting bounds
are separate obligations.
-/

open Complex Set Filter Topology Asymptotics
open RiemannZeta.GuthMaynard
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Ford's right vertical edge equals the finite zero/pole residue sum plus
the other three oriented edges. -/
theorem fordK_rightEdge_eq_residues_add_edges
    {s : ℂ} {F₀ : ℂ → ℂ} {alpha R : ℝ}
    (halpha : 1 < alpha) (hR : 0 < R) (has : alpha < s.re)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R)
    (hF₀ : ∀ z : ℂ, 0 < z.re → DifferentiableAt ℂ F₀ z) :
    VIntegral' (fordKSurrogateIntegrand s F₀) alpha (-R) R =
      F₀ (s - 1) -
          ∑ rho ∈ zeroSet 0 R,
            (analyticVanishingOrder riemannZeta rho : ℂ) * F₀ (s - rho) -
        HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha (-R) +
        HIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) alpha R +
        VIntegral' (fordKSurrogateIntegrand s F₀) (-(1 / 2)) (-R) R := by
  have hrect := fordK_rectangleIntegral_eq_explicit_sum
    (s := s) (F₀ := F₀) halpha hR has hheight hF₀
  have hreLeft :
      (((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I).re) = -(1 / 2 : ℝ) := by
    norm_num
  have hreRight : (((alpha : ℂ) + (R : ℂ) * I).re) = alpha := by
    simp
  have himLeft :
      (((-(1 / 2 : ℝ) : ℂ) - (R : ℂ) * I).im) = -R := by
    simp
  have himRight : (((alpha : ℂ) + (R : ℂ) * I).im) = R := by
    simp
  simp only [RectangleIntegral', RectangleIntegral, HIntegral', VIntegral',
    smul_eq_mul] at hrect ⊢
  rw [hreLeft, hreRight, himLeft, himRight] at hrect
  linear_combination hrect

end

end GafniTao
