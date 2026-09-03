import GafniTao.HeathBrownTriangularKernel

/-!
# Removing the last-coordinate wrap in the localized count

This is the source step immediately after the choice of the block parameter
`K`: once the last derivative-coordinate difference is at most `1/2`, its
nearest-integer condition is an ordinary absolute-value condition.  The lower
derivative bound then forces the two source indices to be close.
-/

namespace GafniTao

noncomputable section

theorem heathBrownPairCountTwo_last_coordinate_abs_le
    {N k H K : ℕ} {f : ℝ → ℝ} {m n : ℕ}
    (hp : (m, n) ∈ heathBrownPairCountTwo N k H K f)
    (hspread :
      |heathBrownDerivativeCoordinate f (k - 1) m -
        heathBrownDerivativeCoordinate f (k - 1) n| ≤ 1 / 2) :
    |heathBrownDerivativeCoordinate f (k - 1) m -
        heathBrownDerivativeCoordinate f (k - 1) n| ≤
      4 * (((H : ℝ) ^ (k - 1))⁻¹) := by
  rw [mem_heathBrownPairCountTwo] at hp
  exact abs_le_of_heathBrownDistanceToInteger_le_of_abs_le_half
    hp.2.2.2.2.2.2 hspread

/-- Exact real-index separation forced by the last coordinate of a localized
pair.  Instantiating `mu = lambda/(k-1)!` gives the displayed source range for
the difference `d`. -/
theorem heathBrownPairCountTwo_index_separation
    {N k H K : ℕ} {f : ℝ → ℝ} {m n : ℕ} {mu : ℝ}
    (hmuPos : 0 < mu)
    (hg : ContinuousOn
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Icc 0 (N : ℝ)))
    (hgd : DifferentiableOn ℝ
      (fun x => heathBrownDerivativeCoordinate f (k - 1) x)
      (Set.Ioo 0 (N : ℝ)))
    (hderivLower : ∀ x ∈ Set.Ioo (0 : ℝ) (N : ℝ),
      mu ≤ deriv (fun y => heathBrownDerivativeCoordinate f (k - 1) y) x)
    (hp : (m, n) ∈ heathBrownPairCountTwo N k H K f)
    (hspread :
      |heathBrownDerivativeCoordinate f (k - 1) m -
        heathBrownDerivativeCoordinate f (k - 1) n| ≤ 1 / 2) :
    |(m : ℝ) - n| ≤
      (4 * (((H : ℝ) ^ (k - 1))⁻¹)) / mu := by
  have hpMem := hp
  rw [mem_heathBrownPairCountTwo] at hp
  have hmN : m ≤ N := hp.2.1
  have hnN : n ≤ N := hp.2.2.2.1
  have hmI : (m : ℝ) ∈ Set.Icc (0 : ℝ) N :=
    ⟨by positivity, by exact_mod_cast hmN⟩
  have hnI : (n : ℝ) ∈ Set.Icc (0 : ℝ) N :=
    ⟨by positivity, by exact_mod_cast hnN⟩
  have hcoord := heathBrownPairCountTwo_last_coordinate_abs_le hpMem hspread
  rcases le_total m n with hmn | hnm
  · have hslope := heathBrown_lower_slope hg hgd hderivLower hmI hnI
      (by exact_mod_cast hmn)
    have hdiffnonneg :
        0 ≤ heathBrownDerivativeCoordinate f (k - 1) n -
          heathBrownDerivativeCoordinate f (k - 1) m := by
      have hindex : 0 ≤ (n : ℝ) - m :=
        sub_nonneg.mpr (by exact_mod_cast hmn)
      nlinarith
    have hupper :
        heathBrownDerivativeCoordinate f (k - 1) n -
          heathBrownDerivativeCoordinate f (k - 1) m ≤
            4 * (((H : ℝ) ^ (k - 1))⁻¹) := by
      rw [← abs_of_nonneg hdiffnonneg, abs_sub_comm]
      exact hcoord
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hmn)), neg_sub,
      div_eq_mul_inv]
    have hmuInv : mu * mu⁻¹ = 1 := by field_simp
    have hinvPos : 0 < mu⁻¹ := inv_pos.mpr hmuPos
    nlinarith [mul_le_mul_of_nonneg_right hslope hinvPos.le]
  · have hslope := heathBrown_lower_slope hg hgd hderivLower hnI hmI
      (by exact_mod_cast hnm)
    have hdiffnonneg :
        0 ≤ heathBrownDerivativeCoordinate f (k - 1) m -
          heathBrownDerivativeCoordinate f (k - 1) n := by
      have hindex : 0 ≤ (m : ℝ) - n :=
        sub_nonneg.mpr (by exact_mod_cast hnm)
      nlinarith
    have hupper :
        heathBrownDerivativeCoordinate f (k - 1) m -
          heathBrownDerivativeCoordinate f (k - 1) n ≤
            4 * (((H : ℝ) ^ (k - 1))⁻¹) := by
      rw [← abs_of_nonneg hdiffnonneg]
      exact hcoord
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hnm)),
      div_eq_mul_inv]
    have hmuInv : mu * mu⁻¹ = 1 := by field_simp
    have hinvPos : 0 < mu⁻¹ := inv_pos.mpr hmuPos
    nlinarith [mul_le_mul_of_nonneg_right hslope hinvPos.le]

#print axioms heathBrownPairCountTwo_last_coordinate_abs_le
#print axioms heathBrownPairCountTwo_index_separation

end

end GafniTao
