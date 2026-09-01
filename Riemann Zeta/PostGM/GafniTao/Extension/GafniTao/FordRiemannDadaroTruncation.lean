import GafniTao.FordTheorem2Unshifted

/-!
# Dadaro truncation aligned with Ford's ordinary zeta sum

For the first inequality in Ford Theorem 1 the finite source sum is
`sum_{1 <= n <= t} n^{-s}`, not the shifted Hurwitz tail.  The half-integral
cutoff `floor(t) + 1/2` has floor exactly `floor(t)`, so Dadaro's formula
matches that source sum without an extra endpoint term.
-/

open Complex Finset Set Filter Topology
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordRiemannDadaroCutoff (t : ℝ) : ℝ :=
  (fordFiniteEndpoint t : ℝ) + 1 / 2

theorem fordRiemannDadaroCutoff_pos (t : ℝ) :
    0 < fordRiemannDadaroCutoff t := by
  unfold fordRiemannDadaroCutoff
  positivity

theorem fordRiemannDadaroCutoff_isHalfInteger (t : ℝ) :
    (fordRiemannDadaroCutoff t).IsHalfInteger := by
  refine ⟨(fordFiniteEndpoint t : ℤ), ?_⟩
  unfold fordRiemannDadaroCutoff
  push_cast
  ring

theorem fordRiemannDadaroCutoff_floor (t : ℝ) :
    ⌊fordRiemannDadaroCutoff t⌋₊ = fordFiniteEndpoint t := by
  have hcut : 0 ≤ fordRiemannDadaroCutoff t :=
    (fordRiemannDadaroCutoff_pos t).le
  rw [Nat.floor_eq_iff hcut]
  constructor
  · unfold fordRiemannDadaroCutoff
    norm_num
  · unfold fordRiemannDadaroCutoff
    have hhalf : (1 / 2 : ℝ) < 1 := by norm_num
    linarith

theorem fordRiemannDadaroCutoff_le_add_half {t : ℝ} (ht : 0 ≤ t) :
    fordRiemannDadaroCutoff t ≤ t + 1 / 2 := by
  simpa [fordRiemannDadaroCutoff, fordFiniteEndpoint] using
    add_le_add_right (Nat.floor_le ht) (1 / 2 : ℝ)

theorem t_sub_half_lt_fordRiemannDadaroCutoff (t : ℝ) :
    t - 1 / 2 < fordRiemannDadaroCutoff t := by
  unfold fordRiemannDadaroCutoff fordFiniteEndpoint
  have hfloor := Nat.lt_floor_add_one t
  norm_num at hfloor ⊢
  linarith

theorem fordRiemannDadaroCutoff_gt_height_div_two_pi
    {t : ℝ} (ht : 3 ≤ t) :
    fordRiemannDadaroCutoff t > |t| / (2 * Real.pi) := by
  have htPos : 0 < t := by linarith
  rw [abs_of_pos htPos]
  have hlower := t_sub_half_lt_fordRiemannDadaroCutoff t
  have hratio : t / (2 * Real.pi) < t - 1 / 2 := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  exact hratio.trans hlower

def fordRiemannDadaroPhase (sigma t : ℝ) : ℝ :=
  Real.pi * RiemannZeta.GuthMaynard.sharpZetaTheta
    (fordComplexHeight sigma t) (fordRiemannDadaroCutoff t)

theorem fordRiemannDadaroPhase_eq (sigma t : ℝ) :
    fordRiemannDadaroPhase sigma t =
      t / (2 * fordRiemannDadaroCutoff t) := by
  unfold fordRiemannDadaroPhase
  rw [RiemannZeta.GuthMaynard.pi_mul_sharpZetaTheta_eq _
    (fordRiemannDadaroCutoff_pos t).ne']
  simp [fordComplexHeight]

theorem fordRiemannDadaroPhase_mem_Icc
    {sigma t : ℝ} (ht : 3 ≤ t) :
    fordRiemannDadaroPhase sigma t ∈
      Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ) := by
  have htPos : 0 < t := by linarith
  have hcutPos := fordRiemannDadaroCutoff_pos t
  have hupper := fordRiemannDadaroCutoff_le_add_half htPos.le
  have hlower := t_sub_half_lt_fordRiemannDadaroCutoff t
  rw [fordRiemannDadaroPhase_eq]
  constructor
  · rw [le_div_iff₀ (mul_pos two_pos hcutPos)]
    nlinarith
  · rw [div_le_iff₀ (mul_pos two_pos hcutPos)]
    nlinarith

theorem one_fourth_le_sin_of_mem_rpow_phase {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 3 : ℝ) (2 / 3 : ℝ)) :
    1 / 4 ≤ Real.sin x := by
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hxabs : |x| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    linarith [hx.2]
  have hbound := Real.sin_bound hxabs
  have hlow := (abs_le.mp hbound).1
  rw [abs_of_nonneg hx0] at hlow
  have hx2 : x ^ 2 ≤ 4 / 9 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx.2)]
  have hx3 : x ^ 3 ≤ 4 * x / 9 := by
    nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx2)]
  have hx4 : x ^ 4 ≤ 8 * x / 27 := by
    have hmul := mul_le_mul_of_nonneg_left hx3 hx0
    nlinarith [hx.2]
  nlinarith [hx.1]

theorem riemannZeta_eq_fordPartialSum_sub_terms
    {sigma t : ℝ} (hsigma : 0 ≤ sigma) (ht : 3 ≤ t) :
    ∃ E : ℂ,
      riemannZeta (fordComplexHeight sigma t) =
          (∑ n ∈ Finset.Icc 1 (fordFiniteEndpoint t),
            (n : ℂ) ^ (-fordComplexHeight sigma t)) -
            ((fordRiemannDadaroCutoff t : ℂ) ^
              (1 - fordComplexHeight sigma t)) /
              (1 - fordComplexHeight sigma t) -
            RiemannZeta.GuthMaynard.sharpZetaBoundaryCoeff
                (fordComplexHeight sigma t) (fordRiemannDadaroCutoff t) *
              ((fordRiemannDadaroCutoff t : ℂ) ^
                (-fordComplexHeight sigma t)) + E ∧
        ‖E‖ ≤
          RiemannZeta.GuthMaynard.sharpZetaErrorCoeff
              (fordComplexHeight sigma t) (fordRiemannDadaroCutoff t) /
            fordRiemannDadaroCutoff t ^ (sigma + 1) := by
  have htPos : 0 < t := by linarith
  have hsNe : fordComplexHeight sigma t ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [fordComplexHeight] at him
    linarith
  obtain ⟨E, hEq, hE⟩ :=
    RiemannZeta.GuthMaynard.riemannZeta_sharp_halfInteger_truncation
      hsNe (by simpa [fordComplexHeight] using hsigma)
      (fordRiemannDadaroCutoff_pos t)
      (fordRiemannDadaroCutoff_isHalfInteger t)
      (by simpa [fordComplexHeight] using
        fordRiemannDadaroCutoff_gt_height_div_two_pi ht)
  refine ⟨E, ?_, ?_⟩
  · rw [fordRiemannDadaroCutoff_floor] at hEq
    simpa [fordComplexHeight] using hEq
  · simpa [fordComplexHeight] using hE

#print axioms fordRiemannDadaroCutoff_floor
#print axioms fordRiemannDadaroPhase_mem_Icc
#print axioms one_fourth_le_sin_of_mem_rpow_phase
#print axioms riemannZeta_eq_fordPartialSum_sub_terms

end

end GafniTao
