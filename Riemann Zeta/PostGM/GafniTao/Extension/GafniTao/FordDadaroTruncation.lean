import GafniTao.FordHurwitzTruncation
import RiemannZeta.External.PNT.ZetaAppendix
import RiemannZeta.GuthMaynard.ZetaTruncation

/-!
# A native Riemann-zeta truncation at Ford's height

For the Riemann-zeta output actually consumed by Gafni--Tao, Dadaro's
kernel-checked sharp partial-sum formula supplies Ford's `10^-80` remainder
without introducing a Hurwitz-zeta postulate.  The half-integral cutoff is
chosen so its finite sum is exactly `1 + fordFiniteHurwitzSum ... u=1`.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordDadaroCutoff (t : ℝ) : ℝ :=
  (fordFiniteEndpoint t : ℝ) + 3 / 2

theorem fordDadaroCutoff_pos (t : ℝ) :
    0 < fordDadaroCutoff t := by
  unfold fordDadaroCutoff
  positivity

theorem fordDadaroCutoff_isHalfInteger (t : ℝ) :
    (fordDadaroCutoff t).IsHalfInteger := by
  refine ⟨(fordFiniteEndpoint t : ℤ) + 1, ?_⟩
  unfold fordDadaroCutoff
  push_cast
  ring

theorem fordDadaroCutoff_le_add {t : ℝ} (ht : 0 ≤ t) :
    fordDadaroCutoff t ≤ t + 3 / 2 := by
  simpa [fordDadaroCutoff, fordFiniteEndpoint] using
    add_le_add_right (Nat.floor_le ht) (3 / 2 : ℝ)

theorem lt_fordDadaroCutoff (t : ℝ) :
    t < fordDadaroCutoff t := by
  unfold fordDadaroCutoff fordFiniteEndpoint
  have hfloor := Nat.lt_floor_add_one t
  norm_num at hfloor ⊢
  linarith

theorem fordDadaroCutoff_gt_height_div_two_pi
    {t : ℝ} (ht : 3 ≤ t) :
    fordDadaroCutoff t > |t| / (2 * Real.pi) := by
  have htPos : 0 < t := by linarith
  rw [abs_of_pos htPos]
  have hcut : t < fordDadaroCutoff t := lt_fordDadaroCutoff t
  have hratio : t / (2 * Real.pi) < t := by
    rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith [Real.pi_gt_three]
  exact hratio.trans hcut

theorem fordDadaroCutoff_floor (t : ℝ) :
    ⌊fordDadaroCutoff t⌋₊ = fordFiniteEndpoint t + 1 := by
  have hcut : 0 ≤ fordDadaroCutoff t := by
    unfold fordDadaroCutoff
    positivity
  rw [Nat.floor_eq_iff hcut]
  constructor
  · unfold fordDadaroCutoff
    push_cast
    have hthreeHalves : (3 / 2 : ℝ) < 2 := by norm_num
    linarith
  · unfold fordDadaroCutoff
    push_cast
    have hthreeHalves : (3 / 2 : ℝ) < 2 := by norm_num
    linarith

theorem ford_head_one_add_finite_eq_partial_sum
    (sigma t : ℝ) (M : ℕ) :
    fordHurwitzHead sigma 1 t + fordFiniteHurwitzSum sigma M 1 t =
      ∑ n ∈ Finset.Icc 1 (M + 1),
        (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  induction M with
  | zero =>
      simp [fordHurwitzHead, fordFiniteHurwitzSum, fordComplexHeight]
  | succ M ih =>
      rw [fordFiniteHurwitzSum,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 2)]
      rw [← ih]
      unfold fordFiniteHurwitzSum fordComplexHeight
      push_cast
      ring

theorem fordHurwitzFiniteApproximation_one_eq_partial_sum
    (sigma t : ℝ) :
    fordHurwitzFiniteApproximation sigma 1 t =
      ∑ n ∈ Finset.Icc 1 ⌊fordDadaroCutoff t⌋₊,
        (n : ℂ) ^ (-fordComplexHeight sigma t) := by
  rw [fordDadaroCutoff_floor]
  exact ford_head_one_add_finite_eq_partial_sum sigma t (fordFiniteEndpoint t)

/-- The pinned PNT+ Dadaro formula at Ford's exact finite endpoint.  This is
an equality with all three non-finite terms exposed; no asymptotic remainder
has yet been discarded. -/
theorem riemannZeta_eq_fordFiniteApproximation_sub_terms
    {sigma t : ℝ} (hsigma : 0 ≤ sigma) (ht : 3 ≤ t) :
    ∃ E : ℂ,
      riemannZeta (fordComplexHeight sigma t) =
          fordHurwitzFiniteApproximation sigma 1 t -
            ((fordDadaroCutoff t : ℂ) ^
              (1 - fordComplexHeight sigma t)) /
              (1 - fordComplexHeight sigma t) -
            RiemannZeta.GuthMaynard.sharpZetaBoundaryCoeff
                (fordComplexHeight sigma t) (fordDadaroCutoff t) *
              ((fordDadaroCutoff t : ℂ) ^
                (-fordComplexHeight sigma t)) + E ∧
        ‖E‖ ≤
          RiemannZeta.GuthMaynard.sharpZetaErrorCoeff
              (fordComplexHeight sigma t) (fordDadaroCutoff t) /
            fordDadaroCutoff t ^ (sigma + 1) := by
  have htPos : 0 < t := by linarith
  have hsNe : fordComplexHeight sigma t ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [fordComplexHeight] at him
    linarith
  obtain ⟨E, hEq, hE⟩ :=
    RiemannZeta.GuthMaynard.riemannZeta_sharp_halfInteger_truncation
      hsNe (by simpa [fordComplexHeight] using hsigma)
      (fordDadaroCutoff_pos t) (fordDadaroCutoff_isHalfInteger t)
      (by simpa [fordComplexHeight] using
        fordDadaroCutoff_gt_height_div_two_pi ht)
  refine ⟨E, ?_, ?_⟩
  · rw [fordHurwitzFiniteApproximation_one_eq_partial_sum]
    simpa [fordComplexHeight] using hEq
  · simpa [fordComplexHeight] using hE

#print axioms fordDadaroCutoff_floor
#print axioms fordHurwitzFiniteApproximation_one_eq_partial_sum
#print axioms riemannZeta_eq_fordFiniteApproximation_sub_terms

end

end GafniTao
