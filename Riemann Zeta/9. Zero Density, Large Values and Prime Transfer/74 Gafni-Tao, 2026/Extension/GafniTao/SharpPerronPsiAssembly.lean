import GafniTao.SharpPerronSelectedHeight

/-!
# Assembly of the selected-height sharp psi formula

This module combines the arithmetic right-edge approximation with the
residue rectangle and all three remaining contour-edge estimates.  The zero
sum is the actual multiplicity-weighted `zeroSet` sum.
-/

open Complex Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace GafniTao

private theorem sharpPsiTruncationError_eq_selected_edges
    {x R : ℝ} (hy : 1 < sharpPerronHalfPoint x) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    sharpPsiTruncationError R (sharpPerronHalfPoint x) =
      ((Chebyshev.psi (sharpPerronHalfPoint x) : ℂ) -
        sharpZetaPerronRightIntegral (sharpPerronHalfPoint x) R) +
      (-logDeriv sharpZetaSurrogate 0 - 1) -
      HIntegral' (sharpZetaPerronIntegrand (sharpPerronHalfPoint x)) (-1)
        (sharpPerronAbscissa (sharpPerronHalfPoint x)) (-R) +
      HIntegral' (sharpZetaPerronIntegrand (sharpPerronHalfPoint x)) (-1)
        (sharpPerronAbscissa (sharpPerronHalfPoint x)) R +
      VIntegral' (sharpZetaPerronIntegrand (sharpPerronHalfPoint x))
        (-1) (-R) R := by
  have hrect := sharpZetaPerron_rightVertical_eq_explicit_sum_add_edges
    hy hR hheight
  have hright := VIntegral'_sharpZetaPerronIntegrand_right_eq
    (R := R) hy
  rw [hright] at hrect
  unfold sharpPsiTruncationError truncatedPsiZeroSum
  push_cast
  linear_combination hrect

/-- At a selected good height `R∈[T,T+1]`, the complete sharp-psi remainder
is `O(y log²y/T)` at the half-integral point `y`. -/
theorem exists_norm_sharpPsiTruncationError_selected_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T x R : ℝ} (hT : 8 ≤ T),
      2 ≤ sharpPerronHalfPoint x → T ≤ sharpPerronHalfPoint x →
      R ∈ Set.Icc T (T + 1) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      (∀ rho ∈ zeroSet 0 R, |rho.im| < R) →
      ‖sharpPsiTruncationError R (sharpPerronHalfPoint x)‖ ≤
        C * sharpPerronHalfPoint x *
          Real.log (sharpPerronHalfPoint x) ^ 2 / T := by
  obtain ⟨D, hD, hright⟩ :=
    exists_norm_optimized_halfPoint_Perron_sub_psi_le
  obtain ⟨Ctop, hCtop, htop⟩ :=
    exists_norm_sharpZetaPerron_HIntegral_top_le
  obtain ⟨Cbot, hCbot, hbot⟩ :=
    exists_norm_sharpZetaPerron_HIntegral_bottom_le
  obtain ⟨Cleft, hCleft, hleft⟩ :=
    exists_norm_sharpZetaPerron_VIntegral_left_le
  let K : ℝ := ‖-logDeriv sharpZetaSurrogate 0 - 1‖ + 1
  let C : ℝ := D + K + Ctop + Cbot + Cleft
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro T x R hT hy hTy hR hfar hheight
  let y : ℝ := sharpPerronHalfPoint x
  let S : ℝ := y * Real.log y ^ 2 / T
  have hTpos : 0 < T := by linarith
  have hypos : 0 < y := by dsimp [y]; linarith
  have hRpos : 0 < R := by linarith [hR.1]
  have hlogNonneg : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hlogOne : 1 ≤ Real.log y := by
    apply (Real.le_log_iff_exp_le hypos).2
    exact Real.exp_one_lt_three.le.trans
      ((by norm_num : (3 : ℝ) ≤ 8).trans (hT.trans hTy))
  have hSone : 1 ≤ S := by
    dsimp [S]
    rw [le_div_iff₀ hTpos]
    nlinarith [sq_nonneg (Real.log y - 1)]
  have hrightRaw := hright (T := R) (x := x) hy hRpos
  have hrightT :
      ‖(Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R‖ ≤
        D * S := by
    have hsymm :
        ‖(Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R‖ =
          ‖sharpZetaPerronRightIntegral y R - (Chebyshev.psi y : ℂ)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hsymm]
    refine hrightRaw.trans ?_
    calc
      D * sharpPerronHalfPoint x *
            Real.log (sharpPerronHalfPoint x) ^ 2 / R ≤
          (D * sharpPerronHalfPoint x *
            Real.log (sharpPerronHalfPoint x) ^ 2) / T := by
              apply div_le_div_of_nonneg_left
              · positivity
              · exact hTpos
              · exact hR.1
      _ = D * S := by dsimp [S, y]; ring
  have hconst : ‖-logDeriv sharpZetaSurrogate 0 - 1‖ ≤ K * S := by
    have hnormK : ‖-logDeriv sharpZetaSurrogate 0 - 1‖ ≤ K := by
      dsimp [K]
      linarith
    exact hnormK.trans (by nlinarith [hK.le, hSone])
  have htop' := htop hT hy hTy hR hfar
  have hbot' := hbot hT hy hTy hR hfar
  have hleft' := hleft hT hy hTy hR
  have htopS :
      ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
        (sharpPerronAbscissa y) R‖ ≤ Ctop * S := by
    refine htop'.trans_eq ?_
    dsimp [y, S]
    ring
  have hbotS :
      ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
        (sharpPerronAbscissa y) (-R)‖ ≤ Cbot * S := by
    refine hbot'.trans_eq ?_
    dsimp [y, S]
    ring
  have hleftS :
      ‖VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ ≤
        Cleft * S := by
    refine hleft'.trans_eq ?_
    dsimp [y, S]
    ring
  have heq := sharpPsiTruncationError_eq_selected_edges
    (x := x) (R := R) (by linarith [hy]) hRpos hheight
  rw [heq]
  have htri :
      ‖((Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R) +
          (-logDeriv sharpZetaSurrogate 0 - 1) -
          HIntegral' (sharpZetaPerronIntegrand y) (-1)
            (sharpPerronAbscissa y) (-R) +
          HIntegral' (sharpZetaPerronIntegrand y) (-1)
            (sharpPerronAbscissa y) R +
          VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ ≤
        ‖(Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R‖ +
          ‖-logDeriv sharpZetaSurrogate 0 - 1‖ +
          ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
            (sharpPerronAbscissa y) (-R)‖ +
          ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
            (sharpPerronAbscissa y) R‖ +
          ‖VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ := by
    let a : ℂ := (Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R
    let b : ℂ := -logDeriv sharpZetaSurrogate 0 - 1
    let c : ℂ := HIntegral' (sharpZetaPerronIntegrand y) (-1)
      (sharpPerronAbscissa y) (-R)
    let d : ℂ := HIntegral' (sharpZetaPerronIntegrand y) (-1)
      (sharpPerronAbscissa y) R
    let e : ℂ := VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R
    change ‖a + b - c + d + e‖ ≤
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖
    calc
      ‖a + b - c + d + e‖ ≤ ‖a + b - c + d‖ + ‖e‖ := norm_add_le _ _
      _ ≤ (‖a + b - c‖ + ‖d‖) + ‖e‖ := by
        exact add_le_add (norm_add_le _ _) le_rfl
      _ ≤ ((‖a + b‖ + ‖c‖) + ‖d‖) + ‖e‖ := by
        exact add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
      _ ≤ (((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖) + ‖e‖ := by
        exact add_le_add
          (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) le_rfl
  calc
    ‖((Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R) +
        (-logDeriv sharpZetaSurrogate 0 - 1) -
        HIntegral' (sharpZetaPerronIntegrand y) (-1)
          (sharpPerronAbscissa y) (-R) +
        HIntegral' (sharpZetaPerronIntegrand y) (-1)
          (sharpPerronAbscissa y) R +
        VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ ≤
      ‖(Chebyshev.psi y : ℂ) - sharpZetaPerronRightIntegral y R‖ +
        ‖-logDeriv sharpZetaSurrogate 0 - 1‖ +
        ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
          (sharpPerronAbscissa y) (-R)‖ +
        ‖HIntegral' (sharpZetaPerronIntegrand y) (-1)
          (sharpPerronAbscissa y) R‖ +
        ‖VIntegral' (sharpZetaPerronIntegrand y) (-1) (-R) R‖ := by
          exact htri
    _ ≤ D * S + K * S + Cbot * S + Ctop * S + Cleft * S := by
          exact add_le_add
            (add_le_add
              (add_le_add (add_le_add hrightT hconst) hbotS) htopS)
            hleftS
    _ = C * S := by dsimp [C]; ring
    _ = C * sharpPerronHalfPoint x *
          Real.log (sharpPerronHalfPoint x) ^ 2 / T := by
          dsimp [S, y]
          ring

/-- Existence form using the actual good-height selector. -/
theorem exists_good_height_norm_sharpPsiTruncationError_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T x : ℝ}, 8 ≤ T →
      2 ≤ sharpPerronHalfPoint x → T ≤ sharpPerronHalfPoint x →
      ∃ R ∈ Set.Icc T (T + 1),
        ‖sharpPsiTruncationError R (sharpPerronHalfPoint x)‖ ≤
          C * sharpPerronHalfPoint x *
            Real.log (sharpPerronHalfPoint x) ^ 2 / T := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_norm_sharpPsiTruncationError_selected_le
  refine ⟨C, hC, ?_⟩
  intro T x hT hy hTy
  obtain ⟨R, hR, hfar, hheight⟩ :=
    exists_sharpPerron_residue_good_height hT
  exact ⟨R, hR, hselected hT hy hTy hR hfar hheight⟩

end GafniTao
