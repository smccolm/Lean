import GafniTao.SharpPerronGeneralLogBound
import GafniTao.SharpPerronSelectedHeight

/-!
# Selected-height sharp explicit formula at an arbitrary real endpoint

The contour identity and the three non-right edges were already uniform in
the endpoint.  This module combines them with the endpoint-uniform Perron
bound and the actual good-height selector.
-/

open Complex Set MeasureTheory
open scoped BigOperators

noncomputable section

namespace GafniTao

private theorem sharpPsiTruncationError_eq_general_selected_edges
    {x R : ℝ} (hx : 1 < x) (hR : 0 < R)
    (hheight : ∀ rho ∈ zeroSet 0 R, |rho.im| < R) :
    sharpPsiTruncationError R x =
      ((Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R) +
      (-logDeriv sharpZetaSurrogate 0 - 1) -
      HIntegral' (sharpZetaPerronIntegrand x) (-1)
        (sharpPerronAbscissa x) (-R) +
      HIntegral' (sharpZetaPerronIntegrand x) (-1)
        (sharpPerronAbscissa x) R +
      VIntegral' (sharpZetaPerronIntegrand x) (-1) (-R) R := by
  have hrect := sharpZetaPerron_rightVertical_eq_explicit_sum_add_edges
    hx hR hheight
  have hright := VIntegral'_sharpZetaPerronIntegrand_right_eq
    (R := R) hx
  rw [hright] at hrect
  unfold sharpPsiTruncationError truncatedPsiZeroSum
  push_cast
  linear_combination hrect

/-- Complete selected-height contour estimate for every real endpoint in the
physical range `8 ≤ T ≤ x`. -/
theorem exists_norm_sharpPsiTruncationError_general_selected_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T x R : ℝ} (hT : 8 ≤ T),
      T ≤ x → R ∈ Set.Icc T (T + 1) →
      (∀ ρ ∈ sharpLandauZeroFinset T hT,
        1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
          |R - (sharpLandauMap T ρ).im|) →
      (∀ rho ∈ zeroSet 0 R, |rho.im| < R) →
      ‖sharpPsiTruncationError R x‖ ≤
        C * x * Real.log x ^ 2 / T := by
  obtain ⟨D, hD, hright⟩ :=
    exists_norm_optimized_general_Perron_sub_psi_le
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
  intro T x R hT hTx hR hfar hheight
  let S : ℝ := x * Real.log x ^ 2 / T
  have hTpos : 0 < T := by linarith
  have hxpos : 0 < x := by linarith [hT, hTx]
  have hxTwo : 2 ≤ x := by linarith [hT, hTx]
  have hRpos : 0 < R := by linarith [hR.1]
  have hlogNonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogOne : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hxpos).2
    exact Real.exp_one_lt_three.le.trans
      ((by norm_num : (3 : ℝ) ≤ 8).trans (hT.trans hTx))
  have hSone : 1 ≤ S := by
    dsimp [S]
    rw [le_div_iff₀ hTpos]
    nlinarith [sq_nonneg (Real.log x - 1)]
  have hrightRaw := hright (T := R) (x := x)
    (by linarith [hT, hTx]) (by linarith [hR.1]) (by linarith [hR.2, hTx])
  have hrightT :
      ‖(Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R‖ ≤
        D * S := by
    have hsymm :
        ‖(Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R‖ =
          ‖sharpZetaPerronRightIntegral x R - (Chebyshev.psi x : ℂ)‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hsymm]
    refine hrightRaw.trans ?_
    calc
      D * x * Real.log x ^ 2 / R ≤
          (D * x * Real.log x ^ 2) / T := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hTpos
        · exact hR.1
      _ = D * S := by dsimp [S]; ring
  have hconst : ‖-logDeriv sharpZetaSurrogate 0 - 1‖ ≤ K * S := by
    have hnormK : ‖-logDeriv sharpZetaSurrogate 0 - 1‖ ≤ K := by
      dsimp [K]
      linarith
    exact hnormK.trans (by nlinarith [hK.le, hSone])
  have htop' := htop hT hxTwo hTx hR hfar
  have hbot' := hbot hT hxTwo hTx hR hfar
  have hleft' := hleft hT hxTwo hTx hR
  have htopS :
      ‖HIntegral' (sharpZetaPerronIntegrand x) (-1)
        (sharpPerronAbscissa x) R‖ ≤ Ctop * S := by
    refine htop'.trans_eq ?_
    dsimp [S]
    ring
  have hbotS :
      ‖HIntegral' (sharpZetaPerronIntegrand x) (-1)
        (sharpPerronAbscissa x) (-R)‖ ≤ Cbot * S := by
    refine hbot'.trans_eq ?_
    dsimp [S]
    ring
  have hleftS :
      ‖VIntegral' (sharpZetaPerronIntegrand x) (-1) (-R) R‖ ≤
        Cleft * S := by
    refine hleft'.trans_eq ?_
    dsimp [S]
    ring
  have heq := sharpPsiTruncationError_eq_general_selected_edges
    (x := x) (R := R) (by linarith [hT, hTx]) hRpos hheight
  rw [heq]
  have htri :
      ‖((Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R) +
          (-logDeriv sharpZetaSurrogate 0 - 1) -
          HIntegral' (sharpZetaPerronIntegrand x) (-1)
            (sharpPerronAbscissa x) (-R) +
          HIntegral' (sharpZetaPerronIntegrand x) (-1)
            (sharpPerronAbscissa x) R +
          VIntegral' (sharpZetaPerronIntegrand x) (-1) (-R) R‖ ≤
        ‖(Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R‖ +
          ‖-logDeriv sharpZetaSurrogate 0 - 1‖ +
          ‖HIntegral' (sharpZetaPerronIntegrand x) (-1)
            (sharpPerronAbscissa x) (-R)‖ +
          ‖HIntegral' (sharpZetaPerronIntegrand x) (-1)
            (sharpPerronAbscissa x) R‖ +
          ‖VIntegral' (sharpZetaPerronIntegrand x) (-1) (-R) R‖ := by
    let a : ℂ := (Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R
    let b : ℂ := -logDeriv sharpZetaSurrogate 0 - 1
    let c : ℂ := HIntegral' (sharpZetaPerronIntegrand x) (-1)
      (sharpPerronAbscissa x) (-R)
    let d : ℂ := HIntegral' (sharpZetaPerronIntegrand x) (-1)
      (sharpPerronAbscissa x) R
    let e : ℂ := VIntegral' (sharpZetaPerronIntegrand x) (-1) (-R) R
    change ‖a + b - c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖
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
    _ ≤ ‖(Chebyshev.psi x : ℂ) - sharpZetaPerronRightIntegral x R‖ +
        ‖-logDeriv sharpZetaSurrogate 0 - 1‖ +
        ‖HIntegral' (sharpZetaPerronIntegrand x) (-1)
          (sharpPerronAbscissa x) (-R)‖ +
        ‖HIntegral' (sharpZetaPerronIntegrand x) (-1)
          (sharpPerronAbscissa x) R‖ +
        ‖VIntegral' (sharpZetaPerronIntegrand x) (-1) (-R) R‖ := htri
    _ ≤ D * S + K * S + Cbot * S + Ctop * S + Cleft * S := by
      exact add_le_add
        (add_le_add (add_le_add (add_le_add hrightT hconst) hbotS) htopS)
        hleftS
    _ = C * S := by dsimp [C]; ring
    _ = C * x * Real.log x ^ 2 / T := by dsimp [S]; ring

/-- Existence form using the actual good-height selector. -/
theorem exists_good_height_norm_sharpPsiTruncationError_general_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {T x : ℝ}, 8 ≤ T → T ≤ x →
      ∃ R ∈ Set.Icc T (T + 1),
        ‖sharpPsiTruncationError R x‖ ≤
          C * x * Real.log x ^ 2 / T := by
  obtain ⟨C, hC, hselected⟩ :=
    exists_norm_sharpPsiTruncationError_general_selected_le
  refine ⟨C, hC, ?_⟩
  intro T x hT hTx
  obtain ⟨R, hR, hfar, hheight⟩ :=
    exists_sharpPerron_residue_good_height hT
  exact ⟨R, hR, hselected hT hTx hR hfar hheight⟩

end GafniTao
