import GafniTao.Pintz2023PoweredCoefficient
import RiemannZeta.GuthMaynard.ClassicalLargeValues
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Pintz (2023), equations (4.19)--(4.24): finite MHH entry

This module applies the frozen finite Montgomery--Halasz--Huxley theorem to
the actual coefficient obtained by powering Pintz's selected, zero-padded
source block.  Both dyadic selections and their cardinality losses remain
visible.  The theorem here is finite: the source parameter choices and final
exponent optimization are subsequent obligations.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- Constant-normalized exact powered coefficient. -/
noncomputable def pintz2023NormalizedSelectedPoweredCoeff
    (X Y U h : ℕ) (beta C : ℝ) (m : ℕ) : ℂ :=
  pintz2023SelectedPoweredLineCoeff X Y U h beta m / (C : ℂ)

/-- Scale-sensitive normalization on a chosen ordinary dyadic block.  This
is the normalization used for Pintz's exponent: the factor `Q^beta` retains
the saving from the real part, while `(2Q)^epsilon` absorbs the exact divisor
and factorization loss. -/
noncomputable def pintz2023ScaledNormalizedPoweredCoeff
    (X Y U h Q : ℕ) (beta C epsilon : ℝ) (m : ℕ) : ℂ :=
  (((Q : ℝ) ^ beta : ℝ) : ℂ) *
      pintz2023SelectedPoweredLineCoeff X Y U h beta m /
    ((C * ((2 * Q : ℕ) : ℝ) ^ epsilon : ℝ) : ℂ)

/-- Normalizing the coefficient divides the whole finite polynomial by the
same positive real constant. -/
theorem dirichletPoly_pintz2023NormalizedSelectedPoweredCoeff
    (X Y U h N : ℕ) (beta C t : ℝ) :
    dirichletPoly N
        (pintz2023NormalizedSelectedPoweredCoeff X Y U h beta C) t =
      dirichletPoly N
        (pintz2023SelectedPoweredLineCoeff X Y U h beta) t / (C : ℂ) := by
  unfold dirichletPoly pintz2023NormalizedSelectedPoweredCoeff
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  rw [div_mul_eq_mul_div]

/-- Exact polynomial identity for the scale-sensitive normalization. -/
theorem dirichletPoly_pintz2023ScaledNormalizedPoweredCoeff
    (X Y U h Q : ℕ) (beta C epsilon t : ℝ) :
    dirichletPoly Q
        (pintz2023ScaledNormalizedPoweredCoeff
          X Y U h Q beta C epsilon) t =
      (((Q : ℝ) ^ beta : ℝ) : ℂ) *
          dirichletPoly Q
            (pintz2023SelectedPoweredLineCoeff X Y U h beta) t /
        ((C * ((2 * Q : ℕ) : ℝ) ^ epsilon : ℝ) : ℂ) := by
  unfold dirichletPoly pintz2023ScaledNormalizedPoweredCoeff
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The scale-sensitive coefficients are literally bounded by one on the
chosen ordinary dyadic block. -/
theorem norm_pintz2023ScaledNormalizedPoweredCoeff_le_one
    {X Y U h Q m : ℕ} {beta C epsilon : ℝ}
    (hQ : 0 < Q) (hBeta : 0 ≤ beta) (hC : 0 < C)
    (hEpsilon : 0 < epsilon) (hm : m ∈ dyadicInterval Q)
    (hCoeff :
      ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m‖ ≤
        C * (m : ℝ) ^ (epsilon - beta)) :
    ‖pintz2023ScaledNormalizedPoweredCoeff
      X Y U h Q beta C epsilon m‖ ≤ 1 := by
  have hmBounds : Q < m ∧ m ≤ 2 * Q := by
    simpa only [dyadicInterval] using Finset.mem_Ioc.mp hm
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmReal : (0 : ℝ) < m := by exact_mod_cast (lt_trans hQ hmBounds.1)
  have hTwoQReal : (0 : ℝ) < (2 * Q : ℕ) := by
    exact_mod_cast (mul_pos (by omega : 0 < 2) hQ)
  have hQm : (Q : ℝ) ≤ m := by exact_mod_cast hmBounds.1.le
  have hmTwoQ : (m : ℝ) ≤ (2 * Q : ℕ) := by
    exact_mod_cast hmBounds.2
  have hQBeta : (Q : ℝ) ^ beta ≤ (m : ℝ) ^ beta :=
    Real.rpow_le_rpow hQReal.le hQm hBeta
  have hMerge : (m : ℝ) ^ beta * (m : ℝ) ^ (epsilon - beta) =
      (m : ℝ) ^ epsilon := by
    rw [← Real.rpow_add hmReal]
    congr 1
    ring
  have hScale : (Q : ℝ) ^ beta * (m : ℝ) ^ (epsilon - beta) ≤
      ((2 * Q : ℕ) : ℝ) ^ epsilon := by
    calc
      (Q : ℝ) ^ beta * (m : ℝ) ^ (epsilon - beta) ≤
          (m : ℝ) ^ beta * (m : ℝ) ^ (epsilon - beta) := by
        gcongr
      _ = (m : ℝ) ^ epsilon := hMerge
      _ ≤ ((2 * Q : ℕ) : ℝ) ^ epsilon :=
        Real.rpow_le_rpow hmReal.le hmTwoQ hEpsilon.le
  have hDenom : 0 < C * ((2 * Q : ℕ) : ℝ) ^ epsilon := by
    exact mul_pos hC (Real.rpow_pos_of_pos hTwoQReal _)
  unfold pintz2023ScaledNormalizedPoweredCoeff
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hQReal _), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hDenom, div_le_one hDenom]
  calc
    (Q : ℝ) ^ beta *
        ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m‖ ≤
      (Q : ℝ) ^ beta *
        (C * (m : ℝ) ^ (epsilon - beta)) := by gcongr
    _ = C * ((Q : ℝ) ^ beta *
        (m : ℝ) ^ (epsilon - beta)) := by ring
    _ ≤ C * ((2 * Q : ℕ) : ℝ) ^ epsilon := by gcongr

/-- Exact finite large-values consequence for the powered Pintz block.
The returned `r` is the post-powering dyadic block, and `W'` is the common
subfamily on which that one block is large. -/
theorem exists_pintz2023_powered_mhh_bound
    {X Y U h : ℕ} {beta V T epsilonCoeff epsilonMHH : ℝ}
    {W : Finset ℝ}
    (hU : 0 < U) (hh : 0 < h) (hV : 0 < V)
    (hT : 1 ≤ T) (hEpsilonCoeff : 0 < epsilonCoeff)
    (hEpsilonCoeffBeta : epsilonCoeff ≤ beta)
    (hEpsilonMHH : 0 < epsilonMHH)
    (hScale : ∀ r ∈ Finset.range h,
      ((2 ^ r * U ^ h : ℕ) : ℝ) ≤ T)
    (hSeparated : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly U
        (pintz2023LocalizedLineCoeff X Y beta) t‖) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∃ r ∈ Finset.range h, ∃ W' ⊆ W,
        (W.card : ℝ) ≤ h * (W'.card : ℝ) ∧
        (W'.card : ℝ) ≤
          K * T ^ epsilonMHH *
            (((2 ^ r * U ^ h : ℕ) : ℝ) ^ 2 /
                ((V ^ h / h) / B) ^ 2 +
              T * min
                (((2 ^ r * U ^ h : ℕ) : ℝ) /
                  ((V ^ h / h) / B) ^ 2)
                (((2 ^ r * U ^ h : ℕ) : ℝ) ^ 4 /
                  ((V ^ h / h) / B) ^ 6)) := by
  obtain ⟨B, hB, hCoeff⟩ :=
    norm_pintz2023SelectedPoweredLineCoeff_le
      h epsilonCoeff hEpsilonCoeff
  obtain ⟨K, hK, hMHH⟩ :=
    classical_montgomery_halasz_huxley_native epsilonMHH hEpsilonMHH
  obtain ⟨r, hr, W', hW', hCard, hLarge'⟩ :=
    exists_pintz2023_powered_dyadic_block_and_subset
      hU hh hV.le hLarge
  let N : ℕ := 2 ^ r * U ^ h
  let L : ℝ := (V ^ h / h) / B
  have hN : 0 < N := by
    dsimp only [N]
    exact mul_pos (pow_pos (by omega) r) (pow_pos hU h)
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hUnit : ∀ m ∈ dyadicInterval N,
      ‖pintz2023NormalizedSelectedPoweredCoeff X Y U h beta B m‖ ≤ 1 := by
    intro m hm
    apply norm_pintz2023_normalized_powered_coeff_le_one hB
    apply hCoeff X Y U m beta hU
    · rw [dyadicInterval, Finset.mem_Ioc] at hm
      omega
    · exact hEpsilonCoeffBeta
  have hSep' : IsSeparated 1 W' := by
    intro s hs t ht hst
    exact hSeparated s (hW' hs) t (hW' ht) hst
  have hBase' : InBaseInterval T W' := by
    intro t ht
    exact hBase t (hW' ht)
  have hLargeNorm : ∀ t ∈ W', L ≤
      ‖dirichletPoly N
        (pintz2023NormalizedSelectedPoweredCoeff X Y U h beta B) t‖ := by
    intro t ht
    rw [dirichletPoly_pintz2023NormalizedSelectedPoweredCoeff,
      norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB]
    exact div_le_div_of_nonneg_right (hLarge' t ht) hB.le
  have hBound := hMHH N T L W'
    (pintz2023NormalizedSelectedPoweredCoeff X Y U h beta B)
    hN hT (hScale r hr) hL hUnit hSep' hBase' hLargeNorm
  refine ⟨B, hB, K, hK, r, hr, W', hW', hCard, ?_⟩
  simpa only [N, L] using hBound

/-- Scale-sensitive finite MHH bound.  Unlike the coarse constant-only
normalization above, this is the source exponent form used in Pintz
(4.19)--(4.24): the large-value threshold contains `Q^beta`, and only the
explicit coefficient loss `(2Q)^epsilonCoeff` is paid. -/
theorem exists_pintz2023_powered_scaled_mhh_bound
    {X Y U h : ℕ} {beta V T epsilonCoeff epsilonMHH : ℝ}
    {W : Finset ℝ}
    (hU : 0 < U) (hh : 0 < h) (hV : 0 < V)
    (hBeta : 0 ≤ beta) (hT : 1 ≤ T)
    (hEpsilonCoeff : 0 < epsilonCoeff)
    (hEpsilonMHH : 0 < epsilonMHH)
    (hScale : ∀ r ∈ Finset.range h,
      ((2 ^ r * U ^ h : ℕ) : ℝ) ≤ T)
    (hSeparated : IsSeparated 1 W) (hBase : InBaseInterval T W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly U
        (pintz2023LocalizedLineCoeff X Y beta) t‖) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∃ r ∈ Finset.range h, ∃ W' ⊆ W,
        let Q : ℕ := 2 ^ r * U ^ h
        let L : ℝ :=
          (Q : ℝ) ^ beta * (V ^ h / h) /
            (B * ((2 * Q : ℕ) : ℝ) ^ epsilonCoeff)
        (W.card : ℝ) ≤ h * (W'.card : ℝ) ∧
        (W'.card : ℝ) ≤
          K * T ^ epsilonMHH *
            ((Q : ℝ) ^ 2 / L ^ 2 +
              T * min ((Q : ℝ) / L ^ 2)
                ((Q : ℝ) ^ 4 / L ^ 6)) := by
  obtain ⟨B, hB, hCoeff⟩ :=
    norm_pintz2023SelectedPoweredLineCoeff_le_rpow
      h epsilonCoeff hEpsilonCoeff
  obtain ⟨K, hK, hMHH⟩ :=
    classical_montgomery_halasz_huxley_native epsilonMHH hEpsilonMHH
  obtain ⟨r, hr, W', hW', hCard, hLarge'⟩ :=
    exists_pintz2023_powered_dyadic_block_and_subset
      hU hh hV.le hLarge
  let Q : ℕ := 2 ^ r * U ^ h
  let L : ℝ :=
    (Q : ℝ) ^ beta * (V ^ h / h) /
      (B * ((2 * Q : ℕ) : ℝ) ^ epsilonCoeff)
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact mul_pos (pow_pos (by omega) r) (pow_pos hU h)
  have hQReal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hTwoQReal : (0 : ℝ) < (2 * Q : ℕ) := by
    exact_mod_cast (mul_pos (by omega : 0 < 2) hQ)
  have hDenom : 0 < B * ((2 * Q : ℕ) : ℝ) ^ epsilonCoeff := by
    exact mul_pos hB (Real.rpow_pos_of_pos hTwoQReal _)
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hUnit : ∀ m ∈ dyadicInterval Q,
      ‖pintz2023ScaledNormalizedPoweredCoeff
        X Y U h Q beta B epsilonCoeff m‖ ≤ 1 := by
    intro m hm
    apply norm_pintz2023ScaledNormalizedPoweredCoeff_le_one
      hQ hBeta hB hEpsilonCoeff hm
    apply hCoeff X Y U m beta hU
    rw [dyadicInterval, Finset.mem_Ioc] at hm
    omega
  have hSep' : IsSeparated 1 W' := by
    intro s hs t ht hst
    exact hSeparated s (hW' hs) t (hW' ht) hst
  have hBase' : InBaseInterval T W' := by
    intro t ht
    exact hBase t (hW' ht)
  have hLargeNorm : ∀ t ∈ W', L ≤
      ‖dirichletPoly Q
        (pintz2023ScaledNormalizedPoweredCoeff
          X Y U h Q beta B epsilonCoeff) t‖ := by
    intro t ht
    rw [dirichletPoly_pintz2023ScaledNormalizedPoweredCoeff,
      norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hQReal _), Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hDenom]
    dsimp only [L]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hLarge' t ht)
        (Real.rpow_nonneg hQReal.le beta)) hDenom.le
  have hBound := hMHH Q T L W'
    (pintz2023ScaledNormalizedPoweredCoeff
      X Y U h Q beta B epsilonCoeff)
    hQ hT (hScale r hr) hL hUnit hSep' hBase' hLargeNorm
  exact ⟨B, hB, K, hK, r, hr, W', hW', hCard, hBound⟩

#print axioms dirichletPoly_pintz2023NormalizedSelectedPoweredCoeff
#print axioms dirichletPoly_pintz2023ScaledNormalizedPoweredCoeff
#print axioms norm_pintz2023ScaledNormalizedPoweredCoeff_le_one
#print axioms exists_pintz2023_powered_mhh_bound
#print axioms exists_pintz2023_powered_scaled_mhh_bound

end

end GafniTao
