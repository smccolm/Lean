import GafniTao.Pintz2023HalaszInfiniteBounds

/-!
# Pintz (2023), equation (4.19): quantitative cardinality consumer

This file performs the diagonal/off-diagonal split of the literal infinite
Gram sum.  The final absorption hypothesis is exactly the source step saying
that each off-diagonal contribution is small compared with the squared
detected value after multiplication by the `d_n` energy.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Exact diagonal/off-diagonal decomposition of Pintz's infinite Gram
factor. -/
theorem pintz2023_infinite_gram_eq_diagonal_add_offDiagonal
    (N : ℕ) (W : Finset ℝ) (eta : ℝ)
    (etaAt gammaAt : ℝ → ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖) =
      (∑ t ∈ W,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt t) - gammaAt t : ℝ) : ℂ))‖) +
      ∑ t ∈ W, ∑ u ∈ W.erase t,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖ := by
  classical
  calc
    _ = ∑ t ∈ W,
        (‖pintz2023SmoothedZetaSum N
            (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
              I * (((gammaAt t) - gammaAt t : ℝ) : ℂ))‖ +
          ∑ u ∈ W.erase t,
            ‖pintz2023SmoothedZetaSum N
              (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
                I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_erase_add W _ ht]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib]

/-- A uniform diagonal and a uniform off-diagonal majorant bound the exact
double Gram sum with the correct linear and quadratic cardinality factors. -/
theorem pintz2023_infinite_gram_le_cardinality_majorant
    (N : ℕ) (W : Finset ℝ) (eta D O : ℝ)
    (etaAt gammaAt : ℝ → ℝ)
    (hO : 0 ≤ O)
    (hDiagonal : ∀ t ∈ W,
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt t) - gammaAt t : ℝ) : ℂ))‖ ≤ D)
    (hOffDiagonal : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖ ≤ O) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖) ≤
      (W.card : ℝ) * D + (W.card : ℝ) ^ 2 * O := by
  rw [pintz2023_infinite_gram_eq_diagonal_add_offDiagonal]
  have hDiagSum :
      (∑ t ∈ W,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt t) - gammaAt t : ℝ) : ℂ))‖) ≤
        (W.card : ℝ) * D := by
    calc
      _ ≤ ∑ _t ∈ W, D := Finset.sum_le_sum hDiagonal
      _ = (W.card : ℝ) * D := by simp
  have hOffSum :
      (∑ t ∈ W, ∑ u ∈ W.erase t,
        ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖) ≤
        (W.card : ℝ) ^ 2 * O := by
    calc
      _ ≤ ∑ t ∈ W, ∑ _u ∈ W.erase t, O := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        exact hOffDiagonal t ht u (Finset.mem_of_mem_erase hu)
          ((Finset.ne_of_mem_erase hu).symm)
      _ = ∑ t ∈ W, ((W.erase t).card : ℝ) * O := by
        apply Finset.sum_congr rfl
        intro t ht
        simp
      _ ≤ ∑ _t ∈ W, (W.card : ℝ) * O := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.card_erase_le : (W.erase t).card ≤ W.card)) hO
      _ = (W.card : ℝ) ^ 2 * O := by
        simp
        ring
  linarith

/-- Source-level quantitative consumer of Pintz (4.19).  It consumes the
literal infinite Gram theorem, the exact `d_n` energy, and a proved
off-diagonal absorption; it does not accept a cardinality theorem as an
input. -/
theorem pintz2023_halasz_cardinality_of_infinite_gram
    {N : ℕ} (Iset : Finset ℕ) (W : Finset ℝ) (b : ℕ → ℂ)
    (eta lambda A E D O : ℝ) (etaAt gammaAt : ℝ → ℝ)
    (hN : 0 < N) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hD : 0 ≤ D) (hO : 0 ≤ O)
    (hpositive : ∀ n ∈ Iset, 0 < n)
    (hReal : ∀ t ∈ W, ∀ u ∈ W,
      0 ≤ 1 - etaAt t - etaAt u - 4 * eta)
    (hLarge : ∀ t ∈ W,
      A ≤ ‖∑ n ∈ Iset,
        b n * (n : ℂ) ^
          (-(((1 - etaAt t + 1 / lambda : ℝ) : ℂ) +
            I * ((gammaAt t : ℝ) : ℂ)))‖)
    (hEnergy :
      (∑ n ∈ Iset,
        ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
          (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) ≤ E)
    (hDiagonal : ∀ t ∈ W,
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt t - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt t) - gammaAt t : ℝ) : ℂ))‖ ≤ D)
    (hOffDiagonal : ∀ t ∈ W, ∀ u ∈ W, t ≠ u →
      ‖pintz2023SmoothedZetaSum N
          (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
            I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖ ≤ O)
    (hAbsorb : E * O ≤ A ^ 2 / 2) :
    (W.card : ℝ) * A ^ 2 ≤ 2 * E * D := by
  let K : ℝ := W.card
  let G : ℝ := ∑ t ∈ W, ∑ u ∈ W,
    ‖pintz2023SmoothedZetaSum N
      (((1 - etaAt t - etaAt u - 4 * eta : ℝ) : ℂ) +
        I * (((gammaAt u) - gammaAt t : ℝ) : ℂ))‖
  have hGram := pintz2023_halasz_gram_infinite Iset W b eta lambda A
    etaAt gammaAt hN hA hpositive hReal hLarge
  have hGNonneg : 0 ≤ G := by
    dsimp only [G]
    positivity
  have hGramBound : G ≤ K * D + K ^ 2 * O := by
    simpa only [G, K] using
      pintz2023_infinite_gram_le_cardinality_majorant
        N W eta D O etaAt gammaAt hO hDiagonal hOffDiagonal
  have hCore : (K * A) ^ 2 ≤ E * (K * D + K ^ 2 * O) := by
    calc
      (K * A) ^ 2 ≤
          (∑ n ∈ Iset,
            ‖b n‖ ^ 2 * (pintz2023HalaszKernel N n)⁻¹ *
              (n : ℝ) ^ (-1 - 4 * eta - 2 / lambda)) * G := by
        simpa only [K, G] using hGram
      _ ≤ E * G := mul_le_mul_of_nonneg_right hEnergy hGNonneg
      _ ≤ E * (K * D + K ^ 2 * O) :=
        mul_le_mul_of_nonneg_left hGramBound hE
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  by_cases hKzero : K = 0
  · change K * A ^ 2 ≤ 2 * E * D
    rw [hKzero, zero_mul]
    positivity
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
  have hAbsorbK : E * (K ^ 2 * O) ≤ K ^ 2 * A ^ 2 / 2 := by
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hAbsorb)]
  have hHalf : K ^ 2 * A ^ 2 / 2 ≤ E * (K * D) := by
    nlinarith [hCore, hAbsorbK]
  nlinarith [mul_nonneg hE hD]

#print axioms pintz2023_infinite_gram_eq_diagonal_add_offDiagonal
#print axioms pintz2023_infinite_gram_le_cardinality_majorant
#print axioms pintz2023_halasz_cardinality_of_infinite_gram

end

end GafniTao
