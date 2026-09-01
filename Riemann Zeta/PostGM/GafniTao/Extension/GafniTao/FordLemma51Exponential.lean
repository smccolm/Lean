import GafniTao.FordEquation52

/-!
# Ford's exponential-sum Lemma 5.1: moment assembly

This file combines equations (5.2), (5.3), and the proved `W_h...W_g`
estimate.  The first public bound deliberately retains the unnormalized
moment majorant; a subsequent algebraic theorem rewrites it into Ford's
displayed negative-exponent form.
-/

open Complex Finset
open scoped BigOperators NNReal

namespace GafniTao

noncomputable section

/-- The real moment majorant obtained by substituting the final estimate for
`T` into equation (5.3). -/
def fordLemma51MomentMajorant
    (k h g r s M M₂ N : ℕ) (B : Finset ℕ) (t : ℝ) : ℝ :=
  (B.card : ℝ) ^ (2 * r * s - 2 * s) *
    (M : ℝ) ^ (2 * r * s - 2 * r) *
    (fordVinogradovMomentNat r k M : ℝ) *
    ((5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
      (fordLemma51WindowMoment k h g s B : ℝ) *
      ∏ j : FordLemma51DegreeWindow k h g,
        fordLemma51W s M₂ r M N t j.1)

/-- Equation (5.3) after inserting the complete `W_h...W_g` estimate. -/
theorem fordLemma51U_pow_le_momentMajorant
    {k h g r s M M₂ N : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hM : 0 < M) (hM₂ : 1 ≤ M₂) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    {t z : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hNz : (N : ℝ) ≤ z) (hz2N : z ≤ 2 * N) :
    ‖fordLemma51U k M B t z‖ ^ (2 * r * s) ≤
      fordLemma51MomentMajorant k h g r s M M₂ N B t := by
  have hr1 : 1 ≤ r := by omega
  have hs1 : 1 ≤ s := by omega
  have h53 := ford_equation_5_3 k M r s hr1 hs1 B t z
  have h53R :
      ‖fordLemma51U k M B t z‖ ^ (2 * r * s) ≤
        (B.card : ℝ) ^ (2 * r * s - 2 * s) *
          (M : ℝ) ^ (2 * r * s - 2 * r) *
          (fordVinogradovMomentNat r k M : ℝ) *
          (fordLemma51MomentT k M r s B t z : ℝ) := by
    exact_mod_cast h53
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hT := fordLemma51MomentT_le_windowMoment_mul_W
    (k := k) (h := h) (g := g) (M₂ := M₂) hs hM₂
    (Nat.zero_lt_of_lt hr) hM hBpos hBtop hNreal ht hNz hz2N
  unfold fordLemma51MomentMajorant
  exact h53R.trans (mul_le_mul_of_nonneg_left hT (by positivity))

/-- Taking the positive `2rs`-th root of the assembled moment estimate. -/
theorem fordLemma51U_le_momentMajorant_rpow
    {k h g r s M M₂ N : ℕ} (hr : 2 ≤ r) (hs : 2 ≤ s)
    (hM : 0 < M) (hM₂ : 1 ≤ M₂) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    {t z : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hNz : (N : ℝ) ≤ z) (hz2N : z ≤ 2 * N) :
    ‖fordLemma51U k M B t z‖ ≤
      (fordLemma51MomentMajorant k h g r s M M₂ N B t) ^
        (1 / ((2 * r * s : ℕ) : ℝ)) := by
  have hp : 0 < ((2 * r * s : ℕ) : ℝ) := by positivity
  have hpow := fordLemma51U_pow_le_momentMajorant
    (k := k) (h := h) (g := g)
    hr hs hM hM₂ hBpos hBtop hN ht hNz hz2N
  have hY : 0 ≤ fordLemma51MomentMajorant k h g r s M M₂ N B t :=
    (pow_nonneg (norm_nonneg _) _).trans hpow
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hY hp).2
  rw [Real.rpow_natCast]
  exact hpow

/-- Ford's Lemma 5.1 before the final exponent normalization.  This theorem
already consumes the actual shifted sum, selected `z`, Vinogradov moment,
incomplete moment, and every displayed `W_j`. -/
theorem ford_exponential_lemma_5_1_raw
    {k h g r s M M₂ N R : ℕ}
    (hr : 2 ≤ r) (hs : 2 ≤ s) (hM : 0 < M) (hM₂ : 1 ≤ M₂)
    {B : Finset ℕ} (hBne : B.Nonempty)
    (hBpos : ∀ b ∈ B, 1 ≤ b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    (hMN : M * M₂ ≤ N) (hR : R ≤ 2 * N)
    {u t : ℝ} (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 < t) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      (N : ℝ) / ((M : ℝ) * B.card) *
          (fordLemma51MomentMajorant k h g r s M M₂ N B t) ^
            (1 / ((2 * r * s : ℕ) : ℝ)) +
        t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
          (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) +
        2 * (M : ℝ) * (M₂ : ℝ) := by
  have hN : 0 < N := lt_of_lt_of_le (Nat.mul_pos hM hM₂) hMN
  obtain ⟨z, hz, h52⟩ := ford_equation_5_2
    hN hM hBne hBpos hBtop hMN hR hu huOne ht.le
  have hU := fordLemma51U_le_momentMajorant_rpow
    (k := k) (h := h) (g := g) hr hs hM hM₂
    (fun b hb => hBpos b hb) hBtop hN ht hz.1 hz.2
  have hfactor : 0 ≤ (N : ℝ) / ((M : ℝ) * B.card) := by positivity
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        (N : ℝ) / ((M : ℝ) * B.card) * ‖fordLemma51U k M B t z‖ +
          t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
            (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) +
          2 * (M : ℝ) * (M₂ : ℝ) := h52
    _ ≤ (N : ℝ) / ((M : ℝ) * B.card) *
            (fordLemma51MomentMajorant k h g r s M M₂ N B t) ^
              (1 / ((2 * r * s : ℕ) : ℝ)) +
          t * (((M * M₂ : ℕ) : ℝ) ^ (k + 1)) /
            (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) +
          2 * (M : ℝ) * (M₂ : ℝ) := by
      gcongr

#print axioms fordLemma51U_pow_le_momentMajorant
#print axioms fordLemma51U_le_momentMajorant_rpow
#print axioms ford_exponential_lemma_5_1_raw

end

end GafniTao
