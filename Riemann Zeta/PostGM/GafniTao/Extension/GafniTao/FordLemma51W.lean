import GafniTao.FordLemma51Spacing

/-!
# Ford Lemma 5.1: the published `W_j`

This file expands the absolute Taylor coefficient and uses `N ≤ z ≤ 2N` to
obtain the displayed factor in Lemma 5.1 from the raw spacing bound.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem abs_fordTaylorGamma_eq
    {t z : ℝ} (ht : 0 < t) (hz : 0 < z) (j : ℕ) :
    |fordTaylorGamma t z j| =
      t / (2 * Real.pi * (j + 1) * z ^ (j + 1)) := by
  unfold fordTaylorGamma
  rw [abs_div]
  have hden : 0 < 2 * Real.pi * ((j : ℝ) + 1) * z ^ (j + 1) := by
    positivity
  rw [abs_of_pos hden]
  have hsign : |(-1 : ℝ) ^ (j + 1)| = 1 := by simp
  rw [abs_mul, hsign, one_mul, abs_of_pos ht]

/-- The literal displayed `W_j` in Ford's Lemma 5.1, with source degree
`j+1`. -/
def fordLemma51W
    {k : ℕ} (s M₂ r M : ℕ) (N t : ℝ) (j : Fin k) : ℝ :=
  let d : ℕ := (j : ℕ) + 1
  min (2 * (s : ℝ) * (M₂ : ℝ) ^ d)
    (2 * (s : ℝ) * (M₂ : ℝ) ^ d /
        ((r : ℝ) * (M : ℝ) ^ d) +
      (s : ℝ) * t * (M₂ : ℝ) ^ d /
        (Real.pi * d * N ^ d) +
      4 * Real.pi * d * (2 * N) ^ d /
        ((r : ℝ) * t * (M : ℝ) ^ d) + 2)

theorem fordLemma51RawSpacingBound_eq_expanded
    {k s M₂ r M : ℕ} {t z : ℝ} (ht : 0 < t) (hz : 0 < z)
    (hr : 0 < r) (hM : 0 < M) (j : Fin k) :
    fordLemma51RawSpacingBound s M₂ r M t z j =
      2 * ((s : ℝ) * (M₂ : ℝ) ^ ((j : ℕ) + 1) - 1) /
          ((r : ℝ) * (M : ℝ) ^ ((j : ℕ) + 1)) +
      (((s : ℝ) * (M₂ : ℝ) ^ ((j : ℕ) + 1) - 1) * t) /
          (Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * z ^ ((j : ℕ) + 1)) +
      4 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * z ^ ((j : ℕ) + 1) /
          ((r : ℝ) * t * (M : ℝ) ^ ((j : ℕ) + 1)) + 2 := by
  unfold fordLemma51RawSpacingBound fordLemma51SourceRadius
    fordLemma51TentWidth
  rw [abs_fordTaylorGamma_eq ht hz]
  push_cast
  field_simp
  ring

theorem fordLemma51RawSpacingBound_le_displayed
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {N t z : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hNz : N ≤ z) (hz2N : z ≤ 2 * N)
    (j : Fin k) :
    fordLemma51RawSpacingBound s M₂ r M t z j ≤
      2 * (s : ℝ) * (M₂ : ℝ) ^ ((j : ℕ) + 1) /
          ((r : ℝ) * (M : ℝ) ^ ((j : ℕ) + 1)) +
      (s : ℝ) * t * (M₂ : ℝ) ^ ((j : ℕ) + 1) /
          (Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * N ^ ((j : ℕ) + 1)) +
      4 * Real.pi * (((j : ℕ) + 1 : ℕ) : ℝ) * (2 * N) ^ ((j : ℕ) + 1) /
          ((r : ℝ) * t * (M : ℝ) ^ ((j : ℕ) + 1)) + 2 := by
  let d : ℕ := (j : ℕ) + 1
  let A : ℝ := (s : ℝ) * (M₂ : ℝ) ^ d
  let R : ℝ := (r : ℝ) * (M : ℝ) ^ d
  have hz : 0 < z := hN.trans_le hNz
  have hA : 1 ≤ A := by
    dsimp [A, d]
    norm_cast
    have hp : 1 ≤ M₂ ^ ((j : ℕ) + 1) := one_le_pow₀ hM₂
    nlinarith
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hd : 0 < (d : ℝ) := by
    dsimp [d]
    positivity
  have hNpow : N ^ d ≤ z ^ d := by
    exact pow_le_pow_left₀ hN.le hNz d
  have hzpow : z ^ d ≤ (2 * N) ^ d := by
    exact pow_le_pow_left₀ hz.le hz2N d
  have hterm1 :
      2 * (A - 1) / R ≤ 2 * A / R := by
    apply div_le_div_of_nonneg_right
    · linarith
    · exact hR.le
  have hdenN : 0 < Real.pi * (d : ℝ) * N ^ d := by positivity
  have hdenZ : Real.pi * (d : ℝ) * N ^ d ≤
      Real.pi * (d : ℝ) * z ^ d := by
    gcongr
  have hnum : (A - 1) * t ≤ A * t := by
    gcongr
    linarith
  have hterm2 :
      (A - 1) * t / (Real.pi * (d : ℝ) * z ^ d) ≤
        A * t / (Real.pi * (d : ℝ) * N ^ d) := by
    exact div_le_div₀ (by positivity) hnum hdenN hdenZ
  have hdenR : 0 < R * t := mul_pos hR ht
  have hterm3 :
      4 * Real.pi * (d : ℝ) * z ^ d / (R * t) ≤
        4 * Real.pi * (d : ℝ) * (2 * N) ^ d / (R * t) := by
    apply div_le_div_of_nonneg_right
    · gcongr
    · exact hdenR.le
  rw [fordLemma51RawSpacingBound_eq_expanded ht hz hr hM]
  have hsum : 2 * (A - 1) / R +
      (A - 1) * t / (Real.pi * (d : ℝ) * z ^ d) +
      4 * Real.pi * (d : ℝ) * z ^ d / (R * t) + 2 ≤
    2 * A / R + A * t / (Real.pi * (d : ℝ) * N ^ d) +
      4 * Real.pi * (d : ℝ) * (2 * N) ^ d / (R * t) + 2 := by
    linarith
  simpa [A, R, d, mul_comm, mul_left_comm, mul_assoc] using hsum

theorem fordLemma51RawW_le_W
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {N t z : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hNz : N ≤ z) (hz2N : z ≤ 2 * N)
    (j : Fin k) :
    fordLemma51RawW s M₂ r M t z j ≤ fordLemma51W s M₂ r M N t j := by
  unfold fordLemma51RawW fordLemma51W
  apply min_le_min le_rfl
  exact fordLemma51RawSpacingBound_le_displayed
    hs hM₂ hr hM hN ht hNz hz2N j

theorem fordLemma51ResonantSet_card_le_W
    {k s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {N t z : ℝ}
    (hN : 0 < N) (ht : 0 < t) (hNz : N ≤ z) (hz2N : z ≤ 2 * N)
    (j : Fin k) :
    ((fordLemma51ResonantSet s M₂ r M t z j).card : ℝ) ≤
      fordLemma51W s M₂ r M N t j :=
  (fordLemma51ResonantSet_card_le_rawW hs hM₂ hr hM ht
    (hN.trans_le hNz) j).trans
      (fordLemma51RawW_le_W hs hM₂ hr hM hN ht hNz hz2N j)

/-- The complete moment estimate at the end of the proof of Ford's Lemma
5.1, with the displayed `W_h⋯W_g`. -/
theorem fordLemma51MomentT_le_windowMoment_mul_W
    {k h g s M₂ r M : ℕ} (hs : 2 ≤ s) (hM₂ : 1 ≤ M₂)
    (hr : 0 < r) (hM : 0 < M) {B : Finset ℕ}
    (hBpos : ∀ b ∈ B, 0 < b) (hBtop : ∀ b ∈ B, b ≤ M₂)
    {N t z : ℝ} (hN : 0 < N) (ht : 0 < t)
    (hNz : N ≤ z) (hz2N : z ≤ 2 * N) :
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
      (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
        (fordLemma51WindowMoment k h g s B : ℝ) *
          ∏ j : FordLemma51DegreeWindow k h g,
            fordLemma51W s M₂ r M N t j.1 := by
  have hraw := fordLemma51MomentT_le_windowMoment_mul_rawW
    (k := k) (h := h) (g := g) hs hM₂ hr hM hBpos hBtop ht
      (hN.trans_le hNz)
  have hprod :
      (∏ j : FordLemma51DegreeWindow k h g,
          fordLemma51RawW s M₂ r M t z j.1) ≤
        ∏ j : FordLemma51DegreeWindow k h g,
          fordLemma51W s M₂ r M N t j.1 := by
    apply Finset.prod_le_prod
    · intro j hj
      exact (Nat.cast_nonneg
        (fordLemma51ResonantSet s M₂ r M t z j.1).card).trans
          (fordLemma51ResonantSet_card_le_rawW
            hs hM₂ hr hM ht (hN.trans_le hNz) j.1)
    · intro j hj
      exact fordLemma51RawW_le_W hs hM₂ hr hM hN ht hNz hz2N j.1
  calc
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
        (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
          (fordLemma51WindowMoment k h g s B : ℝ) *
            ∏ j : FordLemma51DegreeWindow k h g,
              fordLemma51RawW s M₂ r M t z j.1 := hraw
    _ ≤ (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
          (fordLemma51WindowMoment k h g s B : ℝ) *
            ∏ j : FordLemma51DegreeWindow k h g,
              fordLemma51W s M₂ r M N t j.1 := by
      gcongr

#print axioms abs_fordTaylorGamma_eq
#print axioms fordLemma51RawSpacingBound_eq_expanded
#print axioms fordLemma51RawSpacingBound_le_displayed
#print axioms fordLemma51RawW_le_W
#print axioms fordLemma51ResonantSet_card_le_W
#print axioms fordLemma51MomentT_le_windowMoment_mul_W

end

end GafniTao
