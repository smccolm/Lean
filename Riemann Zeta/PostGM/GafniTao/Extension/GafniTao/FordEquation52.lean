import GafniTao.FordLemma51Average

/-!
# Ford's equation (5.2)

This module assembles the finite Weyl shift, the selected physical
`z in [N,2N]`, and the exact degree-`k` Taylor error.  Unlike the earlier
pointwise Taylor lemma, the public theorem starts from Ford's actual shifted
exponential sum.
-/

open Complex Finset

namespace GafniTao

noncomputable section

/-- Ford's equation (5.2), retaining the sharper source denominator `k+1`.
The polynomial sum is the actual `fordLemma51U` consumed by (5.3). -/
theorem ford_equation_5_2
    {k M₁ M₂ N R : ℕ} {B : Finset ℕ} {u t : ℝ}
    (hN : 0 < N) (hM₁ : 0 < M₁) (hBne : B.Nonempty)
    (hBpos : ∀ b ∈ B, 1 ≤ b) (hB : ∀ b ∈ B, b ≤ M₂)
    (hM : M₁ * M₂ ≤ N) (hR : R ≤ 2 * N)
    (hu : 0 < u) (huOne : u ≤ 1) (ht : 0 ≤ t) :
    ∃ z : ℝ, z ∈ Set.Icc (N : ℝ) (2 * N : ℝ) ∧
      ‖fordShiftedExponentialSum N R u t‖ ≤
        (N : ℝ) / ((M₁ : ℝ) * B.card) *
            ‖fordLemma51U k M₁ B t z‖ +
          t * (((M₁ * M₂ : ℕ) : ℝ) ^ (k + 1)) /
            (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) +
          2 * (M₁ : ℝ) * (M₂ : ℝ) := by
  obtain ⟨z, hz, hzAvg⟩ := exists_fordLemma51LogU_controls_average
    (M₁ := M₁) (B := B) (u := u) (t := t) hN hR hu huOne
  refine ⟨z, hz, ?_⟩
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hzpos : 0 < z := hNreal.trans_le hz.1
  have hc : 0 < (M₁ : ℝ) * (B.card : ℝ) := by positivity
  have havg := norm_fordShiftedExponentialSum_le_average
    (M₁ := M₁) (M₂ := M₂) (N := N) (R := R) (B := B)
    (u := u) (t := t) hM₁ hBne hBpos hB
  have hAvgDiv :
      ‖fordLemma51CommonShiftAverage M₁ B N R u t‖ /
          ((M₁ : ℝ) * B.card) ≤
        (N : ℝ) / ((M₁ : ℝ) * B.card) *
          ‖fordLemma51LogU M₁ B t z‖ := by
    calc
      _ ≤ ((N : ℝ) * ‖fordLemma51LogU M₁ B t z‖) /
          ((M₁ : ℝ) * B.card) :=
        div_le_div_of_nonneg_right hzAvg hc.le
      _ = _ := by ring
  have hTaylor := ford_equation_5_2_normalized_taylor_error
    (k := k) hN hM₁ hBne hz.1 hM hB ht
  change
      ((N : ℝ) / ((M₁ : ℝ) * B.card)) *
        ‖fordLemma51LogU M₁ B t z -
          (∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
            fordTaylorOscillation k t (((a * b : ℕ) : ℝ) / z))‖ ≤
      t * (((M₁ * M₂ : ℕ) : ℝ) ^ (k + 1)) /
        (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) at hTaylor
  rw [fordTaylorDoubleSum_eq_fordLemma51U hzpos.ne'] at hTaylor
  have hfactor : 0 ≤ (N : ℝ) / ((M₁ : ℝ) * B.card) := by positivity
  have hLog :
      (N : ℝ) / ((M₁ : ℝ) * B.card) *
          ‖fordLemma51LogU M₁ B t z‖ ≤
        (N : ℝ) / ((M₁ : ℝ) * B.card) *
            ‖fordLemma51U k M₁ B t z‖ +
          t * (((M₁ * M₂ : ℕ) : ℝ) ^ (k + 1)) /
            (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) := by
    have htri :
        ‖fordLemma51LogU M₁ B t z‖ ≤
          ‖fordLemma51LogU M₁ B t z - fordLemma51U k M₁ B t z‖ +
            ‖fordLemma51U k M₁ B t z‖ := by
      calc
        _ = ‖(fordLemma51LogU M₁ B t z - fordLemma51U k M₁ B t z) +
            fordLemma51U k M₁ B t z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    calc
      _ ≤ (N : ℝ) / ((M₁ : ℝ) * B.card) *
          (‖fordLemma51LogU M₁ B t z - fordLemma51U k M₁ B t z‖ +
            ‖fordLemma51U k M₁ B t z‖) :=
        mul_le_mul_of_nonneg_left htri hfactor
      _ = (N : ℝ) / ((M₁ : ℝ) * B.card) *
            ‖fordLemma51LogU M₁ B t z - fordLemma51U k M₁ B t z‖ +
          (N : ℝ) / ((M₁ : ℝ) * B.card) *
            ‖fordLemma51U k M₁ B t z‖ := by ring
      _ ≤ _ := by linarith
  linarith

#print axioms ford_equation_5_2

end

end GafniTao
