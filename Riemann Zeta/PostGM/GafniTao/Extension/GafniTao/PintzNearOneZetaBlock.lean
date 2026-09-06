import GafniTao.Pintz2023ThreeQuarterExponentialSum

/-!
# Exact Abel transfer to Pintz's near-one zeta block

The terminal-point estimate is first moved to the physical height
`t = N^fordLambda N t`, then consumed by monotone summation by parts.  The
`sigma` in the unweighted target cancels the literal `n^(-sigma)` weight.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The near-one prefix estimate at the actual physical ordinate. -/
theorem norm_pintz2023ExponentialBlock_le_nearOne_physical
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      sigma ≤ 1 → 3 / 4 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N → (N : ℝ) ^ 2 ≤ t →
      ‖pintz2023ExponentialBlock N R t‖ ≤
        C * (N : ℝ) ^
          pintzNearOneUnweightedTarget sigma epsilon (fordLambda N t) := by
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_threeQuarter_target hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt
  have hNOne : 1 < N := by omega
  have ht : 0 < t :=
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 2).trans_le hNt
  have htau : 2 ≤ fordLambda N t :=
    two_le_fordLambda_of_sq_le hNOne hNt
  have hraw := hbound sigma N R (fordLambda N t)
    hsigmaUpper hsigmaLower hN hNR hR htau
  rwa [rpow_fordLambda_eq hNOne ht] at hraw

/-- Monotone Abel summation with every prefix supplied by the native
near-one exponential-sum theorem. -/
theorem norm_fordShiftedWeightedBlock_zero_le_nearOne_physical
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      sigma ≤ 1 → 3 / 4 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon (fordLambda N t)) := by
  obtain ⟨C, hC, hprefix⟩ :=
    norm_pintz2023ExponentialBlock_le_nearOne_physical hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt
  have hsigma : 0 ≤ sigma := by linarith
  unfold fordShiftedWeightedBlock
  simp only [add_zero]
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => (n : ℝ) ^ (-sigma))
      (fun n => fordShiftedLogPhase n 0 t) N R
      (C * (N : ℝ) ^
        pintzNearOneUnweightedTarget sigma epsilon (fordLambda N t)) hNR
  · intro n _hn
    positivity
  · intro n _hnN _hnR
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (show 0 < n by omega)
    · exact_mod_cast Nat.le_succ n
    · linarith
  · intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
      positivity
    · rw [← fordShiftedExponentialSum_eq_sum_range]
      rw [← pintz2023ExponentialBlock_eq_fordShiftedExponentialSum
        t (by omega : 0 < N)]
      exact hprefix sigma t N (N + j) hsigmaUpper hsigmaLower
        hN (by omega) (by omega) hNt

/-- Pintz (2.19) in the exact dyadic-block form needed in the proof of his
strict `23/24` segment. -/
theorem norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      sigma ≤ 1 → 3 / 4 ≤ sigma →
      1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ ((1 / 2 : ℝ) *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨C, hC, hblock⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_nearOne_physical hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt
  have hsigma : 0 ≤ sigma := by linarith
  have hNOne : 1 < N := by omega
  have hNPos : (0 : ℝ) < N := by positivity
  have ht : 0 < t :=
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 2).trans_le hNt
  let tau : ℝ := fordLambda N t
  let q : ℝ := (1 / 2 : ℝ) *
    (1 - sigma) ^ (3 / 2 : ℝ) + epsilon
  have hweight : (((N + 1 : ℕ) : ℝ) ^ (-sigma)) ≤
      (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos hNPos
    · exact_mod_cast Nat.le_succ N
    · linarith
  have hmajorant : 0 ≤ C * (N : ℝ) ^
      pintzNearOneUnweightedTarget sigma epsilon tau := by positivity
  have hcombine :
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau) =
        C * (N : ℝ) ^ (tau * q) := by
    calc
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau) =
          C * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^ pintzNearOneUnweightedTarget sigma epsilon tau) := by
              ring
      _ = C * (N : ℝ) ^
          (-sigma + pintzNearOneUnweightedTarget sigma epsilon tau) := by
            rw [← Real.rpow_add hNPos]
      _ = C * (N : ℝ) ^ (tau * q) := by
        unfold pintzNearOneUnweightedTarget
        dsimp only [q]
        ring_nf
  have hscale : (N : ℝ) ^ (tau * q) = t ^ q := by
    calc
      (N : ℝ) ^ (tau * q) = ((N : ℝ) ^ tau) ^ q :=
        Real.rpow_mul hNPos.le tau q
      _ = t ^ q := by rw [rpow_fordLambda_eq hNOne ht]
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau) := by
      simpa only [tau] using
        hblock sigma t N R hsigmaUpper hsigmaLower hN hNR hR hNt
    _ ≤ (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            pintzNearOneUnweightedTarget sigma epsilon tau) :=
      mul_le_mul_of_nonneg_right hweight hmajorant
    _ = C * (N : ℝ) ^ (tau * q) := hcombine
    _ = C * t ^ q := by rw [hscale]
    _ = C * t ^ ((1 / 2 : ℝ) *
        (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := rfl

#print axioms norm_pintz2023ExponentialBlock_le_nearOne_physical
#print axioms norm_fordShiftedWeightedBlock_zero_le_nearOne_physical
#print axioms norm_fordShiftedWeightedBlock_zero_le_pintz_nearOne

end

end GafniTao
