import GafniTao.HeathBrownHybridZetaBlock
import GafniTao.HeathBrownZetaExponent

/-!
# Heath--Brown Theorem 4 and its weighted zeta-block consumer

This file fixes the exact public statement of Heath--Brown (2017), Theorem 4,
equation (1.9), for the logarithmic phase used by Pintz.  The theorem is a
genuine upstream target, not an assumption hidden in the final density
theorem.  The second theorem proves the complete Abel and scale transfer from
that source statement to one weighted dyadic block.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The exponent in Heath--Brown (2017), equation (1.9). -/
def heathBrownEP1Target (epsilon tau : ℝ) : ℝ :=
  1 - 49 / (80 * tau ^ 2) + epsilon

/-- Source-faithful logarithmic-phase specialization of Heath--Brown
Theorem 4.  The lower cutoff `1024` is harmless and makes the finite
uniformity needed by the dyadic consumer explicit. -/
def HeathBrownEP1ExponentialSumBound : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N → 2 ≤ tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon tau

/-- The sharper constant in Heath--Brown (1.10) is strictly below the
coefficient `1/2` quoted by Pintz in (2.19). -/
theorem heathBrownZetaKappa_lt_half :
    heathBrownZetaKappa < 1 / 2 := by
  have hs : Real.sqrt 15 < 63 / 16 := by
    have hs_nonneg : 0 ≤ Real.sqrt 15 := Real.sqrt_nonneg _
    have hs_sq : Real.sqrt 15 ^ 2 = 15 := Real.sq_sqrt (by norm_num)
    nlinarith
  unfold heathBrownZetaKappa
  nlinarith

/-- Exact physical-height form of Theorem 4. -/
theorem norm_pintz2023ExponentialBlock_le_EP1_physical
    (hEP1 : HeathBrownEP1ExponentialSumBound)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (t : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N → (N : ℝ) ^ 2 ≤ t →
      ‖pintz2023ExponentialBlock N R t‖ ≤
        C * (N : ℝ) ^ heathBrownEP1Target epsilon (fordLambda N t) := by
  obtain ⟨C, hC, hbound⟩ := hEP1 epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro N R t hN hNR hR hNt
  have hNOne : 1 < N := by omega
  have ht : 0 < t :=
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 2).trans_le hNt
  have htau : 2 ≤ fordLambda N t :=
    two_le_fordLambda_of_sq_le hNOne hNt
  have hraw := hbound N R (fordLambda N t) hN hNR hR htau
  rwa [rpow_fordLambda_eq hNOne ht] at hraw

/-- The complete monotone Abel transfer of Theorem 4 to one weighted
Dirichlet block. -/
theorem norm_fordShiftedWeightedBlock_zero_le_EP1_physical
    (hEP1 : HeathBrownEP1ExponentialSumBound)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → 1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            heathBrownEP1Target epsilon (fordLambda N t)) := by
  obtain ⟨C, hC, hprefix⟩ :=
    norm_pintz2023ExponentialBlock_le_EP1_physical hEP1 hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigma hN hNR hR hNt
  unfold fordShiftedWeightedBlock
  simp only [add_zero]
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => (n : ℝ) ^ (-sigma))
      (fun n => fordShiftedLogPhase n 0 t) N R
      (C * (N : ℝ) ^
        heathBrownEP1Target epsilon (fordLambda N t)) hNR
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
      exact hprefix N (N + j) t hN (by omega) (by omega) hNt

/-- Heath--Brown Theorem 4, after exact Abel weighting and the source
one-variable optimization.  This is the dyadic block form of (1.10), still
retaining the sharper coefficient `8 * sqrt 15 / 63`. -/
theorem norm_fordShiftedWeightedBlock_zero_le_EP1_zeta
    (hEP1 : HeathBrownEP1ExponentialSumBound)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → sigma ≤ 1 → 1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ (heathBrownZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  have hepsHalf : 0 < epsilon / 2 := by positivity
  obtain ⟨C, hC, hblock⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_EP1_physical hEP1 hepsHalf
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigma hsigmaUpper hN hNR hR hNt
  have hNOne : 1 < N := by omega
  have hNReal : (0 : ℝ) < N := by positivity
  have hNRealOne : (1 : ℝ) < N := by exact_mod_cast hNOne
  have ht : 0 < t :=
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 2).trans_le hNt
  have htOne : 1 ≤ t := by
    have : (1 : ℝ) < (N : ℝ) ^ 2 := by nlinarith
    linarith
  let tau : ℝ := fordLambda N t
  let u : ℝ := 1 - sigma
  have htau : 2 ≤ tau := by
    simpa only [tau] using two_le_fordLambda_of_sq_le hNOne hNt
  have htauPos : 0 < tau := by linarith
  have hu : 0 ≤ u := by dsimp only [u]; linarith
  have hweight : (((N + 1 : ℕ) : ℝ) ^ (-sigma)) ≤
      (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos hNReal
    · exact_mod_cast Nat.le_succ N
    · linarith
  have hpowerNonneg :
      0 ≤ C * (N : ℝ) ^ heathBrownEP1Target (epsilon / 2) tau := by
    positivity
  have hcombine :
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^ heathBrownEP1Target (epsilon / 2) tau) =
        C * (N : ℝ) ^
          (u - 49 / (80 * tau ^ 2) + epsilon / 2) := by
    calc
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^ heathBrownEP1Target (epsilon / 2) tau) =
          C * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^ heathBrownEP1Target (epsilon / 2) tau) := by ring_nf
      _ = C * (N : ℝ) ^
          (-sigma + heathBrownEP1Target (epsilon / 2) tau) := by
            rw [← Real.rpow_add hNReal]
      _ = C * (N : ℝ) ^
          (u - 49 / (80 * tau ^ 2) + epsilon / 2) := by
            unfold heathBrownEP1Target u
            ring_nf
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNRealOne
  have htauLog : tau * Real.log (N : ℝ) = Real.log t := by
    dsimp only [tau, fordLambda]
    field_simp [hlogN.ne']
  have hscaleExponent :
      Real.log (N : ℝ) *
          (u - 49 / (80 * tau ^ 2) + epsilon / 2) =
        Real.log t *
          (u / tau - 49 / (80 * tau ^ 3) + epsilon / (2 * tau)) := by
    rw [← htauLog]
    field_simp [htauPos.ne']
  have hscalePower :
      (N : ℝ) ^ (u - 49 / (80 * tau ^ 2) + epsilon / 2) =
        t ^ (u / tau - 49 / (80 * tau ^ 3) +
          epsilon / (2 * tau)) := by
    rw [Real.rpow_def_of_pos hNReal, Real.rpow_def_of_pos ht,
      hscaleExponent]
  have hepsilonDiv : epsilon / (2 * tau) ≤ epsilon := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * tau)]
    nlinarith
  have hoptimized := heathBrown_zeta_exponent_le hu htauPos
  have hexponent :
      u / tau - 49 / (80 * tau ^ 3) + epsilon / (2 * tau) ≤
        heathBrownZetaKappa * u ^ (3 / 2 : ℝ) + epsilon := by
    linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le htOne hexponent
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (C * (N : ℝ) ^
            heathBrownEP1Target (epsilon / 2) tau) := by
      simpa only [tau] using hblock sigma t N R hsigma hN hNR hR hNt
    _ ≤ (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            heathBrownEP1Target (epsilon / 2) tau) :=
      mul_le_mul_of_nonneg_right hweight hpowerNonneg
    _ = C * t ^ (u / tau - 49 / (80 * tau ^ 3) +
          epsilon / (2 * tau)) := by rw [hcombine, hscalePower]
    _ ≤ C * t ^ (heathBrownZetaKappa * u ^ (3 / 2 : ℝ) + epsilon) :=
      mul_le_mul_of_nonneg_left hpow hC.le
    _ = C * t ^ (heathBrownZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by rfl

#print axioms heathBrownZetaKappa_lt_half
#print axioms norm_pintz2023ExponentialBlock_le_EP1_physical
#print axioms norm_fordShiftedWeightedBlock_zero_le_EP1_physical
#print axioms norm_fordShiftedWeightedBlock_zero_le_EP1_zeta

end

end GafniTao
