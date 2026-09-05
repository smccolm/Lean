import GafniTao.HeathBrownEPHalfNative
import GafniTao.HeathBrownEPHalfZetaExponent
import GafniTao.PintzPartialZetaDyadic

/-!
# The short half of Heath--Brown's zeta estimate

For a dyadic block with `N ^ 2 <= t`, the physical ordinate can be written
exactly as `t = N ^ tau`, where `tau = log t / log N >= 2`.  This file feeds
that identity into the coefficient-one-half exponential-sum theorem and then
performs the literal monotone Abel transfer to `n ^ (-sigma-it)`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The physical height is exactly the logarithmic `N`-power used by the
Heath--Brown block theorem. -/
theorem rpow_fordLambda_eq
    {N : ℕ} {t : ℝ} (hN : 1 < N) (ht : 0 < t) :
    (N : ℝ) ^ fordLambda N t = t := by
  have hNPos : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hNOne : (N : ℝ) ≠ 1 := by exact_mod_cast hN.ne'
  simpa only [fordLambda, Real.logb] using
    (Real.rpow_logb hNPos hNOne ht)

/-- A block lying below the square-root conductor has logarithmic scale at
least two. -/
theorem two_le_fordLambda_of_sq_le
    {N : ℕ} {t : ℝ} (hN : 1 < N) (hNt : (N : ℝ) ^ 2 ≤ t) :
    2 ≤ fordLambda N t := by
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  have ht : 0 < t := (by positivity : (0 : ℝ) < (N : ℝ) ^ 2).trans_le hNt
  apply (Real.rpow_le_rpow_left_iff hNReal).mp
  rw [Real.rpow_two, rpow_fordLambda_eq hN ht]
  simpa only [sq] using hNt

/-- Uniform unweighted prefix estimate at the actual physical height. -/
theorem norm_pintz2023ExponentialBlock_le_half_physical
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (t : ℝ),
      1024 ≤ N → N < R → R ≤ 2 * N → (N : ℝ) ^ 2 ≤ t →
      ‖pintz2023ExponentialBlock N R t‖ ≤
        C * (N : ℝ) ^ heathBrownHalfTarget epsilon (fordLambda N t) := by
  obtain ⟨C, hC, hbound⟩ :=
    heathBrownHalfExponentialSumBound_native epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro N R t hN hNR hR hNt
  have hNOne : 1 < N := by omega
  have ht : 0 < t :=
    (by positivity : (0 : ℝ) < (N : ℝ) ^ 2).trans_le hNt
  have htau : 2 ≤ fordLambda N t :=
    two_le_fordLambda_of_sq_le hNOne hNt
  have hraw := hbound N R (fordLambda N t) hN hNR hR htau
  rwa [rpow_fordLambda_eq hNOne ht] at hraw

/-- The exact monotone Abel transfer on a dyadic block below `sqrt t`.
Every prefix is supplied by the physical Heath--Brown theorem above. -/
theorem norm_fordShiftedWeightedBlock_zero_le_half_physical
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → 1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        ((N + 1 : ℕ) : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^
            heathBrownHalfTarget epsilon (fordLambda N t)) := by
  obtain ⟨C, hC, hprefix⟩ :=
    norm_pintz2023ExponentialBlock_le_half_physical hepsilon
  refine ⟨C, hC, ?_⟩
  intro sigma t N R hsigma hN hNR hR hNt
  unfold fordShiftedWeightedBlock
  simp only [add_zero]
  apply ford_norm_weighted_Ioc_le_of_antitone
      (fun n => (n : ℝ) ^ (-sigma))
      (fun n => fordShiftedLogPhase n 0 t) N R
      (C * (N : ℝ) ^
        heathBrownHalfTarget epsilon (fordLambda N t)) hNR
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

/-- A short physical block, after its exact Abel weight is included, has the
zeta exponent furnished by the coefficient-one-half optimization.  This is
the form used in Pintz (4.9) and (4.20). -/
theorem norm_fordShiftedWeightedBlock_zero_le_half_zeta
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (sigma t : ℝ) (N R : ℕ),
      0 ≤ sigma → sigma ≤ 1 → 1024 ≤ N → N < R → R ≤ 2 * N →
      (N : ℝ) ^ 2 ≤ t →
      ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
  obtain ⟨C, hC, hblock⟩ :=
    norm_fordShiftedWeightedBlock_zero_le_half_physical hepsilon
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
      0 ≤ C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau := by
    positivity
  have hcombine :
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau) =
        C * (N : ℝ) ^
          (u - 1 / (2 * tau ^ 2) + epsilon) := by
    calc
      (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau) =
          C * ((N : ℝ) ^ (-sigma) *
            (N : ℝ) ^ heathBrownHalfTarget epsilon tau) := by ring
      _ = C * (N : ℝ) ^
          (-sigma + heathBrownHalfTarget epsilon tau) := by
            rw [← Real.rpow_add hNReal]
      _ = C * (N : ℝ) ^
          (u - 1 / (2 * tau ^ 2) + epsilon) := by
            unfold heathBrownHalfTarget u
            ring
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNRealOne
  have hNsqOne : (1 : ℝ) < (N : ℝ) ^ 2 := by nlinarith
  have hlogt : 0 < Real.log t := Real.log_pos (hNsqOne.trans_le hNt)
  have htauLog : tau * Real.log (N : ℝ) = Real.log t := by
    dsimp only [tau, fordLambda]
    field_simp [hlogN.ne']
  have hscaleExponent :
      Real.log (N : ℝ) *
          (u - 1 / (2 * tau ^ 2) + epsilon) =
        Real.log t *
          (u / tau - 1 / (2 * tau ^ 3) + epsilon / tau) := by
    rw [← htauLog]
    field_simp [htauPos.ne']
  have hscalePower :
      (N : ℝ) ^ (u - 1 / (2 * tau ^ 2) + epsilon) =
        t ^ (u / tau - 1 / (2 * tau ^ 3) + epsilon / tau) := by
    rw [Real.rpow_def_of_pos hNReal, Real.rpow_def_of_pos ht,
      hscaleExponent]
  have hepsilonDiv : epsilon / tau ≤ epsilon := by
    rw [div_le_iff₀ htauPos]
    nlinarith
  have hoptimized := heathBrownHalf_zeta_exponent_le hu htauPos
  have hexponent :
      u / tau - 1 / (2 * tau ^ 3) + epsilon / tau ≤
        heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) + epsilon := by
    linarith
  have hpow :
      t ^ (u / tau - 1 / (2 * tau ^ 3) + epsilon / tau) ≤
        t ^ (heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) + epsilon) :=
    Real.rpow_le_rpow_of_exponent_le htOne hexponent
  calc
    ‖fordShiftedWeightedBlock sigma N R 0 t‖ ≤
        (((N + 1 : ℕ) : ℝ) ^ (-sigma)) *
          (C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau) := by
      simpa only [tau] using hblock sigma t N R hsigma hN hNR hR hNt
    _ ≤ (N : ℝ) ^ (-sigma) *
          (C * (N : ℝ) ^ heathBrownHalfTarget epsilon tau) :=
      mul_le_mul_of_nonneg_right hweight hpowerNonneg
    _ = C * t ^
          (u / tau - 1 / (2 * tau ^ 3) + epsilon / tau) := by
      rw [hcombine, hscalePower]
    _ ≤ C * t ^
          (heathBrownHalfZetaKappa * u ^ (3 / 2 : ℝ) + epsilon) :=
      mul_le_mul_of_nonneg_left hpow hC.le
    _ = C * t ^ (heathBrownHalfZetaKappa *
          (1 - sigma) ^ (3 / 2 : ℝ) + epsilon) := by
      rfl

#print axioms rpow_fordLambda_eq
#print axioms two_le_fordLambda_of_sq_le
#print axioms norm_pintz2023ExponentialBlock_le_half_physical
#print axioms norm_fordShiftedWeightedBlock_zero_le_half_physical
#print axioms norm_fordShiftedWeightedBlock_zero_le_half_zeta

end

end GafniTao
