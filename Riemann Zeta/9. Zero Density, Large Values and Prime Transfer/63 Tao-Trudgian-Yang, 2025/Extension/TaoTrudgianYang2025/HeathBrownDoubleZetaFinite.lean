import TaoTrudgianYang2025.HeathBrownEnergyFinite

/-!
# Heath--Brown's double-zeta estimate on the paper's actual support

The native coefficient-one theorem uses half-open support and a base interval.
The source uses closed support and an arbitrary interval. The finite bridge below
accounts for the single endpoint and reflects the actual ordinates; its constants
are chosen before the pattern. This does not scale or discard the fifth coordinate.
-/

open Complex Finset
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- Exact closed-support decomposition after reflecting an ordinate difference. -/
theorem LargeValuePattern.phaseSum_eq_endpoint_add_source
    (P : LargeValuePattern) (t u : ℝ) :
    (∑ n ∈ P.indices, dirichletPhase n (t - u)) =
      dirichletPhase P.scale (t - u) +
        sourceDirichletPoly P.scale (fun _ => 1)
          ((P.intervalRight - t) - (P.intervalRight - u)) := by
  rw [P.indices_eq_dyadicInterval, Finset.Icc_eq_cons_Ioc (by omega), Finset.sum_cons]
  congr 1
  unfold sourceDirichletPoly dyadicInterval
  apply Finset.sum_congr rfl
  intro n hn
  simp only [one_mul, dirichletPhase]
  congr 1
  push_cast
  ring

/-- One endpoint costs at most the explicit squared-norm error two. -/
theorem LargeValuePattern.phaseSum_sq_le_reflected_source
    (P : LargeValuePattern) (t u : ℝ) :
    ‖∑ n ∈ P.indices, dirichletPhase n (t - u)‖ ^ 2 ≤
      2 * ‖sourceDirichletPoly P.scale (fun _ => 1)
        ((P.intervalRight - t) - (P.intervalRight - u))‖ ^ 2 + 2 := by
  have hmem : P.scale ∈ P.indices := by
    rw [P.indices_eq_dyadicInterval]
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  rw [P.phaseSum_eq_endpoint_add_source]
  have h := norm_add_le (dirichletPhase P.scale (t - u))
    (sourceDirichletPoly P.scale (fun _ => 1)
      ((P.intervalRight - t) - (P.intervalRight - u)))
  rw [P.norm_dirichletPhase hmem] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖sourceDirichletPoly P.scale (fun _ => 1)
    ((P.intervalRight - t) - (P.intervalRight - u))‖ - 1)]

/-- The source double sum is controlled by the genuine native ratio moment.
The additive error is the closed left endpoint, not an assumed asymptotic loss. -/
theorem doubleZetaSum_le_native_secondMoment (P : LargeValuePattern) :
    doubleZetaSum P ≤
      2 * gmDiscreteRatioMoment 2 P.scale P.reflectedOrdinates +
        2 * (P.ordinates.card : ℝ) ^ 2 := by
  have himage :
      (∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖sourceDirichletPoly P.scale (fun _ => 1)
          ((P.intervalRight - t) - (P.intervalRight - u))‖ ^ 2) =
        gmDiscreteRatioMoment 2 P.scale P.reflectedOrdinates := by
    rw [gmDiscreteRatioMoment_eq_iterated,
      ← sourceCoefficientOne_differenceMoment_eq_gmR_ratioMoment]
    unfold LargeValuePattern.reflectedOrdinates
    rw [Finset.sum_image (fun x _ y _ hxy => by linarith)]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_image (fun x _ y _ hxy => by linarith)]
  calc
    doubleZetaSum P ≤ ∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        (2 * ‖sourceDirichletPoly P.scale (fun _ => 1)
          ((P.intervalRight - t) - (P.intervalRight - u))‖ ^ 2 + 2) :=
      Finset.sum_le_sum fun t _ =>
        Finset.sum_le_sum fun u _ => P.phaseSum_sq_le_reflected_source t u
    _ = 2 * (∑ t ∈ P.ordinates, ∑ u ∈ P.ordinates,
        ‖sourceDirichletPoly P.scale (fun _ => 1)
          ((P.intervalRight - t) - (P.intervalRight - u))‖ ^ 2) +
        2 * (P.ordinates.card : ℝ) ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    _ = _ := by rw [himage]

/-- Uniform finite `hb-double` estimate with the paper's closed support.
No relation between `N` and the enclosing height is required. -/
theorem heathBrown_largeValuePattern_doubleZeta :
    ∀ ε : ℝ, 0 < ε → ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
      ∀ (P : LargeValuePattern) (H : ℝ), H₀ ≤ H → P.T ≤ H →
        doubleZetaSum P ≤ C * H ^ ε *
          ((P.ordinates.card : ℝ) ^ 2 * P.N +
            (P.ordinates.card : ℝ) * P.N ^ 2 +
            (P.ordinates.card : ℝ) ^ (5 / 4 : ℝ) * H ^ (1 / 2 : ℝ) * P.N) := by
  intro ε hε
  obtain ⟨C, H₀, hC, hH₀, hsecond⟩ := gmDiscreteRatioSecondMoment_native ε hε
  refine ⟨2 * C + 2, H₀, by positivity, hH₀, ?_⟩
  intro P H hH hTH
  have hbase : InBaseInterval H P.reflectedOrdinates := by
    intro t ht
    exact ⟨(P.reflectedOrdinates_inBaseInterval t ht).1,
      (P.reflectedOrdinates_inBaseInterval t ht).2.trans hTH⟩
  have h₂ := hsecond P.scale H P.reflectedOrdinates P.scale_pos hH
    P.reflectedOrdinates_isSeparated hbase
  rw [P.reflectedOrdinates_card, ← P.N_eq_scale] at h₂
  let B : ℝ := (P.ordinates.card : ℝ) ^ 2 * P.N +
    (P.ordinates.card : ℝ) * P.N ^ 2 +
    (P.ordinates.card : ℝ) ^ (5 / 4 : ℝ) * H ^ (1 / 2 : ℝ) * P.N
  have hHone : 1 ≤ H := hH₀.trans hH
  have hHpow : 1 ≤ H ^ ε := Real.one_le_rpow hHone hε.le
  have hBN : (P.ordinates.card : ℝ) ^ 2 ≤ (P.ordinates.card : ℝ) ^ 2 * P.N := by
    nlinarith [sq_nonneg (P.ordinates.card : ℝ), P.one_lt_N]
  have hB : (P.ordinates.card : ℝ) ^ 2 ≤ B := by
    dsimp only [B]
    have := zero_lt_one.trans P.one_lt_N
    have := zero_lt_one.trans_le hHone
    linarith [show 0 ≤ (P.ordinates.card : ℝ) * P.N ^ 2 by positivity,
      show 0 ≤ (P.ordinates.card : ℝ) ^ (5 / 4 : ℝ) * H ^ (1 / 2 : ℝ) * P.N by positivity]
  have hBH : (P.ordinates.card : ℝ) ^ 2 ≤ H ^ ε * B :=
    hB.trans (le_mul_of_one_le_left (le_trans (sq_nonneg _) hB) hHpow)
  have hbound := (doubleZetaSum_le_native_secondMoment P).trans
    (add_le_add (mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
  change doubleZetaSum P ≤ (2 * C + 2) * H ^ ε * B
  change doubleZetaSum P ≤ 2 * (C * H ^ ε * B) + 2 * (P.ordinates.card : ℝ) ^ 2 at hbound
  nlinarith

end TaoTrudgianYang2025
